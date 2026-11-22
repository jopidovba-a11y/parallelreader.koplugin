local Device = require("device")
local Blitbuffer = require("ffi/blitbuffer")
local Geom = require("ui/geometry")
local Widget = require("ui/widget/widget")
local InputContainer = require("ui/widget/container/inputcontainer")
local WidgetContainer = require("ui/widget/container/widgetcontainer")
local InfoMessage = require("ui/widget/infomessage")
local UIManager = require("ui/uimanager")
local Font = require("ui/font")
local RenderText = require("ui/rendertext")
local PathChooser = require("ui/widget/pathchooser")
local DocumentRegistry = require("document/documentregistry")
local DocSettings = require("docsettings")
local DataStorage = require("datastorage")
local Dispatcher = require("dispatcher")
local util = require("util")
local CanvasContext = require("document/canvascontext")
local lfs = require("libs/libkoreader-lfs")
local ffiUtil = require("ffi/util")
local _ = require("gettext")

local Screen = Device.screen

local ParallelReader = WidgetContainer:extend{
    name = "parallelreader",
    is_doc_only = false,
}

local MIN_SPLIT = 0.30
local MAX_SPLIT = 0.70
local SPLIT_STEP = 0.03
local DIVIDER_SIZE = 3
local PANEL_INSET = 4
local PANEL_MARGIN = PANEL_INSET + 2
local MENU_SWIPE_ZONE = 0.14 -- top fraction of the screen: swipe down opens the menu
local PAGE_ZOOM_STEP = 1.25
local MIN_PAGE_ZOOM = 1.0
local MAX_PAGE_ZOOM = 4.0
local SETTINGS_KEY = "parallelreader"

-- Only one Parallel Reader window can exist at a time.
local active_window = nil

-- Created lazily so reopening the bottom menu does not allocate new classes.
local PanelConfigDialogClass

------------------------------------------------------------------------
-- Logging / error helpers
------------------------------------------------------------------------

local function tracebackError(err)
    local message = tostring(err)
    if debug and debug.traceback then return debug.traceback(message, 2) end
    return message
end

local function appendDebugLog() end

-- Runs callback protected; remembers the last error for the diagnostics item.
local function runStage(plugin, stage, callback)
    local ok, result = xpcall(callback, tracebackError)
    if ok then return true, result end
    if plugin then
        plugin.last_error = tostring(result)
        plugin.last_error_stage = stage
    end
    appendDebugLog(plugin, stage, "ERROR: " .. tostring(result))
    return false, result
end

local function showInfo(message, timeout)
    pcall(function()
        UIManager:show(InfoMessage:new{ text = tostring(message), timeout = timeout or 8 })
    end)
end

-- Shows a message, forces it onto the screen, runs a blocking job, removes it.
local function withBusy(text, job)
    local info = InfoMessage:new{ text = text, dismissable = false }
    pcall(UIManager.show, UIManager, info)
    pcall(UIManager.forceRePaint, UIManager)
    local ok, a, b = xpcall(job, tracebackError)
    pcall(UIManager.close, UIManager, info)
    if not ok then error(a, 0) end
    return a, b
end

-- Calls fn(...) protected and returns its first result (nil on error).
local function try(fn, ...)
    if type(fn) ~= "function" then return nil end
    local ok, value = pcall(fn, ...)
    if ok then return value end
    return nil
end

local function clamp(value, low, high, default)
    value = tonumber(value) or default
    return math.max(low, math.min(high, value))
end

local function drawText(bb, x, y, text, size)
    local face = Font:getFace("cfont", size or 18)
    RenderText:renderUtf8Text(bb, x, y, face, tostring(text), true)
end

local function getBaseName(path)
    if not path then return "" end
    return path:match("([^/]+)$") or path
end

------------------------------------------------------------------------
-- Persistent plugin preferences (stored in settings.reader.lua)
------------------------------------------------------------------------

local function getPrefs()
    local prefs = G_reader_settings:readSetting(SETTINGS_KEY)
    if type(prefs) ~= "table" then prefs = {} end
    return prefs
end

local function setPref(key, value)
    local prefs = getPrefs()
    prefs[key] = value
    G_reader_settings:saveSetting(SETTINGS_KEY, prefs)
end

------------------------------------------------------------------------
-- Document helpers
------------------------------------------------------------------------

local function getPageCount(doc)
    if doc and type(doc.getPageCount) == "function" then
        local ok, count = pcall(doc.getPageCount, doc)
        if ok and type(count) == "number" then return count end
    end
    if doc and doc.info and type(doc.info.number_of_pages) == "number" then
        return doc.info.number_of_pages
    end
    return 0
end

local function getReflowablePosition(doc)
    local position = try(doc and doc.getCurrentPos, doc)
    return type(position) == "number" and position or 0
end

local function getDocumentXPointer(doc)
    if doc and type(doc.getXPointer) == "function" then
        local ok, xpointer = pcall(doc.getXPointer, doc)
        if ok then return xpointer end
    end
    return nil
end

local function isScrollMode(doc)
    return doc and doc._view_mode ~= nil and doc._view_mode == doc.SCROLL_VIEW_MODE
end

-- The native view keeps its own "current page". Re-sync it before any query
-- that depends on it (word lookup, highlight boxes) so it can never be stale.
local function syncDocView(record)
    local doc = record and record.doc
    if not doc or record.kind ~= "reflowable" then return end
    if isScrollMode(doc) then
        if type(doc.gotoPos) == "function" then pcall(doc.gotoPos, doc, record.position or 0) end
    elseif type(doc.gotoPage) == "function" then
        pcall(doc.gotoPage, doc, record.page or 1)
    end
end

local function closeDocumentRecord(record)
    if not record then return end
    if record.doc then
        local doc = record.doc
        record.doc = nil
        record.selection = nil
        record.hl_cache = nil
        pcall(doc.close, doc)
    end
    -- Private copy used when the same book is open in both panels.
    if record.temp_copy then
        pcall(os.remove, record.temp_copy)
        record.temp_copy = nil
    end
end

local function getTempDir()
    return DataStorage:getDataDir() .. "/parallelreader_tmp"
end

-- Removes leftovers of a previous session (for example after a crash).
local function clearTempDir()
    local dir = getTempDir()
    if lfs.attributes(dir, "mode") ~= "directory" then return end
    for name in lfs.dir(dir) do
        if name ~= "." and name ~= ".." then pcall(os.remove, dir .. "/" .. name) end
    end
end

-- DocumentRegistry shares one document object per path, so a second fully
-- independent crengine view of the same book is opened from a private copy.
local function makeTempBookCopy(path)
    local dir = getTempDir()
    if lfs.attributes(dir, "mode") ~= "directory" then lfs.mkdir(dir) end
    local extension = path:match("(%.[^./]+)$") or ""
    local key = try(util.partialMD5, path)
    if type(key) ~= "string" or key == "" then
        key = tostring(lfs.attributes(path, "size") or 0)
    end
    local destination = dir .. "/pr_" .. key .. extension

    local input, open_error = io.open(path, "rb")
    if not input then error("Could not read the book to duplicate it: " .. tostring(open_error)) end
    local output, write_error = io.open(destination, "wb")
    if not output then
        input:close()
        error("Could not create the temporary copy: " .. tostring(write_error))
    end
    local copy_ok, copy_error = pcall(function()
        while true do
            local chunk = input:read(1024 * 1024)
            if not chunk then break end
            assert(output:write(chunk))
        end
    end)
    input:close()
    output:close()
    if not copy_ok or lfs.attributes(destination, "size") ~= lfs.attributes(path, "size") then
        pcall(os.remove, destination)
        error("Could not duplicate the book for the second panel: "
            .. tostring(copy_error or "size mismatch"))
    end
    return destination
end

local function shallowProviderForFile(provider, path)
    local extension = (path:match("%.([^./]+)$") or ""):lower()
    -- ReaderUI normally adds these per-file flags before opening crengine.
    -- Clone the provider instead of mutating KOReader's shared provider table.
    return setmetatable({
        is_fb2 = extension:sub(1, 2) == "fb",
        is_txt = extension == "txt",
    }, { __index = provider })
end

local function getReflowablePageCount(doc)
    if not doc then return 0 end
    local ok, count = pcall(doc.getPageCount, doc)
    if ok and type(count) == "number" then return count end
    return 0
end

local function countOpenReflowableDocuments(session)
    local count = 0
    for index = 1, 2 do
        local record = session.records[index]
        if record and record.kind == "reflowable" and record.doc then count = count + 1 end
    end
    return count
end

local function copyConfigValue(value)
    if type(value) ~= "table" then return value end
    local copy = {}
    for key, item in pairs(value) do copy[key] = copyConfigValue(item) end
    return copy
end

------------------------------------------------------------------------
-- Panel geometry
------------------------------------------------------------------------

-- mode: 0 = automatic (side by side in landscape), 1 = side by side, 2 = stacked
local function getPanelRects(w, h, ratio, mode)
    local divider = DIVIDER_SIZE
    local side_by_side
    if mode == 1 then side_by_side = true
    elseif mode == 2 then side_by_side = false
    else side_by_side = w > h end
    local first, second
    if side_by_side then
        local first_w = math.floor((w - divider) * ratio)
        first = Geom:new{ x = 0, y = 0, w = first_w, h = h }
        second = Geom:new{ x = first_w + divider, y = 0, w = w - first_w - divider, h = h }
    else
        local first_h = math.floor((h - divider) * ratio)
        first = Geom:new{ x = 0, y = 0, w = w, h = first_h }
        second = Geom:new{ x = 0, y = first_h + divider, w = w, h = h - first_h - divider }
    end
    return first, second, side_by_side
end

local function getFooterHeight(session)
    if not session.show_footer then return 0 end
    return Screen:scaleBySize(20)
end

local function sessionRects(session, ratio)
    return getPanelRects(session.screen_w or Screen:getWidth(),
        session.screen_h or Screen:getHeight(),
        ratio or session.split_ratio or 0.50,
        session.split_mode or 0)
end

-- Returns: panel rect, content rect (where the document is drawn), footer height.
local function getPanelLayout(session, index)
    local first, second = sessionRects(session)
    local panel = index == 1 and first or second
    local footer_h = getFooterHeight(session)
    local content = Geom:new{
        x = panel.x + PANEL_MARGIN,
        y = panel.y + PANEL_MARGIN,
        w = math.max(64, panel.w - PANEL_MARGIN * 2),
        h = math.max(64, panel.h - PANEL_MARGIN * 2 - footer_h),
    }
    return panel, content, footer_h
end

local function getPanelContentSize(session, index)
    local _panel, content = getPanelLayout(session, index)
    return content.w, content.h
end

-- Converts a screen position into the panel document's local coordinates.
local function getLocalDocumentPosition(session, index, screen_pos)
    if not screen_pos or type(screen_pos.x) ~= "number" or type(screen_pos.y) ~= "number" then
        return nil
    end
    local _panel, content = getPanelLayout(session, index)
    -- Clamp rather than reject: hold-pan selection continues to the panel edge.
    local x = math.max(0, math.min(content.w - 1, screen_pos.x - content.x))
    local y = math.max(0, math.min(content.h - 1, screen_pos.y - content.y))
    return { x = x, y = y }
end

local function getSelectionScreenBoxes(session, index, selection)
    local boxes = selection and selection.sboxes
    if type(boxes) ~= "table" or #boxes == 0 then return nil end
    local _panel, content = getPanelLayout(session, index)
    local result = {}
    for i = 1, #boxes do
        local box = boxes[i]
        if box and type(box.x) == "number" and type(box.y) == "number"
                and type(box.w) == "number" and type(box.h) == "number" then
            result[#result + 1] = Geom:new{
                x = content.x + box.x, y = content.y + box.y, w = box.w, h = box.h,
            }
        end
    end
    return #result > 0 and result or nil
end

-- Screen band that contains the divider for a given split ratio.
local function getDividerBand(session, ratio)
    local first, _second, side_by_side = sessionRects(session, ratio)
    if side_by_side then
        return Geom:new{ x = math.max(0, first.w - 6), y = 0, w = DIVIDER_SIZE + 12,
            h = session.screen_h or Screen:getHeight() }
    end
    return Geom:new{ x = 0, y = math.max(0, first.h - 6),
        w = session.screen_w or Screen:getWidth(), h = DIVIDER_SIZE + 12 }
end

local function unionRegion(a, b)
    local x0, y0 = math.min(a.x, b.x), math.min(a.y, b.y)
    local x1, y1 = math.max(a.x + a.w, b.x + b.w), math.max(a.y + a.h, b.y + b.h)
    return Geom:new{ x = x0, y = y0, w = x1 - x0, h = y1 - y0 }
end

-- CReDocument creates its native view in :init() using CanvasContext's
-- screen dimensions. Temporarily expose the panel's content dimensions only
-- during DocumentRegistry:openDocument(), then always restore the real screen.
-- This is synchronous by design: never yield or schedule work in this block.
local function openWithCanvasSize(width, height, callback)
    local real_screen = CanvasContext.screen
    if not real_screen then error("CanvasContext has no initialized screen") end

    local panel_screen = setmetatable({
        getWidth = function() return width end,
        getHeight = function() return height end,
    }, {
        __index = function(_t, key)
            local value = real_screen[key]
            if type(value) == "function" then
                return function(_self, ...) return value(real_screen, ...) end
            end
            return value
        end,
    })

    CanvasContext.screen = panel_screen
    local ok, result = xpcall(callback, tracebackError)
    CanvasContext.screen = real_screen
    if not ok then error(result) end
    return result
end

------------------------------------------------------------------------
-- Per-panel reading settings (same options as the stock bottom dialog)
------------------------------------------------------------------------

-- Only settings that can safely apply to an independent CRe view.
-- Device rotation and ReaderUI-only/global options are intentionally excluded.
local PANEL_CONFIG_GROUPS = {
    { source = 2, names = {
        h_page_margins = true, sync_t_b_page_margins = true,
        t_page_margin = true, b_page_margin = true,
    } },
    { source = 3, names = {
        view_mode = true, block_rendering_mode = true,
        render_dpi = true, line_spacing = true,
    } },
    { source = 4, names = {
        font_size = true, font_fine_tune = true, word_spacing = true,
        word_expansion = true, cjk_width_scaling = true,
    } },
    { source = 5, names = {
        font_gamma = true, font_base_weight = true,
        font_hinting = true, font_kerning = true,
    } },
    { source = 6, names = {
        embedded_fonts = true, smooth_scaling = true, nightmode_images = true,
    } },
}

-- Keep in sync with ReaderTypeset's native CRe block-rendering presets.
local BLOCK_RENDERING_FLAGS = {
    0x00000000, -- legacy
    0x03030031, -- flat
    0x03375131, -- book
    0x7FFFFFFF, -- web
}

local panel_config_options_cache
local function getPanelConfigOptions()
    if panel_config_options_cache then return panel_config_options_cache end
    local all_options = require("ui/data/creoptions")
    local filtered = { prefix = all_options.prefix }
    for _i, group_spec in ipairs(PANEL_CONFIG_GROUPS) do
        local source_group = all_options[group_spec.source]
        if source_group then
            local group = { icon = source_group.icon, options = {} }
            for _j, option in ipairs(source_group.options or {}) do
                if option.name and group_spec.names[option.name] then
                    table.insert(group.options, option)
                end
            end
            if #group.options > 0 then table.insert(filtered, group) end
        end
    end
    panel_config_options_cache = filtered
    return filtered
end

local function createPanelConfigurable(config_options, doc_settings)
    local configurable = {}
    local settings = G_reader_settings
    for _i, group in ipairs(config_options) do
        for _j, option in ipairs(group.options or {}) do
            local name = option.name
            if name and configurable[name] == nil then
                local value
                local setting_key = (config_options.prefix or "copt") .. "_" .. name
                if doc_settings then
                    value = try(doc_settings.readSetting, doc_settings, setting_key)
                end
                if value == nil and settings then
                    value = try(settings.readSetting, settings, setting_key)
                end
                if value == nil then
                    value = option.default_value
                    -- Match ReaderTypeset: fresh documents default to web mode
                    -- unless the user has explicitly chosen another mode.
                    if name == "block_rendering_mode" and settings
                            and settings:readSetting("copt_block_rendering_mode") == nil then
                        value = 3
                    end
                end
                if name == "sync_t_b_page_margins" then
                    value = (value == true or tonumber(value) == 1) and 1 or 0
                end
                if value == nil and option.values and #option.values > 0 then
                    local position = option.default_pos or 1
                    value = option.values[math.max(1, math.min(#option.values, position))]
                end
                configurable[name] = copyConfigValue(value)
            end
        end
    end
    return configurable
end

local function applyPanelMargins(doc, configurable)
    if type(doc.setPageMargins) ~= "function" then return end
    local horizontal = configurable.h_page_margins or { 0, 0 }
    local left = type(horizontal) == "table" and horizontal[1] or horizontal
    local right = type(horizontal) == "table" and horizontal[2] or horizontal
    left = tonumber(left) or 0
    right = tonumber(right) or left
    local top = tonumber(configurable.t_page_margin) or 0
    local bottom = tonumber(configurable.b_page_margin) or 0
    if configurable.sync_t_b_page_margins == 1 or configurable.sync_t_b_page_margins == true then
        bottom = top
        configurable.b_page_margin = top
    end
    doc:setPageMargins(Screen:scaleBySize(left), Screen:scaleBySize(top),
        Screen:scaleBySize(right), Screen:scaleBySize(bottom))
end

-- crengine's "alternative status bar": the book title header at the top of the
-- page. Same values ReaderTypeset uses: 0 = shown, 1 = hidden.
local function applyHeaderSetting(doc, show_header)
    if type(doc.setStatusLineProp) == "function" then
        doc:setStatusLineProp(show_header and 0 or 1)
    end
end

-- Applies the same core CRe settings ReaderFont/ReaderTypeset apply in ReaderUI.
local function applyPanelConfigToDocument(doc, c)
    local function has(name) return c[name] ~= nil end
    local function flag(value) return value == 1 or value == true end
    if has("view_mode") and doc.setViewMode then
        doc:setViewMode(c.view_mode == 1 and "scroll" or "page")
    end
    if has("block_rendering_mode") and doc.setBlockRenderingFlags then
        local mode = clamp(c.block_rendering_mode, 0, #BLOCK_RENDERING_FLAGS - 1, 2)
        doc:setBlockRenderingFlags(BLOCK_RENDERING_FLAGS[mode + 1])
    end
    if has("render_dpi") and doc.setRenderDPI then doc:setRenderDPI(c.render_dpi) end
    if has("embedded_fonts") and doc.setEmbeddedFonts then doc:setEmbeddedFonts(c.embedded_fonts) end
    if has("smooth_scaling") and doc.setImageScaling then doc:setImageScaling(flag(c.smooth_scaling)) end
    if has("nightmode_images") and doc.setNightmodeImages then
        doc:setNightmodeImages(flag(c.nightmode_images))
    end
    if has("font_size") and doc.setFontSize then doc:setFontSize(Screen:scaleBySize(c.font_size)) end
    if has("font_base_weight") and doc.setFontBaseWeight then doc:setFontBaseWeight(c.font_base_weight) end
    if has("font_hinting") and doc.setFontHinting then doc:setFontHinting(c.font_hinting) end
    if has("font_kerning") and doc.setFontKerning then doc:setFontKerning(c.font_kerning) end
    if has("word_spacing") and doc.setWordSpacing then doc:setWordSpacing(c.word_spacing) end
    if has("word_expansion") and doc.setWordExpansion then doc:setWordExpansion(c.word_expansion) end
    if has("cjk_width_scaling") and doc.setCJKWidthScaling then
        doc:setCJKWidthScaling(c.cjk_width_scaling)
    end
    if has("line_spacing") and doc.setInterlineSpacePercent then
        doc:setInterlineSpacePercent(c.line_spacing)
    end
    if has("font_gamma") and doc.setGammaIndex then doc:setGammaIndex(c.font_gamma) end
    applyPanelMargins(doc, c)
end

-- Persists the per-book settings used by ReaderUI, through DocSettings.
-- DocSettings resolves the user's configured .sdr location (hash/dir modes too).
local function savePanelConfig(record)
    if not record or not record.doc_settings or not record.configurable then return end
    local prefix = record.config_prefix or "copt"
    for name, value in pairs(record.configurable) do
        pcall(record.doc_settings.saveSetting, record.doc_settings, prefix .. "_" .. name,
            copyConfigValue(value))
    end
end

-- secondary = true: the same book is open in the other panel and that panel
-- is the one that writes the reading position and settings.
local function saveDocumentRecord(record, secondary)
    if not record or not record.doc_settings then return end
    local settings = record.doc_settings
    local doc = record.doc
    if not secondary then
        if doc and record.kind == "reflowable" then
            local xpointer = getDocumentXPointer(doc)
            if xpointer then
                pcall(settings.saveSetting, settings, "last_xpointer", xpointer)
                if type(doc.getEPubCFIFromXPointer) == "function" then
                    local cfi = try(doc.getEPubCFIFromXPointer, doc, xpointer)
                    if cfi then pcall(settings.saveSetting, settings, "last_epubcfi", cfi) end
                end
            end
            local count = getReflowablePageCount(doc)
            local page = tonumber(record.page)
            if count > 0 and page then
                pcall(settings.saveSetting, settings, "percent_finished",
                    math.max(0, math.min(1, page / count)))
            end
            if not record.temp_copy then
                local cache_path = try(doc.getCacheFilePath, doc)
                if cache_path then pcall(settings.saveSetting, settings, "cache_file_path", cache_path) end
            end
        elseif doc and record.kind == "paged" then
            local count = tonumber(record.page_count) or 0
            local page = tonumber(record.page) or 1
            pcall(settings.saveSetting, settings, "last_page", page)
            if count > 0 then
                pcall(settings.saveSetting, settings, "percent_finished",
                    math.max(0, math.min(1, page / count)))
            end
        end
        savePanelConfig(record)
    end
    if record.annotations then
        pcall(settings.saveSetting, settings, "annotations", record.annotations)
    end
    pcall(settings.flush, settings)
end

-- Reading ratio used to compare the two panels of the same book.
local function getRecordRatio(record)
    local count
    if record.kind == "reflowable" then
        count = getReflowablePageCount(record.doc)
    else
        count = tonumber(record.page_count) or 0
    end
    if count < 1 then return 0 end
    return (tonumber(record.page) or 1) / count
end

-- True when record `a` is at or behind record `b` in the same book.
local function isBehind(a, b)
    if a.kind == "reflowable" and a.doc and b.doc and type(a.doc.compareXPointers) == "function" then
        local xa, xb = getDocumentXPointer(a.doc), getDocumentXPointer(b.doc)
        if xa and xb then
            local order = try(a.doc.compareXPointers, a.doc, xa, xb)
            if order == 1 or order == 0 then return true end
            if order == -1 then return false end
        end
    end
    return getRecordRatio(a) <= getRecordRatio(b)
end

-- Saves the records of a session. When the same book is open in both panels
-- only the panel that is further BEHIND writes its position, so opening the
-- book normally later never skips text that one of the panels has not read.
local function saveSessionRecords(session, only_index)
    local records = session.records
    local first, second = records[1], records[2]
    local shared = first and second and first.doc and second.doc
        and first.doc_settings ~= nil and first.doc_settings == second.doc_settings
    local owner
    if shared then owner = isBehind(first, second) and first or second end
    for index = 1, 2 do
        if only_index == nil or only_index == index then
            local record = records[index]
            if record then saveDocumentRecord(record, shared and record ~= owner or false) end
        end
    end
end

-- Writes the annotation list to the sidecar immediately. Returns true on success.
local function persistAnnotations(record)
    if not record or not record.doc_settings then return false end
    local ok, err = pcall(function()
        record.doc_settings:saveSetting("annotations", record.annotations)
        record.doc_settings:flush()
    end)
    record.ann_gen = (record.ann_gen or 0) + 1
    record.hl_cache = nil
    return ok, err
end

------------------------------------------------------------------------
-- Drawing
------------------------------------------------------------------------

local function paintPanelFrame(bb, rect, is_active)
    bb:paintRect(rect.x, rect.y, rect.w, rect.h, Blitbuffer.COLOR_WHITE)
    if is_active and rect.w > 0 and rect.h > 0 then
        -- A one-pixel outline identifies the active panel without wasting space.
        bb:paintRect(rect.x, rect.y, rect.w, 1, Blitbuffer.COLOR_BLACK)
        bb:paintRect(rect.x, rect.y + rect.h - 1, rect.w, 1, Blitbuffer.COLOR_BLACK)
        bb:paintRect(rect.x, rect.y, 1, rect.h, Blitbuffer.COLOR_BLACK)
        bb:paintRect(rect.x + rect.w - 1, rect.y, 1, rect.h, Blitbuffer.COLOR_BLACK)
    end
end

-- Computes (and caches) the highlight rectangles visible in the current view,
-- in content-local coordinates. The stock ReaderView does this for the normal
-- reader; panels have no ReaderView, so the plugin draws highlights itself.
local function getHighlightItems(record, content_h)
    local annotations = record.annotations
    if not annotations or #annotations == 0 then return nil end
    local doc = record.doc
    local scroll = isScrollMode(doc)
    local key = table.concat({
        scroll and "s" or "p",
        tostring(scroll and record.position or record.page),
        tostring(record.layout_gen or 0),
        tostring(record.ann_gen or 0),
        tostring(content_h),
    }, ":")
    local cache = record.hl_cache
    if cache and cache.key == key then return cache.items end

    local items = {}
    local top = tonumber(record.position) or 0
    for i = 1, #annotations do
        local ann = annotations[i]
        if ann.drawer and ann.pos0 and ann.pos1 then
            local in_view = true
            if scroll then
                local y0 = try(doc.getPosFromXPointer, doc, ann.pos0)
                local y1 = try(doc.getPosFromXPointer, doc, ann.pos1)
                if y0 and y1 then in_view = y1 >= top and y0 <= top + content_h end
            else
                local p0 = try(doc.getPageFromXPointer, doc, ann.pos0)
                local p1 = try(doc.getPageFromXPointer, doc, ann.pos1)
                if p0 and p1 then in_view = p0 <= record.page and record.page <= p1 end
            end
            if in_view then
                local boxes = try(doc.getScreenBoxesFromPositions, doc, ann.pos0, ann.pos1, true)
                local rects = {}
                if type(boxes) == "table" then
                    for j = 1, #boxes do
                        local b = boxes[j]
                        if type(b) == "table" and type(b.x) == "number" and type(b.y) == "number"
                                and type(b.w) == "number" and type(b.h) == "number"
                                and b.w > 0 and b.h > 0
                                and b.y < content_h and b.y + b.h > 0 then
                            rects[#rects + 1] = { x = b.x, y = b.y, w = b.w, h = b.h }
                        end
                    end
                end
                if #rects > 0 then items[#items + 1] = { ann = ann, rects = rects } end
            end
        end
    end
    record.hl_cache = { key = key, items = items }
    return items
end

local function paintHighlightRect(bb, x, y, w, h, drawer)
    if w < 1 or h < 1 then return end
    if drawer == "underscore" then
        bb:paintRect(x, y + h - 2, w, 2, Blitbuffer.gray(0.35))
    elseif drawer == "strikeout" then
        bb:paintRect(x, y + math.floor(h / 2), w, 2, Blitbuffer.gray(0.35))
    elseif drawer == "invert" then
        bb:invertRect(x, y, w, h)
    elseif bb.darkenRect then
        bb:darkenRect(x, y, w, h, 0.2)
    else
        bb:invertRect(x, y, w, h)
    end
end

local function drawHighlights(bb, record, content)
    local items = getHighlightItems(record, content.h)
    if not items then return end
    local note_size = Screen:scaleBySize(4)
    for i = 1, #items do
        local item = items[i]
        local last
        for j = 1, #item.rects do
            local r = item.rects[j]
            local y0 = math.max(0, r.y)
            local y1 = math.min(content.h, r.y + r.h)
            local x0 = math.max(0, r.x)
            local x1 = math.min(content.w, r.x + r.w)
            if y1 > y0 and x1 > x0 then
                paintHighlightRect(bb, content.x + x0, content.y + y0, x1 - x0, y1 - y0,
                    item.ann.drawer)
                last = { x = x1, y = y0 }
            end
        end
        if last and item.ann.note and item.ann.note ~= "" then
            -- Small square at the end of the passage marks highlights with notes.
            bb:paintRect(content.x + math.min(content.w - note_size, last.x),
                content.y + last.y, note_size, note_size, Blitbuffer.COLOR_BLACK)
        end
    end
end

local function drawSelection(bb, record, content)
    local selection = record.selection
    local boxes = selection and selection.sboxes
    if type(boxes) ~= "table" then return end
    for i = 1, #boxes do
        local b = boxes[i]
        if type(b) == "table" and type(b.x) == "number" and type(b.y) == "number"
                and type(b.w) == "number" and type(b.h) == "number" and b.w > 0 and b.h > 0 then
            local y0 = math.max(0, b.y)
            local y1 = math.min(content.h, b.y + b.h)
            local x0 = math.max(0, b.x)
            local x1 = math.min(content.w, b.x + b.w)
            if y1 > y0 and x1 > x0 then
                bb:invertRect(content.x + x0, content.y + y0, x1 - x0, y1 - y0)
            end
        end
    end
end

local function getChapterTitle(record, page)
    if record.kind ~= "reflowable" then return getBaseName(record.path) end
    if record.toc_gen ~= record.layout_gen then
        record.toc_gen = record.layout_gen
        local toc = try(record.doc.getToc, record.doc)
        record.toc_entries = type(toc) == "table" and toc or {}
    end
    local title
    for i = 1, #record.toc_entries do
        local entry = record.toc_entries[i]
        local entry_page = tonumber(entry.page)
        if entry_page then
            if entry_page <= page then title = entry.title or entry.text else break end
        end
    end
    return title and tostring(title) or getBaseName(record.path)
end

local function drawFooter(bb, record, panel, footer_h)
    local doc = record.doc
    local face = Font:getFace("ffont", 12)
    local left = panel.x + PANEL_MARGIN
    local width = panel.w - PANEL_MARGIN * 2
    local top = panel.y + panel.h - PANEL_MARGIN - footer_h

    local page, total
    if record.kind == "reflowable" then
        total = getReflowablePageCount(doc)
        page = record.page
        if isScrollMode(doc) then page = try(doc.getCurrentPage, doc) or record.page end
    else
        total = record.page_count or getPageCount(doc)
        page = record.page
    end
    page = tonumber(page) or 1
    total = math.max(1, tonumber(total) or 1)
    local percent = math.floor(math.min(1, page / total) * 100)

    bb:paintRect(left, top, width, 1, Blitbuffer.gray(0.75))
    local baseline = top + footer_h - Screen:scaleBySize(5)
    local right_text = string.format("%d / %d  \xC2\xB7  %d%%", page, total, percent)
    local right_w = RenderText:sizeUtf8Text(0, width, face, right_text, true, false).x
    RenderText:renderUtf8Text(bb, left + width - right_w, baseline, face, right_text, true)

    local title = getChapterTitle(record, page)
    local available = width - right_w - Screen:scaleBySize(12)
    if title ~= "" and available > 40 then
        local ok, shown = pcall(RenderText.getSubTextByWidth, RenderText, title, face,
            available, true, false)
        if ok and type(shown) == "string" and shown ~= "" then
            RenderText:renderUtf8Text(bb, left, baseline, face, shown, true)
        end
    end
end

-- Calculates the visible page region for fixed-layout documents. Pan positions
-- are stored as normalized ratios, so they remain valid after zoom or panel resize.
local function getPagedViewport(record, content)
    local doc = record and record.doc
    if not doc then return nil end
    local page = tonumber(record.page) or 1
    local native = doc:getNativePageDimensions(page)
    if not native or type(native.w) ~= "number" or type(native.h) ~= "number"
            or native.w <= 0 or native.h <= 0 then
        error("Document returned invalid page dimensions")
    end

    local fit_zoom = math.min(content.w / native.w, content.h / native.h)
    if type(fit_zoom) ~= "number" or fit_zoom <= 0 then error("Invalid page zoom") end
    local zoom_factor = clamp(record.zoom_factor, MIN_PAGE_ZOOM, MAX_PAGE_ZOOM, MIN_PAGE_ZOOM)
    local zoom = fit_zoom * zoom_factor
    local page_size = doc:getPageDimensions(page, zoom, 0)
    if not page_size or page_size.w <= 0 or page_size.h <= 0 then
        error("Document returned invalid scaled page dimensions")
    end

    local visible_w = math.max(1, math.floor(math.min(content.w, page_size.w)))
    local visible_h = math.max(1, math.floor(math.min(content.h, page_size.h)))
    local max_x = math.max(0, math.floor(page_size.w - visible_w))
    local max_y = math.max(0, math.floor(page_size.h - visible_h))
    local pan_x = clamp(record.zoom_pan_x, 0, 1, 0.5)
    local pan_y = clamp(record.zoom_pan_y, 0, 1, 0.5)
    local offset_x = math.floor(max_x * pan_x + 0.5)
    local offset_y = math.floor(max_y * pan_y + 0.5)

    return {
        zoom = zoom,
        max_x = max_x,
        max_y = max_y,
        pan_x = pan_x,
        pan_y = pan_y,
        draw_x = content.x + math.floor((content.w - visible_w) / 2),
        draw_y = content.y + math.floor((content.h - visible_h) / 2),
        visible = Geom:new{ x = offset_x, y = offset_y, w = visible_w, h = visible_h },
    }
end

local function drawDocumentPage(bb, record, content)
    local doc = record and record.doc
    if not doc then return end
    if not doc.info or not doc.info.has_pages then
        error("This document does not expose a paged layout")
    end
    local page_count = getPageCount(doc)
    if page_count < 1 then error("Document has no readable pages") end

    record.page = math.max(1, math.min(record.page or 1, page_count))
    record.page_count = page_count
    local viewport = getPagedViewport(record, content)
    doc:drawPage(bb, viewport.draw_x, viewport.draw_y, viewport.visible,
        record.page, viewport.zoom, 0, 1.0, 1.0)
end

local function drawReflowablePage(bb, record, content)
    local doc = record and record.doc
    if not doc then return end
    local rect = Geom:new{ x = 0, y = 0, w = content.w, h = content.h }

    if isScrollMode(doc) then
        local full_height = doc.info and doc.info.doc_height or content.h
        local max_position = math.max(0, full_height - content.h)
        record.position = math.max(0, math.min(max_position, tonumber(record.position) or 0))
        doc:drawCurrentViewByPos(bb, content.x, content.y, rect, record.position)
    else
        local page_count = getReflowablePageCount(doc)
        if page_count < 1 then error("Reflowable document has no rendered pages") end
        record.page = math.max(1, math.min(page_count, tonumber(record.page) or 1))
        doc:drawCurrentViewByPage(bb, content.x, content.y, rect, record.page)
    end
    drawHighlights(bb, record, content)
    drawSelection(bb, record, content)
end

------------------------------------------------------------------------
-- Canvas: paints both panels
------------------------------------------------------------------------

local SplitCanvas = Widget:extend{}

function SplitCanvas:_paint(bb, x, y)
    local session = self.session
    local w, h = self.dimen.w, self.dimen.h
    if type(w) ~= "number" or type(h) ~= "number" or w < 80 or h < 80 then
        error("Invalid window dimensions: " .. tostring(w) .. " x " .. tostring(h))
    end
    -- The window always covers the whole screen, so layout coordinates are absolute.
    bb:paintRect(x, y, w, h, Blitbuffer.COLOR_WHITE)

    for index = 1, 2 do
        local panel, content, footer_h = getPanelLayout(session, index)
        local record = session.records[index]
        paintPanelFrame(bb, panel, index == session.active_panel)

        if record and record.doc then
            local ok, err = xpcall(function()
                if record.kind == "reflowable" then
                    drawReflowablePage(bb, record, content)
                else
                    drawDocumentPage(bb, record, content)
                end
            end, tracebackError)
            if ok then
                record.render_error = nil
                if footer_h > 0 then
                    local footer_ok, footer_err = pcall(drawFooter, bb, record, panel, footer_h)
                    if not footer_ok and record.logged_footer_error ~= tostring(footer_err) then
                        record.logged_footer_error = tostring(footer_err)
                        appendDebugLog(session.plugin, "footer_panel_" .. index, footer_err)
                    end
                end
            else
                record.render_error = tostring(err)
                if record.logged_render_error ~= record.render_error then
                    record.logged_render_error = record.render_error
                    appendDebugLog(session.plugin, "render_panel_" .. index, record.render_error)
                end
                bb:paintRect(panel.x + 8, panel.y + 8, math.max(1, panel.w - 16),
                    math.max(1, panel.h - 16), Blitbuffer.COLOR_WHITE)
                drawText(bb, panel.x + PANEL_INSET, panel.y + 12, "RENDER ERROR", 17)
                drawText(bb, panel.x + PANEL_INSET, panel.y + 36, record.render_error:sub(1, 90), 12)
            end
        else
            drawText(bb, panel.x + PANEL_INSET + 4, panel.y + math.floor(panel.h * 0.50),
                _("Tap to choose a document"), 17)
        end
    end

    local first, _second, side_by_side = sessionRects(session)
    if side_by_side then
        bb:paintRect(x + first.w, y, DIVIDER_SIZE, h, Blitbuffer.gray(0.30))
    else
        bb:paintRect(x, y + first.h, w, DIVIDER_SIZE, Blitbuffer.gray(0.30))
    end

    -- Small grip in the middle of the divider: it can always be dragged.
    local grip = Screen:scaleBySize(36)
    if side_by_side then
        bb:paintRect(x + first.w - 1, y + math.floor((h - grip) / 2), DIVIDER_SIZE + 2, grip,
            Blitbuffer.COLOR_BLACK)
    else
        bb:paintRect(x + math.floor((w - grip) / 2), y + first.h - 1, grip, DIVIDER_SIZE + 2,
            Blitbuffer.COLOR_BLACK)
    end

    -- Live preview while the divider is being dragged.
    if session.drag_ratio then
        local preview = sessionRects(session, session.drag_ratio)
        if side_by_side then
            bb:paintRect(x + preview.w - 1, y, DIVIDER_SIZE + 2, h, Blitbuffer.COLOR_BLACK)
        else
            bb:paintRect(x, y + preview.h - 1, w, DIVIDER_SIZE + 2, Blitbuffer.COLOR_BLACK)
        end
    end
end

function SplitCanvas:paintTo(bb, x, y)
    x = x or 0
    y = y or 0
    local ok, err = xpcall(function() self:_paint(bb, x, y) end, tracebackError)
    if not ok then
        local plugin = self.session.plugin
        plugin.last_error = tostring(err)
        plugin.last_error_stage = "canvas_paint"
        appendDebugLog(plugin, "canvas_paint", err)
        pcall(function()
            bb:paintRect(x, y, self.dimen.w, self.dimen.h, Blitbuffer.COLOR_WHITE)
            bb:paintRect(x + 4, y + 4, self.dimen.w - 8, 3, Blitbuffer.COLOR_BLACK)
        end)
    end
end

------------------------------------------------------------------------
-- Window: input handling
------------------------------------------------------------------------

local SplitWindow = InputContainer:extend{
    name = "parallelreader_window",
    is_always_active = true,
    covers_fullscreen = true,
    key_events = {
        PressMenu = { { "Menu" } },
        CloseWindow = { { "Back" } },
        NextPanelPage = { { "RPgFwd" }, { "LPgFwd" } },
        PrevPanelPage = { { "RPgBack" }, { "LPgBack" } },
    },
}

local function fullScreenZone()
    return { ratio_x = 0, ratio_y = 0, ratio_w = 1, ratio_h = 1 }
end

function SplitWindow:init()
    local plugin = self.session.plugin
    local ok, err = runStage(plugin, "window_init", function()
        self:registerTouchZones({
            {
                id = "parallel_reader_tap",
                ges = "tap",
                screen_zone = fullScreenZone(),
                handler = function(ges)
                    runStage(plugin, "tap", function()
                        plugin:handlePanelTouch(self.session, ges and ges.pos)
                    end)
                    return true
                end,
            },
            {
                id = "parallel_reader_swipe",
                ges = "swipe",
                screen_zone = fullScreenZone(),
                handler = function(ges)
                    local handled = false
                    runStage(plugin, "swipe", function()
                        handled = plugin:handleSwipe(self.session, ges)
                    end)
                    return handled
                end,
            },
            {
                id = "parallel_reader_hold",
                ges = "hold",
                screen_zone = fullScreenZone(),
                handler = function(ges)
                    runStage(plugin, "text_hold", function()
                        plugin:onTextHold(self.session, ges)
                    end)
                    return true
                end,
            },
            {
                id = "parallel_reader_hold_pan",
                ges = "hold_pan",
                rate = 30,
                screen_zone = fullScreenZone(),
                handler = function(ges)
                    plugin:onTextHoldPan(self.session, ges)
                    return true
                end,
            },
            {
                id = "parallel_reader_hold_release",
                ges = "hold_release",
                screen_zone = fullScreenZone(),
                handler = function(ges)
                    plugin:onTextHoldRelease(self.session, ges)
                    return true
                end,
            },
            {
                id = "parallel_reader_pan",
                ges = "pan",
                rate = 10,
                screen_zone = fullScreenZone(),
                handler = function(ges)
                    local handled = false
                    runStage(plugin, "divider_pan", function()
                        handled = plugin:handlePan(self.session, ges)
                    end)
                    return handled
                end,
            },
            {
                id = "parallel_reader_pan_release",
                ges = "pan_release",
                screen_zone = fullScreenZone(),
                handler = function(ges)
                    local handled = false
                    runStage(plugin, "divider_release", function()
                        handled = plugin:handlePanRelease(self.session, ges)
                    end)
                    return handled
                end,
            },
        })
    end)
    if not ok then error(err) end
end

function SplitWindow:onShow()
    pcall(UIManager.setDirty, UIManager, self, "full")
end

function SplitWindow:onPressMenu()
    self.session.plugin:showReaderMenu(self.session)
    return true
end

function SplitWindow:onCloseWindow()
    self.session.plugin:closeParallelReader(false)
    return true
end

function SplitWindow:onNextPanelPage()
    self.session.plugin:changePage(self.session.active_panel or 1, 1)
    return true
end

function SplitWindow:onPrevPanelPage()
    self.session.plugin:changePage(self.session.active_panel or 1, -1)
    return true
end

function SplitWindow:onSetDimensions(dimen)
    local plugin = self.session.plugin
    runStage(plugin, "window_resize", function()
        self.dimen = dimen
        self.session.screen_w = dimen.w
        self.session.screen_h = dimen.h
        if self[1] then self[1].dimen = Geom:new{ x = 0, y = 0, w = dimen.w, h = dimen.h } end
        self:updateTouchZonesOnScreenResize(dimen)
        plugin:scheduleViewportRefresh()
        UIManager:setDirty(self, "full")
    end)
end

function SplitWindow:onCloseWidget()
    local session = self.session
    local plugin = session.plugin
    if session.menu_container then
        local menu_container = session.menu_container
        session.menu_container = nil
        session.reader_menu = nil
        pcall(UIManager.close, UIManager, menu_container)
    end
    if session.bottom_menu then
        local bottom_menu = session.bottom_menu
        session.bottom_menu = nil
        pcall(UIManager.close, UIManager, bottom_menu)
    end

    -- Decide where to go next before the records are released.
    local target_path = plugin:pickReturnPath(session)
    plugin:rememberSession(session)
    saveSessionRecords(session)
    for index = 1, 2 do
        closeDocumentRecord(session.records[index])
        session.records[index] = nil
    end
    if plugin.window == self then plugin.window = nil end
    if active_window == self then active_window = nil end
    plugin:afterWindowClosed(session, target_path)
end

------------------------------------------------------------------------
-- Plugin: lifecycle and menu entry
------------------------------------------------------------------------

-- True when the plugin instance lives inside the normal reader (a book is open).
local function isInsideBook(ui)
    return ui ~= nil and (ui.document ~= nil or ui.name == "ReaderUI")
end

function ParallelReader:init()
    -- crengine cannot safely host the plugin's own document views next to the
    -- book that is being read, so the plugin stays completely inert inside a
    -- book (no menu entry, no action) and only works from the file manager.
    if isInsideBook(self.ui) then return end
    pcall(function() self:onDispatcherRegisterActions() end)
    self.ui.menu:registerToMainMenu(self)
end

-- Lets the user assign "Parallel Reader" to a gesture or a profile.
function ParallelReader:onDispatcherRegisterActions()
    Dispatcher:registerAction("parallelreader_open", {
        category = "none",
        event = "ShowParallelReader",
        title = _("Parallel Reader"),
        general = true,
    })
end

function ParallelReader:onShowParallelReader()
    if isInsideBook(self.ui) then
        showInfo(_("Parallel Reader can only be opened from the file manager, not from inside a book."), 5)
        return true
    end
    self:openParallelReader()
    return true
end

function ParallelReader:addToMainMenu(menu_items)
    menu_items.parallel_reader = {
        text = _("Parallel Reader"),
        sorting_hint = "tools",
        callback = function() self:openParallelReader() end,
    }
end

-- Full-window or region refreshes. Page turns use partial refreshes limited to
-- the panel and flash every N pages, like the stock reader.
function ParallelReader:refreshWindow(mode, region)
    if self.window then UIManager:setDirty(self.window, mode or "full", region) end
end

function ParallelReader:refreshPanelRegion(index, mode)
    local session = self.session
    if not (session and self.window) then return end
    local panel = getPanelLayout(session, index)
    UIManager:setDirty(self.window, mode or "ui", panel)
end

function ParallelReader:refreshPanel(index)
    local session = self.session
    if not (session and self.window) then return end
    session.refresh_counter = (session.refresh_counter or 0) + 1
    local limit = tonumber((G_reader_settings:readSetting("full_refresh_count")))
    if limit == nil then limit = 6 end
    local mode = "partial"
    if limit == 0 or (limit > 0 and session.refresh_counter >= limit) then
        mode = "flashpartial"
        session.refresh_counter = 0
    end
    UIManager:setDirty(self.window, mode, (getPanelLayout(session, index)))
end

function ParallelReader:createAndShowWindow()
    local width, height = Screen:getWidth(), Screen:getHeight()
    if type(width) ~= "number" or type(height) ~= "number" or width <= 0 or height <= 0 then
        error("Invalid screen dimensions: " .. tostring(width) .. " x " .. tostring(height))
    end
    pcall(clearTempDir)
    local prefs = getPrefs()
    self.last_path = prefs.last_path
    self.session = {
        plugin = self,
        split_ratio = clamp(prefs.split_ratio, MIN_SPLIT, MAX_SPLIT, 0.50),
        split_mode = clamp(prefs.split_mode, 0, 2, 0),
        show_footer = prefs.show_footer ~= false,
        show_header = prefs.show_header == true,
        active_panel = 1,
        menu_tab_index = 1,
        initial_rotation_mode = Screen:getRotationMode(),
        refresh_counter = 0,
        screen_w = width,
        screen_h = height,
        records = {},
    }
    local canvas = SplitCanvas:new{
        session = self.session,
        dimen = Geom:new{ x = 0, y = 0, w = width, h = height },
    }
    local window = SplitWindow:new{
        session = self.session,
        dimen = Geom:new{ x = 0, y = 0, w = width, h = height },
        canvas,
    }
    self.window = window
    self.session.window = window
    active_window = window
    UIManager:show(window, "full")
end

function ParallelReader:openParallelReader()
    if isInsideBook(self.ui) then
        showInfo(_("Parallel Reader can only be opened from the file manager, not from inside a book."), 5)
        return
    end
    if active_window then
        showInfo(_("Parallel Reader is already open."), 3)
        return
    end
    self.last_error = nil
    self.last_error_stage = nil

    local ok, err = runStage(self, "create_window", function() self:createAndShowWindow() end)
    if not ok then
        self.window = nil
        active_window = nil
        showInfo(_("Could not open Parallel Reader:") .. "\n\n" .. tostring(err), 12)
    end
end

-- Picks the book to continue in the normal reader: the active panel's one first.
function ParallelReader:pickReturnPath(session)
    local active = session.records[session.active_panel or 1]
    if active and active.path then return active.path end
    for index = 1, 2 do
        local record = session.records[index]
        if record and record.path then return record.path end
    end
    return nil
end

function ParallelReader:rememberSession(session)
    local paths = {}
    for index = 1, 2 do
        local record = session.records[index]
        paths[index] = record and record.path or false
    end
    local prefs = getPrefs()
    prefs.last_paths = paths
    prefs.split_ratio = session.split_ratio
    prefs.split_mode = session.split_mode
    prefs.show_footer = session.show_footer
    prefs.show_header = session.show_header
    if self.last_path then prefs.last_path = self.last_path end
    G_reader_settings:saveSetting(SETTINGS_KEY, prefs)
end

local function showLibrary(path)
    local ok, err = pcall(function()
        local FileManager = require("apps/filemanager/filemanager")
        local dir = path and ffiUtil.dirname(path) or nil
        FileManager:showFiles(dir, path)
    end)
end

local function openInNormalReader(path)
    local ok, err = pcall(function()
        local ReaderUI = require("apps/reader/readerui")
        ReaderUI:showReader(path)
    end)
    if not ok then
        showLibrary(path)
    end
end

-- When the user chose "Close and continue in the normal reader", the book of the
-- active panel is opened in the stock reader once all panel documents are closed.
function ParallelReader:afterWindowClosed(session, target_path)
    if session.closing_mode == "reader" and target_path then
        UIManager:nextTick(function() openInNormalReader(target_path) end)
    end
end

-- want_reader: continue the active panel's book in the normal reader.
function ParallelReader:closeParallelReader(want_reader)
    local session = self.session
    if not session or not self.window then return end
    session.closing_mode = want_reader and "reader" or nil
    UIManager:close(self.window)
end

------------------------------------------------------------------------
-- Documents
------------------------------------------------------------------------

function ParallelReader:closeSlot(index)
    local record = self.session.records[index]
    saveSessionRecords(self.session, index)
    closeDocumentRecord(record)
    self.session.records[index] = nil
    self:refreshWindow("full")
end

function ParallelReader:loadDocumentIntoSlot(index, path, options)
    options = options or {}
    local session = self.session
    if not session then return false end
    local created_copy -- temporary copy of the book (same book in both panels)

    local ok, result = runStage(self, "open_document_panel_" .. index, function()
        return withBusy(_("Opening…"), function()
            if lfs.attributes(path, "mode") ~= "file" then
                error("Selected path is not a file: " .. tostring(path))
            end
            local provider = DocumentRegistry:getProvider(path)
            if not provider then error("KOReader has no document provider for this file") end

            local is_reflowable = provider.provider == "crengine"
            local current_record = session.records[index]
            if current_record and current_record.doc and current_record.path == path then
                error("This book is already open in this panel.")
            end

            -- Same book already open in the other panel? Then both panels share
            -- the book's sidecar (annotations, settings) and its reading position
            -- is saved as the smaller progress of the two.
            local sibling = session.records[index == 1 and 2 or 1]
            if not (sibling and sibling.doc and sibling.path == path) then sibling = nil end

            local open_path = path
            if is_reflowable then
                if sibling then
                    if not sibling.temp_copy then
                        -- DocumentRegistry shares one CreDocument per path: the second
                        -- view of the same book is opened from a private copy.
                        open_path = makeTempBookCopy(path)
                        created_copy = open_path
                    end
                elseif type(DocumentRegistry.getReferenceCount) == "function"
                        and DocumentRegistry:getReferenceCount(path) ~= nil then
                    -- A path already referenced by KOReader belongs to another live owner.
                    error("This reflowable file is already open elsewhere in KOReader. Close it there or choose another file.")
                end
                -- Keep the peak at two live CRe views.
                local other_record = session.records[index == 1 and 2 or 1]
                if current_record and current_record.kind == "reflowable"
                        and other_record and other_record.kind == "reflowable" then
                    error("Both panels already contain reflowable books. Close this panel first, then choose its replacement so Parallel Reader never creates a third crengine view.")
                end
            end

            local doc, panel_configurable, saved_xpointer
            local content_w, content_h = getPanelContentSize(session, index)
            local doc_settings = sibling and sibling.doc_settings or DocSettings:open(path)
            if is_reflowable then
                if options.xpointer then
                    saved_xpointer = options.xpointer
                elseif sibling then
                    -- Start where the other panel currently is.
                    saved_xpointer = getDocumentXPointer(sibling.doc)
                else
                    saved_xpointer = doc_settings:readSetting("last_xpointer")
                end
                local file_provider = shallowProviderForFile(provider, open_path)
                doc = openWithCanvasSize(content_w, content_h, function()
                    return DocumentRegistry:openDocument(open_path, file_provider)
                end)
                panel_configurable = options.configurable
                    or (sibling and sibling.configurable and copyConfigValue(sibling.configurable))
                    or createPanelConfigurable(getPanelConfigOptions(), doc_settings)
                -- Gamma is shared by the CRe engine on some builds: keep it consistent.
                if session.shared_font_gamma ~= nil then
                    panel_configurable.font_gamma = session.shared_font_gamma
                elseif panel_configurable.font_gamma ~= nil then
                    session.shared_font_gamma = panel_configurable.font_gamma
                end
            else
                doc = DocumentRegistry:openDocument(open_path, provider)
            end
            if not doc then
                error("KOReader could not initialize this document. Check Help > Bug Report for native/provider errors.")
            end
            if doc.is_locked then
                pcall(doc.close, doc)
                error("Password-protected documents are not supported in Parallel Reader yet")
            end

            local record
            if is_reflowable then
                -- Defensive check against accidental DocumentRegistry reuse.
                for slot = 1, 2 do
                    local existing = session.records[slot]
                    if slot ~= index and existing and existing.kind == "reflowable"
                            and existing.doc and existing.doc._document == doc._document then
                        pcall(doc.close, doc)
                        error("KOReader returned the same native crengine view for both panels; refusing to share it.")
                    end
                end
                -- Same essential CRe lifecycle as ReaderUI: defaults -> load -> render.
                local prepared, prepare_error = xpcall(function()
                    if type(doc.setupDefaultView) == "function" then doc:setupDefaultView() end
                    -- Preserve the DOM version associated with existing XPointer annotations.
                    if doc_settings and type(doc.requestDomVersion) == "function" then
                        local dom_version = doc_settings:readSetting("cre_dom_version")
                        if dom_version == nil then
                            if saved_xpointer and type(doc.getOldestDomVersion) == "function" then
                                dom_version = doc:getOldestDomVersion()
                            elseif type(doc.getLatestDomVersion) == "function" then
                                dom_version = doc:getLatestDomVersion()
                            end
                            if dom_version ~= nil then
                                doc_settings:saveSetting("cre_dom_version", dom_version)
                            end
                        end
                        if dom_version ~= nil then doc:requestDomVersion(dom_version) end
                    end
                    if type(doc.loadDocument) ~= "function" or not doc:loadDocument() then
                        error("crengine could not load this file. It may be invalid or unsupported.")
                    end
                    -- Apply settings after loading but before the first render.
                    if panel_configurable then applyPanelConfigToDocument(doc, panel_configurable) end
                    applyHeaderSetting(doc, session.show_header)
                    if type(doc.render) ~= "function" then
                        error("The crengine document does not expose render()")
                    end
                    doc:render()
                    if saved_xpointer and type(doc.gotoXPointer) == "function" then
                        local goto_ok, goto_error = pcall(doc.gotoXPointer, doc, saved_xpointer)
                        if not goto_ok then appendDebugLog(self, "restore_xpointer_warning", goto_error) end
                    end
                end, tracebackError)
                if not prepared then
                    pcall(doc.close, doc)
                    error(prepare_error)
                end

                local page_count = getReflowablePageCount(doc)
                if page_count < 1 then
                    pcall(doc.close, doc)
                    error("crengine rendered the document but reported no pages")
                end
                local page = try(doc.getCurrentPage, doc)
                if type(page) ~= "number" then page = 1 end

                local annotations
                if sibling then
                    -- One annotation table shared by both panels of the same book.
                    annotations = sibling.annotations
                else
                    local saved = doc_settings and doc_settings:readSetting("annotations") or {}
                    if type(saved) ~= "table" then saved = {} end
                    if #saved > 0 and type(saved[1].page) ~= "string" then
                        -- Match ReaderAnnotation's paging-to-rolling compatibility path.
                        if doc_settings and not doc_settings:has("annotations_paging") then
                            doc_settings:saveSetting("annotations_paging", saved)
                        end
                        local rolling = doc_settings and doc_settings:readSetting("annotations_rolling")
                        if type(rolling) == "table" then saved = rolling else saved = {} end
                    end
                    annotations = copyConfigValue(saved)
                end
                record = {
                    doc = doc, path = path, kind = "reflowable", provider = "crengine",
                    temp_copy = created_copy,
                    page = page, page_count = page_count,
                    position = getReflowablePosition(doc),
                    viewport_w = content_w, viewport_h = content_h,
                    configurable = panel_configurable,
                    config_prefix = getPanelConfigOptions().prefix or "copt",
                    doc_settings = doc_settings,
                    annotations = annotations,
                    layout_gen = 0, ann_gen = 0,
                }
            else
                if not doc.info or not doc.info.has_pages then
                    pcall(doc.close, doc)
                    error("This document does not expose a paged layout")
                end
                local page_count = getPageCount(doc)
                if page_count < 1 then
                    pcall(doc.close, doc)
                    error("The selected document has no readable pages")
                end
                local page = tonumber(options.page)
                    or (sibling and tonumber(sibling.page))
                    or tonumber(doc_settings and doc_settings:readSetting("last_page")) or 1
                record = {
                    doc = doc, path = path, kind = "paged", provider = provider.provider,
                    page = math.max(1, math.min(page_count, math.floor(page))),
                    page_count = page_count,
                    zoom_factor = MIN_PAGE_ZOOM,
                    zoom_pan_x = 0.5,
                    zoom_pan_y = 0.5,
                    doc_settings = doc_settings,
                }
            end

            -- Open and validate the replacement first. Only then release the
            -- previous panel document, keeping the old panel intact on failure.
            saveSessionRecords(session, index)
            closeDocumentRecord(session.records[index])
            session.records[index] = record
            self.last_path = ffiUtil.dirname(path)
            appendDebugLog(self, "document_loaded", string.format(
                "panel=%d file=%s pages=%d reflowable_views=%d same_book=%s", index, path,
                record.page_count or 0, countOpenReflowableDocuments(session), tostring(sibling ~= nil)))
            return true
        end)
    end)

    if not ok then
        if created_copy then pcall(os.remove, created_copy) end
        showInfo(_("Parallel Reader could not open this document:") .. "\n\n" .. tostring(result), 14)
        return false
    end
    self.last_error = nil
    self.last_error_stage = nil
    if not options.silent then
        pcall(function() require("readhistory"):addItem(path) end)
    end
    self:refreshWindow("full")
    return true
end

function ParallelReader:chooseDocument(index)
    if self.session then
        self.session.active_panel = index
        self:refreshWindow("ui")
    end
    local current_path = self.last_path
    if not current_path or lfs.attributes(current_path, "mode") ~= "directory" then
        local ok, filemanagerutil = pcall(require, "apps/filemanager/filemanagerutil")
        current_path = ok and filemanagerutil.getHomeFolder() or "/"
    end
    UIManager:show(PathChooser:new{
        title = index == 1 and _("Choose document for first panel")
            or _("Choose document for second panel"),
        select_directory = false,
        select_file = true,
        show_files = true,
        path = current_path,
        file_filter = function(filename) return DocumentRegistry:getProvider(filename) ~= nil end,
        onConfirm = function(path) self:loadDocumentIntoSlot(index, path) end,
    })
end

-- Reopens the two documents that were open when Parallel Reader was last closed.
function ParallelReader:resumeLastSession()
    local paths = getPrefs().last_paths
    if type(paths) ~= "table" then
        showInfo(_("There is no previous session to resume."), 4)
        return
    end
    local opened = 0
    for index = 1, 2 do
        local path = paths[index]
        if type(path) == "string" and lfs.attributes(path, "mode") == "file"
                and not self.session.records[index] then
            if self:loadDocumentIntoSlot(index, path) then opened = opened + 1 end
        end
    end
    if opened == 0 then showInfo(_("Nothing could be resumed."), 4) end
end

------------------------------------------------------------------------
-- Navigation
------------------------------------------------------------------------

-- Drops any text selection of a record without repainting.
function ParallelReader:dropSelection(record)
    if not record then return end
    if record.kind == "reflowable" and record.doc and type(record.doc.clearSelection) == "function" then
        pcall(record.doc.clearSelection, record.doc)
    end
    record.selection = nil
    record.hold_start_pos = nil
    record.hold_active = nil
end

function ParallelReader:changePage(index, delta)
    local record = self.session and self.session.records[index]
    if not record or not record.doc then
        showInfo(_("This panel has no document loaded."), 3)
        return
    end
    self:dropSelection(record)
    local moved = false
    if record.kind == "reflowable" then
        local doc = record.doc
        if isScrollMode(doc) then
            local _content_w, viewport_h = getPanelContentSize(self.session, index)
            local full_height = doc.info and doc.info.doc_height or viewport_h
            local current = tonumber(record.position) or getReflowablePosition(doc)
            local max_position = math.max(0, full_height - viewport_h)
            local target = math.max(0, math.min(max_position,
                current + delta * math.max(1, math.floor(viewport_h * 0.90))))
            moved = target ~= current
            record.position = target
        else
            local count = getReflowablePageCount(doc)
            local page = tonumber(record.page) or 1
            local target = math.max(1, math.min(count, page + delta))
            moved = target ~= page
            record.page = target
        end
    else
        local count = getPageCount(record.doc)
        local page = record.page or 1
        local target = math.max(1, math.min(count, page + delta))
        moved = target ~= page
        record.page = target
        if moved then
            record.zoom_pan_x = 0.5
            record.zoom_pan_y = 0.5
        end
    end
    if moved then self:refreshPanel(index) end
end

function ParallelReader:gotoPage(index, requested_page)
    local record = self.session and self.session.records[index]
    if not record or not record.doc then
        showInfo(_("This panel has no document loaded."), 3)
        return false
    end
    local page_count = record.page_count or getPageCount(record.doc)
    if record.kind == "reflowable" then page_count = getReflowablePageCount(record.doc) end
    if page_count < 1 then
        showInfo(_("The document does not report a valid page count."), 5)
        return false
    end
    local page = math.floor(tonumber(requested_page) or 0)
    if page < 1 or page > page_count then
        showInfo(string.format(_("Enter a page between 1 and %d."), page_count), 5)
        return false
    end
    self:dropSelection(record)
    if record.kind == "reflowable" and isScrollMode(record.doc) then
        local _content_w, viewport_h = getPanelContentSize(self.session, index)
        local full_height = record.doc.info and record.doc.info.doc_height or viewport_h
        local max_position = math.max(0, full_height - viewport_h)
        record.position = page_count > 1
            and math.floor(max_position * ((page - 1) / (page_count - 1))) or 0
    else
        record.page = page
        if record.kind == "paged" then
            record.zoom_pan_x = 0.5
            record.zoom_pan_y = 0.5
        end
    end
    self:refreshPanel(index)
    return true
end

-- Change magnification for the active fixed-layout page. Direction is -1/0/+1;
-- zero restores the fit-to-panel view. Zoom is intentionally not saved to .sdr.
function ParallelReader:adjustPageZoom(index, direction)
    local record = self.session and self.session.records[index]
    if not record or not record.doc or record.kind ~= "paged" then
        showInfo(_("Zoom is available for PDF, image, comic and other fixed-layout documents."), 5)
        return false
    end

    local current = clamp(record.zoom_factor, MIN_PAGE_ZOOM, MAX_PAGE_ZOOM, MIN_PAGE_ZOOM)
    local target
    if direction == 0 then
        target = MIN_PAGE_ZOOM
    elseif direction > 0 then
        target = math.min(MAX_PAGE_ZOOM, current * PAGE_ZOOM_STEP)
    else
        target = math.max(MIN_PAGE_ZOOM, current / PAGE_ZOOM_STEP)
    end
    if math.abs(target - current) < 0.001 then return false end

    record.zoom_factor = target
    if target <= MIN_PAGE_ZOOM then
        record.zoom_pan_x = 0.5
        record.zoom_pan_y = 0.5
    end
    self:refreshPanelRegion(index, "flashpartial")
    showInfo(string.format(_("Page zoom: %d%%"), math.floor(target * 100 + 0.5)), 2)
    return true
end

function ParallelReader:gotoXPointer(index, xpointer)
    local record = self.session and self.session.records[index]
    if not record or record.kind ~= "reflowable" or not record.doc or not xpointer then
        return false
    end
    if not pcall(record.doc.gotoXPointer, record.doc, xpointer) then return false end
    self:dropSelection(record)
    local page = try(record.doc.getCurrentPage, record.doc)
    if type(page) == "number" then record.page = page end
    record.position = getReflowablePosition(record.doc)
    self:refreshPanel(index)
    return true
end

-- Re-lays out reflowable panels whose size changed (split ratio, rotation,
-- footer toggle). Prefers resizing the native view in place; falls back to
-- reopening the document at the same XPointer.
function ParallelReader:scheduleViewportRefresh()
    if self._viewport_refresh_scheduled then return end
    self._viewport_refresh_scheduled = true
    UIManager:nextTick(function()
        self._viewport_refresh_scheduled = nil
        local session = self.session
        if not session or not self.window then return end
        for index = 1, 2 do
            local record = session.records[index]
            if record and record.kind == "reflowable" and record.doc then
                local width, height = getPanelContentSize(session, index)
                if record.viewport_w ~= width or record.viewport_h ~= height then
                    self:resizeReflowable(index, width, height)
                end
            end
        end
        self:refreshWindow("full")
    end)
end

function ParallelReader:resizeReflowable(index, width, height)
    local session = self.session
    local record = session.records[index]
    local doc = record.doc
    local xpointer = getDocumentXPointer(doc)
    self:dropSelection(record)

    local resized = false
    if type(doc.setViewDimen) == "function" then
        resized = pcall(doc.setViewDimen, doc, Geom:new{ x = 0, y = 0, w = width, h = height })
    end
    if resized then
        -- Drop the engine's cached page buffer if it has the old size.
        local buffer = doc.buffer
        if buffer then
            pcall(function()
                if buffer:getWidth() ~= width or buffer:getHeight() ~= height then
                    buffer:free()
                    doc.buffer = nil
                end
            end)
        end
        record.viewport_w, record.viewport_h = width, height
        self:refreshReflowableAfterConfig(index, xpointer)
        return
    end

    appendDebugLog(self, "reflow_viewport_reopen", string.format("panel=%d %dx%d", index, width, height))
    local configurable, path = record.configurable, record.path
    saveSessionRecords(session, index)
    closeDocumentRecord(record)
    session.records[index] = nil
    self:loadDocumentIntoSlot(index, path, {
        xpointer = xpointer, configurable = configurable, silent = true,
    })
end

function ParallelReader:getPanelAtPosition(session, pos)
    if not pos or type(pos.x) ~= "number" or type(pos.y) ~= "number" then
        return session.active_panel or 1
    end
    local first, second, side_by_side = sessionRects(session)
    local function inside(rect)
        return pos.x >= rect.x and pos.x <= rect.x + rect.w
            and pos.y >= rect.y and pos.y <= rect.y + rect.h
    end
    if inside(second) then return 2 end
    if inside(first) then return 1 end
    -- A tap on the divider selects the nearest panel.
    if not side_by_side then
        local d1 = math.abs(pos.y - (first.y + first.h / 2))
        local d2 = math.abs(pos.y - (second.y + second.h / 2))
        return d1 <= d2 and 1 or 2
    end
    local d1 = math.abs(pos.x - (first.x + first.w / 2))
    local d2 = math.abs(pos.x - (second.x + second.w / 2))
    return d1 <= d2 and 1 or 2
end

function ParallelReader:isNearDivider(session, x, y)
    local first, _second, side_by_side = sessionRects(session)
    local tolerance = Screen:scaleBySize(36)
    if side_by_side then
        return math.abs(x - (first.w + DIVIDER_SIZE / 2)) <= tolerance
    end
    return math.abs(y - (first.h + DIVIDER_SIZE / 2)) <= tolerance
end

function ParallelReader:ratioFromPosition(session, pos)
    local _first, _second, side_by_side = sessionRects(session)
    local ratio
    if side_by_side then
        ratio = pos.x / (session.screen_w or Screen:getWidth())
    else
        ratio = pos.y / (session.screen_h or Screen:getHeight())
    end
    return math.max(MIN_SPLIT, math.min(MAX_SPLIT, ratio))
end

------------------------------------------------------------------------
-- Gestures
------------------------------------------------------------------------

function ParallelReader:handlePanelTouch(session, pos)
    -- A stale drag (its release event never arrived) is applied first.
    if session.drag then self:finishDrag(session, nil) end
    session.zoom_pan_drag = nil
    if not pos or type(pos.x) ~= "number" or type(pos.y) ~= "number" then
        self:showReaderMenu(session)
        return
    end
    local index = self:getPanelAtPosition(session, pos)
    local previous_active = session.active_panel
    session.active_panel = index
    local panel, content = getPanelLayout(session, index)
    local record = session.records[index]
    local inside_panel = pos.x >= panel.x and pos.x <= panel.x + panel.w
        and pos.y >= panel.y and pos.y <= panel.y + panel.h

    if inside_panel and panel.w > 0 and panel.h > 0 then
        if not record or not record.doc then
            self:chooseDocument(index)
            return
        end
        -- A tap dismisses an active selection, like the stock reader.
        if record.selection then
            self:clearTextSelection(index)
            return
        end
        -- A tap on a highlight opens its menu.
        if record.kind == "reflowable" then
            local hit = self:findHighlightAt(session, index, pos, content)
            if hit then
                self:showHighlightMenu(index, hit)
                return
            end
        end
        local relative_x = (pos.x - panel.x) / panel.w
        local relative_y = (pos.y - panel.y) / panel.h
        if relative_y >= 0.84 and relative_x >= 0.25 and relative_x <= 0.75 then
            self:showBottomMenu(index)
            return
        end
        if relative_x <= 0.25 then
            self:changePage(index, -1)
            return
        elseif relative_x >= 0.75 then
            self:changePage(index, 1)
            return
        end
    end
    if previous_active ~= index then self:refreshWindow("ui") end
    self:showReaderMenu(session)
end

function ParallelReader:handleSwipe(session, ges)
    local pos = ges and ges.pos
    local direction = ges and ges.direction
    if not pos or not direction then return false end

    -- A fast divider drag can end as a swipe instead of a pan release.
    if session.drag and self:finishDrag(session, nil) then
        session.zoom_pan_drag = nil
        return true
    end

    local screen_h = session.screen_h or Screen:getHeight()
    if direction == "south" and pos.y <= screen_h * MENU_SWIPE_ZONE then
        session.zoom_pan_drag = nil
        self:showReaderMenu(session)
        return true
    end

    -- A zoom-pan gesture must not also turn the page when KOReader classifies
    -- its release as a swipe. The top-edge menu gesture above keeps priority.
    if session.zoom_pan_drag then
        session.zoom_pan_drag = nil
        return true
    end

    local index = self:getPanelAtPosition(session, pos)
    local record = session.records[index]
    if not record or not record.doc then return false end
    session.active_panel = index

    local delta
    if record.kind == "reflowable" and isScrollMode(record.doc) then
        if direction == "north" then delta = 1 elseif direction == "south" then delta = -1 end
    end
    if not delta then
        if direction == "west" then delta = 1 elseif direction == "east" then delta = -1 end
    end
    if not delta then return false end
    self:changePage(index, delta)
    return true
end

-- Applies a divider drag. pos = release position (nil: use the last dragged ratio).
function ParallelReader:finishDrag(session, pos)
    local drag = session.drag
    local ratio = session.drag_ratio
    session.drag = nil
    session.drag_ratio = nil
    if not (drag and drag.active) then return false end
    if pos and type(pos.x) == "number" and type(pos.y) == "number" then
        ratio = self:ratioFromPosition(session, pos)
    end
    if ratio then
        self:setSplitRatio(ratio)
    else
        self:refreshWindow("full")
    end
    return true
end

-- Panning is available only when a fixed-layout page is magnified. Divider
-- dragging remains higher priority and keeps its original behavior.
function ParallelReader:handleZoomPan(session, pos, start_x, start_y)
    local pan = session.zoom_pan_drag
    if pan and (math.abs(pan.sx - start_x) > 10 or math.abs(pan.sy - start_y) > 10) then
        pan = nil
        session.zoom_pan_drag = nil
    end

    if not pan then
        local index = self:getPanelAtPosition(session, { x = start_x, y = start_y })
        local record = session.records[index]
        if not record or not record.doc or record.kind ~= "paged"
                or (tonumber(record.zoom_factor) or MIN_PAGE_ZOOM) <= MIN_PAGE_ZOOM then
            return false
        end
        local _panel, content = getPanelLayout(session, index)
        local viewport = getPagedViewport(record, content)
        if not viewport or (viewport.max_x <= 0 and viewport.max_y <= 0) then return false end
        pan = {
            sx = start_x,
            sy = start_y,
            index = index,
            pan_x = clamp(record.zoom_pan_x, 0, 1, 0.5),
            pan_y = clamp(record.zoom_pan_y, 0, 1, 0.5),
        }
        session.zoom_pan_drag = pan
    end

    local index = pan.index
    local record = session.records[index]
    if not record or not record.doc or record.kind ~= "paged" then
        session.zoom_pan_drag = nil
        return false
    end
    local _panel, content = getPanelLayout(session, index)
    local viewport = getPagedViewport(record, content)
    if not viewport then return false end

    local delta_x = pos.x - pan.sx
    local delta_y = pos.y - pan.sy
    if viewport.max_x > 0 then
        record.zoom_pan_x = clamp(pan.pan_x - delta_x / viewport.max_x, 0, 1, 0.5)
    end
    if viewport.max_y > 0 then
        record.zoom_pan_y = clamp(pan.pan_y - delta_y / viewport.max_y, 0, 1, 0.5)
    end
    self:refreshPanelRegion(index, "partial")
    return true
end

-- Dragging the divider (always active) resizes the panels; the new size is
-- applied as soon as the finger is released. Away from the divider, a zoomed
-- fixed-layout page can be dragged to inspect its clipped areas.
function ParallelReader:handlePan(session, ges)
    local pos = ges and ges.pos
    if not pos or type(pos.x) ~= "number" or type(pos.y) ~= "number" then return false end

    local drag = session.drag
    local relative = ges.relative
    local start_x, start_y = pos.x, pos.y
    if relative and type(relative.x) == "number" and type(relative.y) == "number" then
        start_x, start_y = pos.x - relative.x, pos.y - relative.y
        if drag and (math.abs(drag.sx - start_x) > 10 or math.abs(drag.sy - start_y) > 10) then
            -- A new gesture started and the release of the previous one was lost.
            self:finishDrag(session, nil)
            session.zoom_pan_drag = nil
            drag = nil
        end
    elseif drag then
        start_x, start_y = drag.sx, drag.sy
    end

    if not drag then
        drag = { sx = start_x, sy = start_y, active = self:isNearDivider(session, start_x, start_y) }
        session.drag = drag
    end
    if not drag.active then
        return self:handleZoomPan(session, pos, start_x, start_y)
    end

    local previous = session.drag_ratio or session.split_ratio
    session.drag_ratio = self:ratioFromPosition(session, pos)
    self:refreshWindow("ui", unionRegion(getDividerBand(session, previous),
        getDividerBand(session, session.drag_ratio)))
    return true
end

function ParallelReader:handlePanRelease(session, ges)
    local divider_handled = self:finishDrag(session, ges and ges.pos)
    if divider_handled then
        session.zoom_pan_drag = nil
        return true
    end
    if session.zoom_pan_drag then
        session.zoom_pan_drag = nil
        return true
    end
    return false
end

------------------------------------------------------------------------
-- Text selection, highlights and notes
------------------------------------------------------------------------

function ParallelReader:clearTextSelection(index)
    local record = self.session and self.session.records[index]
    if not record then return end
    self:dropSelection(record)
    self:refreshPanelRegion(index, "ui")
end

function ParallelReader:onTextHold(session, ges)
    local pos = ges and ges.pos
    local index = self:getPanelAtPosition(session, pos)
    session.active_panel = index
    local record = session.records[index]
    if not record or not record.doc or record.kind ~= "reflowable" then
        -- Fixed-layout text extraction is backend-specific; offer the panel actions.
        self:showPanelContextMenu(session, index)
        return true
    end

    local local_pos = getLocalDocumentPosition(session, index, pos)
    if not local_pos then return false end

    local doc = record.doc
    self:dropSelection(record)
    syncDocView(record)
    local ok, word = pcall(doc.getWordFromPosition, doc, local_pos)
    if not ok or type(word) ~= "table" or not word.pos0 or not word.pos1
            or type(word.word) ~= "string" or word.word == "" then
        self:refreshPanelRegion(index, "ui")
        return false
    end

    record.hold_start_pos = local_pos
    record.hold_active = true
    record.selection = {
        text = word.word,
        pos0 = word.pos0,
        pos1 = word.pos1,
        sboxes = word.sbox and { word.sbox } or nil,
        pboxes = word.pbox and { word.pbox } or nil,
        is_word_selection = true,
    }
    self:refreshPanelRegion(index, "ui")
    return true
end

function ParallelReader:onTextHoldPan(session, ges)
    local index = session.active_panel or 1
    local record = session.records[index]
    if not record or record.kind ~= "reflowable" or not record.doc
            or not record.hold_active or not record.hold_start_pos then
        return false
    end
    local local_pos = getLocalDocumentPosition(session, index, ges and ges.pos)
    if not local_pos then return true end

    local ok, selection = pcall(record.doc.getTextFromPositions, record.doc,
        record.hold_start_pos, local_pos)
    if ok and type(selection) == "table" and selection.pos0 and selection.pos1
            and type(selection.text) == "string" then
        selection.is_word_selection = false
        record.selection = selection
        self:refreshPanelRegion(index, "ui")
    end
    return true
end

function ParallelReader:onTextHoldRelease(session)
    local index = session.active_panel or 1
    local record = session.records[index]
    if not record or not record.hold_active then return false end
    record.hold_active = nil
    local selection = record.selection
    if selection and selection.pos0 and selection.pos1
            and util.cleanupSelectedText(selection.text or "") ~= "" then
        if selection.is_word_selection and getPrefs().dict_on_hold ~= false then
            -- Like the stock reader: holding a single word opens the dictionary.
            if self:lookupSelectedText(index) then return true end
        end
        self:refreshPanelRegion(index, "ui")
        self:showSelectionMenu(session, index)
    else
        self:clearTextSelection(index)
    end
    return true
end

local function truncateText(text, limit)
    text = tostring(text or "")
    local chars = util.splitToChars(text)
    if #chars <= limit then return text end
    return table.concat(chars, "", 1, limit) .. "..."
end

local function sortAnnotations(record)
    local doc = record.doc
    if type(doc.compareXPointers) == "function" then
        table.sort(record.annotations, function(a, b)
            local ok, order = pcall(doc.compareXPointers, doc, a.pos0, b.pos0)
            return ok and order == 1
        end)
    end
end

function ParallelReader:saveSelectedAnnotation(index, note)
    local record = self.session and self.session.records[index]
    local selection = record and record.selection
    if not record or record.kind ~= "reflowable" or not record.doc_settings
            or not selection or not selection.pos0 or not selection.pos1 then
        showInfo(_("There is no valid text selection to save."), 4)
        return false
    end

    local doc = record.doc
    local clean_text = util.cleanupSelectedText(selection.text or "")
    if clean_text == "" then return false end
    if note == "" then note = nil end

    local item = {
        datetime = os.date("%Y-%m-%d %H:%M:%S"),
        drawer = G_reader_settings:readSetting("highlight_drawing_style") or "lighten",
        color = G_reader_settings:readSetting("highlight_color") or "yellow",
        text = clean_text,
        note = note,
        page = selection.pos0,
        pos0 = selection.pos0,
        pos1 = selection.pos1,
    }
    if type(doc.getEPubCFIRangeFromXPointers) == "function" then
        local cfi = try(doc.getEPubCFIRangeFromXPointers, doc, selection.pos0, selection.pos1)
        if cfi then item.epubcfi = cfi end
    end

    record.annotations = record.annotations or {}
    -- Avoid duplicates when a touch is accidentally repeated.
    local replaced, previous_note, previous_datetime
    for i = 1, #record.annotations do
        local existing = record.annotations[i]
        if existing.pos0 == item.pos0 and existing.pos1 == item.pos1 then
            if note then
                replaced, previous_note, previous_datetime = existing, existing.note, existing.datetime
                existing.note = note
                existing.datetime = item.datetime
                item = existing
            else
                self:closeTouchMenu(self.session)
                self:clearTextSelection(index)
                showInfo(_("This passage is already highlighted."), 3)
                return true
            end
            break
        end
    end
    if not replaced then table.insert(record.annotations, item) end
    sortAnnotations(record)

    local saved, save_error = self:commitAnnotations(record)
    if not saved then
        -- Roll back by identity: sorting may have moved the new item.
        if replaced then
            replaced.note, replaced.datetime = previous_note, previous_datetime
        else
            for i = 1, #record.annotations do
                if record.annotations[i] == item then
                    table.remove(record.annotations, i)
                    break
                end
            end
        end
        self:commitAnnotations(record)
        showInfo(_("The annotation could not be written to the book's KOReader metadata:")
            .. "\n\n" .. tostring(save_error), 10)
        return false
    end

    self:closeTouchMenu(self.session)
    self:clearTextSelection(index)
    return true
end

function ParallelReader:showNoteDialog(title, initial, on_save)
    local InputDialog = require("ui/widget/inputdialog")
    local dialog
    dialog = InputDialog:new{
        title = title,
        input = initial or "",
        allow_newline = true,
        fullscreen = true,
        buttons = {
            {
                {
                    text = _("Cancel"),
                    id = "close",
                    callback = function() UIManager:close(dialog) end,
                },
                {
                    text = _("Save note"),
                    is_enter_default = false,
                    callback = function()
                        if on_save(dialog:getInputText()) ~= false then UIManager:close(dialog) end
                    end,
                },
            },
        },
    }
    UIManager:show(dialog)
    dialog:onShowKeyboard()
end

function ParallelReader:addNoteToSelection(index)
    local record = self.session and self.session.records[index]
    if not (record and record.selection) then return end
    self:closeTouchMenu(self.session)
    self:showNoteDialog(_("Add note"), "", function(note)
        return self:saveSelectedAnnotation(index, note)
    end)
end

-- Opens the dictionary for the current selection. Returns true when it opened.
function ParallelReader:lookupSelectedText(index)
    local record = self.session and self.session.records[index]
    local selection = record and record.selection
    if not selection then return false end
    local text = util.cleanupSelectedText(selection.text or "")
    if text == "" then return false end

    local ok, err = pcall(function()
        -- The file manager owns a fully working dictionary module (the same one
        -- behind its "Dictionary lookup" menu entry); it needs no ReaderUI.
        local dictionary = self.ui and self.ui.dictionary
        if dictionary and type(dictionary.onLookupWord) == "function" then
            dictionary:onLookupWord(text, false, nil)
            return
        end
        -- Fallback: build a dictionary module around a minimal adapter.
        if not record.dictionary then
            local ReaderDictionary = require("apps/reader/modules/readerdictionary")
            record.dictionary = ReaderDictionary:new{
                dialog = self.window,
                document = record.doc,
                ui = {
                    document = record.doc,
                    doc_settings = record.doc_settings,
                    menu = { registerToMainMenu = function() end },
                },
            }
        end
        record.dictionary:onLookupWord(text, false, nil)
    end)
    if not ok then
        appendDebugLog(self, "dictionary_lookup_error", err)
        showInfo(_("Dictionary lookup could not be opened:") .. "\n\n" .. tostring(err), 8)
        return false
    end
    -- Like the stock reader, the word is no longer marked once the lookup opens.
    self:dropSelection(record)
    self:refreshPanelRegion(index, "ui")
    return true
end

function ParallelReader:showSelectionMenu(session, index)
    local record = session.records[index]
    local selection = record and record.selection
    if not selection then return end
    local selected_text = util.cleanupSelectedText(selection.text or "")
    local function action(text, callback, extra)
        local item = { text = text, callback = callback }
        if extra then for key, value in pairs(extra) do item[key] = value end end
        return item
    end
    local items = {
        {
            icon = "appbar.highlight",
            action(_("Highlight"), function()
                self:saveSelectedAnnotation(index, nil)
            end),
            action(_("Add note"), function()
                UIManager:nextTick(function() self:addNoteToSelection(index) end)
            end),
        },
        {
            icon = "appbar.search",
            action(_("Dictionary"), function()
                self:closeTouchMenu(session)
                UIManager:nextTick(function() self:lookupSelectedText(index) end)
            end),
        },
        {
            icon = "appbar.copy",
            action(_("Copy"), function()
                local copied = Device.input
                    and type(Device.input.setClipboardText) == "function"
                    and pcall(Device.input.setClipboardText, selected_text)
                self:closeTouchMenu(session)
                if copied then
                    showInfo(_("Selection copied to clipboard."), 3)
                else
                    showInfo(_("Clipboard is not available on this device."), 4)
                end
                self:clearTextSelection(index)
            end, { enabled_func = function() return Device:hasClipboard() end }),
            action(_("Clear selection"), function()
                self:closeTouchMenu(session)
                self:clearTextSelection(index)
            end),
        },
    }
    self:openTouchMenu(session, items, 1)
end

-- Returns the annotation whose highlight contains the screen position.
function ParallelReader:findHighlightAt(session, index, pos, content)
    local record = session.records[index]
    if not record or not record.doc or not record.annotations or #record.annotations == 0 then
        return nil
    end
    syncDocView(record)
    local items = getHighlightItems(record, content.h)
    if not items then return nil end
    local lx, ly = pos.x - content.x, pos.y - content.y
    for i = 1, #items do
        for j = 1, #items[i].rects do
            local r = items[i].rects[j]
            if lx >= r.x and lx <= r.x + r.w and ly >= r.y and ly <= r.y + r.h then
                return items[i].ann
            end
        end
    end
    return nil
end

function ParallelReader:deleteAnnotation(index, ann)
    local record = self.session and self.session.records[index]
    if not record or not record.annotations then return end
    for i = 1, #record.annotations do
        if record.annotations[i] == ann then
            table.remove(record.annotations, i)
            break
        end
    end
    local saved, err = self:commitAnnotations(record)
    if not saved then
        showInfo(_("The annotation could not be written to the book's KOReader metadata:")
            .. "\n\n" .. tostring(err), 10)
    end
    self:refreshPanelRegion(index, "partial")
end

function ParallelReader:showHighlightMenu(index, ann)
    local ButtonDialog = require("ui/widget/buttondialog")
    local ConfirmBox = require("ui/widget/confirmbox")
    local preview = (ann.note and ann.note ~= "") and ann.note or ann.text or ""
    local dialog
    dialog = ButtonDialog:new{
        title = truncateText(preview, 220),
        buttons = {
            {
                {
                    text = (ann.note and ann.note ~= "") and _("Edit note") or _("Add note"),
                    callback = function()
                        UIManager:close(dialog)
                        UIManager:nextTick(function()
                            self:showNoteDialog(_("Note"), ann.note or "", function(note)
                                local record = self.session and self.session.records[index]
                                if not record then return false end
                                ann.note = note ~= "" and note or nil
                                ann.datetime_updated = os.date("%Y-%m-%d %H:%M:%S")
                                local saved, err = self:commitAnnotations(record)
                                if not saved then
                                    showInfo(tostring(err), 8)
                                    return false
                                end
                                self:refreshPanelRegion(index, "partial")
                                return true
                            end)
                        end)
                    end,
                },
                {
                    text = _("Delete highlight"),
                    callback = function()
                        UIManager:close(dialog)
                        UIManager:show(ConfirmBox:new{
                            text = _("Delete this highlight?"),
                            ok_text = _("Delete"),
                            ok_callback = function() self:deleteAnnotation(index, ann) end,
                        })
                    end,
                },
            },
            {
                {
                    text = _("Close"),
                    callback = function() UIManager:close(dialog) end,
                },
            },
        },
    }
    UIManager:show(dialog)
end

function ParallelReader:showAnnotationList(index)
    local record = self.session and self.session.records[index]
    if not record or record.kind ~= "reflowable" or not record.doc then
        showInfo(_("Highlights are available for reflowable documents (EPUB, FB2, TXT…)."), 5)
        return
    end
    local annotations = record.annotations
    if not annotations or #annotations == 0 then
        showInfo(_("This document has no highlights or notes yet."), 4)
        return
    end
    local Menu = require("ui/widget/menu")
    local ConfirmBox = require("ui/widget/confirmbox")
    local CenterContainer = require("ui/widget/container/centercontainer")
    local menu_container = CenterContainer:new{ dimen = Screen:getSize(), covers_fullscreen = true }
    local items = {}
    for i = 1, #annotations do
        local ann = annotations[i]
        local label = truncateText(ann.text or "", 90)
        if ann.note and ann.note ~= "" then label = label .. "  [" .. truncateText(ann.note, 40) .. "]" end
        local page = try(record.doc.getPageFromXPointer, record.doc, ann.pos0)
        table.insert(items, {
            text = label,
            mandatory = page and tostring(page) or nil,
            callback = function()
                UIManager:close(menu_container)
                if not self:gotoXPointer(index, ann.pos0) then
                    showInfo(_("Could not jump to this highlight."), 4)
                end
            end,
            ann = ann,
        })
    end
    local list = Menu:new{
        title = _("Highlights and notes"),
        subtitle = getBaseName(record.path),
        item_table = items,
        is_borderless = true,
        is_popout = false,
        title_bar_fm_style = true,
        show_parent = menu_container,
        close_callback = function() UIManager:close(menu_container) end,
        onMenuHold = function(_menu, item)
            UIManager:show(ConfirmBox:new{
                text = _("Delete this highlight?"),
                ok_text = _("Delete"),
                ok_callback = function()
                    UIManager:close(menu_container)
                    self:deleteAnnotation(index, item.ann)
                end,
            })
            return true
        end,
    }
    menu_container[1] = list
    UIManager:show(menu_container)
end

------------------------------------------------------------------------
-- Touch menu (same TouchMenu widget as the stock reader menu)
------------------------------------------------------------------------

function ParallelReader:closeTouchMenu(session)
    if not session or not session.menu_container then return end
    local container = session.menu_container
    session.menu_container = nil
    session.reader_menu = nil
    pcall(UIManager.close, UIManager, container)
end

function ParallelReader:openTouchMenu(session, tab_item_table, last_index)
    local CenterContainer = require("ui/widget/container/centercontainer")
    local TouchMenu = require("ui/widget/touchmenu")

    self:closeTouchMenu(session)

    local menu_container = CenterContainer:new{
        covers_header = true,
        ignore = "height",
        dimen = Screen:getSize(),
    }
    local touch_menu
    touch_menu = TouchMenu:new{
        width = Screen:getWidth(),
        last_index = last_index or 1,
        tab_item_table = tab_item_table,
        show_parent = menu_container,
        close_callback = function()
            if session.reader_menu == touch_menu then
                session.menu_tab_index = touch_menu.last_index
                session.reader_menu = nil
                session.menu_container = nil
                UIManager:close(menu_container)
            end
        end,
    }
    menu_container[1] = touch_menu
    session.menu_container = menu_container
    session.reader_menu = touch_menu
    UIManager:show(menu_container)
    return touch_menu
end

function ParallelReader:showGoToPageDialog(index)
    local record = self.session and self.session.records[index]
    if not record or not record.doc then
        showInfo(_("This panel has no document loaded."), 3)
        return
    end
    local InputDialog = require("ui/widget/inputdialog")
    local page_count = record.page_count or getPageCount(record.doc)
    if record.kind == "reflowable" then page_count = getReflowablePageCount(record.doc) end
    local dialog
    dialog = InputDialog:new{
        title = _("Go to page"),
        input = tostring(tonumber(record.page) or 1),
        input_hint = string.format("1 - %d", math.max(1, page_count)),
        input_type = "number",
        buttons = {
            {
                {
                    text = _("Cancel"),
                    id = "close",
                    callback = function() UIManager:close(dialog) end,
                },
                {
                    text = _("Go to page"),
                    is_enter_default = true,
                    callback = function()
                        local value = tonumber(dialog:getInputText())
                        if value then
                            if self:gotoPage(index, math.floor(value + 0.5)) then
                                UIManager:close(dialog)
                            end
                        else
                            showInfo(_("Please enter a valid page number."), 4)
                        end
                    end,
                },
            },
        },
    }
    UIManager:show(dialog)
    dialog:onShowKeyboard()
end

function ParallelReader:showTableOfContents(index)
    local record = self.session and self.session.records[index]
    if not record or not record.doc then
        showInfo(_("This panel has no document loaded."), 3)
        return
    end
    if type(record.doc.getToc) ~= "function" then
        showInfo(_("This document does not provide a table of contents."), 5)
        return
    end
    local ok, toc = pcall(record.doc.getToc, record.doc)
    if not ok or type(toc) ~= "table" or #toc == 0 then
        showInfo(_("No table of contents is available for this document."), 5)
        return
    end

    local Menu = require("ui/widget/menu")
    local CenterContainer = require("ui/widget/container/centercontainer")
    local menu_container = CenterContainer:new{ dimen = Screen:getSize(), covers_fullscreen = true }
    local items = {}
    for i = 1, #toc do
        local entry = toc[i]
        local page = tonumber(entry.page)
        if page and page >= 1 then
            local title = entry.title or entry.text or _("Untitled chapter")
            local depth = math.max(1, math.floor(tonumber(entry.depth) or 1))
            local xpointer = entry.xpointer
            table.insert(items, {
                text = string.rep("  ", math.min(depth - 1, 8)) .. tostring(title),
                mandatory = tostring(page),
                callback = function()
                    UIManager:close(menu_container)
                    if not (xpointer and record.kind == "reflowable"
                            and self:gotoXPointer(index, xpointer)) then
                        self:gotoPage(index, page)
                    end
                end,
            })
        end
    end
    if #items == 0 then
        showInfo(_("The table of contents has no usable page entries."), 5)
        return
    end

    menu_container[1] = Menu:new{
        title = _("Table of contents"),
        subtitle = getBaseName(record.path),
        item_table = items,
        is_borderless = true,
        is_popout = false,
        title_bar_fm_style = true,
        show_parent = menu_container,
        close_callback = function() UIManager:close(menu_container) end,
    }
    UIManager:show(menu_container)
end

------------------------------------------------------------------------
-- Layout actions
------------------------------------------------------------------------

function ParallelReader:swapDocuments()
    local records = self.session.records
    records[1], records[2] = records[2], records[1]
    self.session.active_panel = 3 - (self.session.active_panel or 1)
    self:refreshWindow("full")
    self:scheduleViewportRefresh()
end

function ParallelReader:setSplitRatio(ratio)
    local session = self.session
    session.split_ratio = math.max(MIN_SPLIT, math.min(MAX_SPLIT, ratio))
    setPref("split_ratio", session.split_ratio)
    self:refreshWindow("full")
    self:scheduleViewportRefresh()
end

function ParallelReader:resizeActivePanel(make_larger)
    local session = self.session
    local delta = make_larger and SPLIT_STEP or -SPLIT_STEP
    if (session.active_panel or 1) == 2 then delta = -delta end
    self:setSplitRatio(session.split_ratio + delta)
end

function ParallelReader:setSplitMode(mode)
    self.session.split_mode = mode
    setPref("split_mode", mode)
    self:refreshWindow("full")
    self:scheduleViewportRefresh()
end

function ParallelReader:setFooterVisible(visible)
    self.session.show_footer = visible
    setPref("show_footer", visible)
    self:refreshWindow("full")
    self:scheduleViewportRefresh()
end

-- Shows/hides crengine's book title header at the top of every reflowable panel.
function ParallelReader:setHeaderVisible(visible)
    local session = self.session
    session.show_header = visible
    setPref("show_header", visible)
    for index = 1, 2 do
        local record = session.records[index]
        if record and record.kind == "reflowable" and record.doc then
            local xpointer = getDocumentXPointer(record.doc)
            self:dropSelection(record)
            local ok, err = pcall(applyHeaderSetting, record.doc, visible)
            if ok then
                self:refreshReflowableAfterConfig(index, xpointer)
            else
                appendDebugLog(self, "header_setting_error", err)
            end
        end
    end
    self:refreshWindow("full")
end

-- Saves the annotations and refreshes every panel showing the same book.
function ParallelReader:commitAnnotations(record)
    local ok, err = persistAnnotations(record)
    local session = self.session
    if session then
        for index = 1, 2 do
            local other = session.records[index]
            if other and other ~= record and other.annotations == record.annotations then
                other.ann_gen = (other.ann_gen or 0) + 1
                other.hl_cache = nil
                self:refreshPanelRegion(index, "partial")
            end
        end
    end
    return ok, err
end

function ParallelReader:refreshReflowableAfterConfig(index, xpointer)
    local record = self.session and self.session.records[index]
    local doc = record and record.doc
    if not record or record.kind ~= "reflowable" or not doc then return end

    -- getCurrentPos() asks crengine to complete any pending reflow. This mirrors
    -- ReaderRolling:onUpdatePos() without constructing a second ReaderUI.
    local ok, err = pcall(function()
        if type(doc.getCurrentPos) == "function" then doc:getCurrentPos() end
        if type(doc.resetCallCache) == "function" then doc:resetCallCache() end
        if type(doc._readMetadata) == "function" then doc:_readMetadata() end
        if xpointer and type(doc.gotoXPointer) == "function" then doc:gotoXPointer(xpointer) end
    end)
    if not ok then
        appendDebugLog(self, "reflow_refresh_error", err)
        showInfo(_("The setting was applied, but the page layout could not be refreshed:")
            .. "\n\n" .. tostring(err), 12)
    end

    record.layout_gen = (record.layout_gen or 0) + 1
    record.hl_cache = nil
    record.page_count = getReflowablePageCount(doc)
    local page = try(doc.getCurrentPage, doc)
    if type(page) == "number" then
        record.page = math.max(1, math.min(record.page_count > 0 and record.page_count or page, page))
    end
    record.position = getReflowablePosition(doc)
    self:refreshPanelRegion(index, "partial")
end

function ParallelReader:scheduleReflowableConfigRefresh(index, xpointer, when_applied_callback)
    self._config_refresh_pending = self._config_refresh_pending or {}
    local pending = self._config_refresh_pending[index]
    if pending then
        if pending.xpointer == nil then pending.xpointer = xpointer end
        if type(when_applied_callback) == "function" then
            table.insert(pending.callbacks, when_applied_callback)
        end
        return
    end
    pending = { xpointer = xpointer, record = self.session.records[index], callbacks = {} }
    if type(when_applied_callback) == "function" then
        table.insert(pending.callbacks, when_applied_callback)
    end
    self._config_refresh_pending[index] = pending
    UIManager:nextTick(function()
        if self._config_refresh_pending then self._config_refresh_pending[index] = nil end
        if self.session and self.session.records[index] == pending.record then
            self:refreshReflowableAfterConfig(index, pending.xpointer)
        end
        -- ConfigDialog uses this callback to reveal itself again after
        -- settings marked hide_on_apply have finished applying.
        for _i, callback in ipairs(pending.callbacks) do
            local callback_ok, callback_err = pcall(callback)
            if not callback_ok then appendDebugLog(self, "config_callback_error", callback_err) end
        end
    end)
end

------------------------------------------------------------------------
-- Bottom config dialog (native ConfigDialog bound to one panel)
------------------------------------------------------------------------

-- name = configurable key, normalize(value) -> stored value,
-- apply(doc, stored) -> native call, reflow = needs a re-layout.
local SETTING_HANDLERS = {
    onSetFontSize = { "font_size",
        function(v) return clamp(v, 12, 255, 22) end,
        function(doc, v) doc:setFontSize(Screen:scaleBySize(v)) end, true },
    onSetLineSpace = { "line_spacing",
        function(v) return clamp(v, 50, 200, 100) end,
        function(doc, v) doc:setInterlineSpacePercent(v) end, true },
    onSetViewMode = { "view_mode",
        function(mode) return mode == "scroll" and 1 or 0 end,
        function(doc, v) doc:setViewMode(v == 1 and "scroll" or "page") end, true },
    onSetBlockRenderingMode = { "block_rendering_mode",
        function(v) return clamp(v, 0, #BLOCK_RENDERING_FLAGS - 1, 2) end,
        function(doc, v) doc:setBlockRenderingFlags(BLOCK_RENDERING_FLAGS[v + 1]) end, true },
    onSetRenderDPI = { "render_dpi",
        function(v) return clamp(v, 0, 1200, 96) end,
        function(doc, v) doc:setRenderDPI(v) end, true },
    onToggleEmbeddedFonts = { "embedded_fonts",
        function(enabled) return enabled and 1 or 0 end,
        function(doc, v) doc:setEmbeddedFonts(v) end, true },
    onToggleImageScaling = { "smooth_scaling",
        function(enabled) return enabled and 1 or 0 end,
        function(doc, v) doc:setImageScaling(v == 1) end, true },
    onToggleNightmodeImages = { "nightmode_images",
        function(enabled) return enabled and 1 or 0 end,
        function(doc, v) doc:setNightmodeImages(v == 1) end, false },
    onSetFontBaseWeight = { "font_base_weight",
        function(v) return v end,
        function(doc, v) doc:setFontBaseWeight(v) end, true },
    onSetFontHinting = { "font_hinting",
        function(v) return v end,
        function(doc, v) doc:setFontHinting(v) end, true },
    onSetFontKerning = { "font_kerning",
        function(v) return v end,
        function(doc, v) doc:setFontKerning(v) end, true },
    onSetWordSpacing = { "word_spacing",
        function(v) return copyConfigValue(v) end,
        function(doc, v) doc:setWordSpacing(v) end, true },
    onSetWordExpansion = { "word_expansion",
        function(v) return v end,
        function(doc, v) doc:setWordExpansion(v) end, true },
    onSetCJKWidthScaling = { "cjk_width_scaling",
        function(v) return v end,
        function(doc, v) doc:setCJKWidthScaling(v) end, true },
}

local function makePanelConfigAdapter(plugin, index, record)
    local adapter = {
        document = record.doc,
        configurable = record.configurable,
        plugin = plugin,
        panel_index = index,
    }

    local function applyDocumentChange(self, name, value, setter, needs_reflow)
        local xpointer = getDocumentXPointer(self.document)
        self.configurable[name] = copyConfigValue(value)
        savePanelConfig(record)
        local ok, err = pcall(setter, self.document, value)
        if not ok then
            appendDebugLog(self.plugin, "config_setting_error", err)
            showInfo(_("Could not apply this reading setting:") .. "\n\n" .. tostring(err), 10)
            return true
        end
        if needs_reflow then
            self.plugin:scheduleReflowableConfigRefresh(self.panel_index, xpointer)
        else
            self.plugin:refreshPanelRegion(self.panel_index, "partial")
        end
        return true
    end

    for event_name, spec in pairs(SETTING_HANDLERS) do
        local name, normalize, apply, reflow = spec[1], spec[2], spec[3], spec[4]
        adapter[event_name] = function(self, value)
            return applyDocumentChange(self, name, normalize(value), apply, reflow)
        end
    end

    function adapter:handleEvent(event)
        if not event or type(event.handler) ~= "string" then return end
        local handler = self[event.handler]
        if type(handler) ~= "function" then
            appendDebugLog(self.plugin, "config_unhandled_event", event.handler)
            return
        end
        local args = event.args or {}
        local unpack_values = unpack or table.unpack
        return handler(self, unpack_values(args, 1, args.n or #args))
    end

    function adapter:onConfigChange(name, value)
        self.configurable[name] = copyConfigValue(value)
        savePanelConfig(record)
        return true
    end

    function adapter:onChangeSize(delta)
        local size = tonumber(self.configurable.font_size) or 22
        return self:onSetFontSize(size + (tonumber(delta) or 0))
    end

    function adapter:onSetFontGamma(value)
        -- CRe gamma may be shared by the engine: apply it to every open view.
        value = tonumber(value) or value
        local session = self.plugin.session
        session.shared_font_gamma = copyConfigValue(value)
        for panel_index = 1, 2 do
            local panel_record = session.records[panel_index]
            if panel_record and panel_record.kind == "reflowable" and panel_record.doc then
                panel_record.configurable = panel_record.configurable or {}
                panel_record.configurable.font_gamma = copyConfigValue(value)
                savePanelConfig(panel_record)
                local ok, err = pcall(panel_record.doc.setGammaIndex, panel_record.doc, value)
                if not ok then
                    appendDebugLog(self.plugin, "shared_font_gamma_error", err)
                    showInfo(_("Could not apply the shared font gamma setting:")
                        .. "\n\n" .. tostring(err), 10)
                end
            end
        end
        self.plugin:refreshWindow("partial")
        return true
    end

    function adapter:applyMargins(when_applied_callback)
        local xpointer = getDocumentXPointer(self.document)
        savePanelConfig(record)
        local ok, err = pcall(applyPanelMargins, self.document, self.configurable)
        if not ok then
            appendDebugLog(self.plugin, "config_margin_error", err)
            showInfo(_("Could not apply the page margins:") .. "\n\n" .. tostring(err), 10)
            if type(when_applied_callback) == "function" then pcall(when_applied_callback) end
            return true
        end
        self.plugin:scheduleReflowableConfigRefresh(self.panel_index, xpointer, when_applied_callback)
        return true
    end

    local function synced(c)
        return c.sync_t_b_page_margins == 1 or c.sync_t_b_page_margins == true
    end

    function adapter:onSetPageHorizMargins(values, when_applied_callback)
        self.configurable.h_page_margins = copyConfigValue(values)
        return self:applyMargins(when_applied_callback)
    end

    function adapter:onSyncPageTopBottomMargins(sync, when_applied_callback)
        local enabled = sync == true or sync == 1
        self.configurable.sync_t_b_page_margins = enabled and 1 or 0
        if enabled then
            local top = tonumber(self.configurable.t_page_margin) or 0
            local bottom = tonumber(self.configurable.b_page_margin) or 0
            local mean = math.floor((top + bottom) / 2 + 0.5)
            self.configurable.t_page_margin = mean
            self.configurable.b_page_margin = mean
        end
        return self:applyMargins(when_applied_callback)
    end

    function adapter:onSetPageTopMargin(value, when_applied_callback)
        self.configurable.t_page_margin = tonumber(value) or 0
        if synced(self.configurable) then self.configurable.b_page_margin = self.configurable.t_page_margin end
        return self:applyMargins(when_applied_callback)
    end

    function adapter:onSetPageBottomMargin(value, when_applied_callback)
        self.configurable.b_page_margin = tonumber(value) or 0
        if synced(self.configurable) then self.configurable.t_page_margin = self.configurable.b_page_margin end
        return self:applyMargins(when_applied_callback)
    end

    function adapter:onSetPageTopAndBottomMargin(values, when_applied_callback)
        local top_value = type(values) == "table" and values[1] or values
        local bottom_value = type(values) == "table" and values[2] or nil
        self.configurable.t_page_margin = tonumber(top_value) or self.configurable.t_page_margin or 0
        self.configurable.b_page_margin = tonumber(bottom_value) or self.configurable.b_page_margin or 0
        if self.configurable.t_page_margin ~= self.configurable.b_page_margin then
            self.configurable.sync_t_b_page_margins = 0
        end
        return self:applyMargins(when_applied_callback)
    end

    return adapter
end

function ParallelReader:showBottomMenu(index)
    local session = self.session
    local record = session and session.records[index]
    if not record or not record.doc then
        showInfo(_("This panel has no document loaded."), 3)
        return
    end
    if record.kind ~= "reflowable" then
        showInfo(_("Text size, line spacing and font settings are available for EPUB/FB2/TXT-style documents, not fixed-layout pages."), 7)
        return
    end
    if not record.configurable then
        record.configurable = createPanelConfigurable(getPanelConfigOptions(), record.doc_settings)
    end

    if session.bottom_menu then
        local old_dialog = session.bottom_menu
        session.bottom_menu = nil
        pcall(UIManager.close, UIManager, old_dialog)
    end
    self:closeTouchMenu(session)
    session.active_panel = index

    if not PanelConfigDialogClass then
        local ConfigDialog = require("ui/widget/configdialog")
        PanelConfigDialogClass = ConfigDialog:extend{}
        function PanelConfigDialogClass:onCloseWidget()
            ConfigDialog.onCloseWidget(self)
            if self.session and self.session.bottom_menu == self then
                self.session.bottom_menu = nil
            end
        end
    end

    local dialog = PanelConfigDialogClass:new{
        document = record.doc,
        ui = makePanelConfigAdapter(self, index, record),
        configurable = record.configurable,
        config_options = getPanelConfigOptions(),
        session = session,
    }
    session.bottom_menu = dialog
    -- The text-size panel is the most useful landing page.
    dialog:onShowConfigPanel(3)
    UIManager:show(dialog)
end

function ParallelReader:setScreenRotationMode(mode)
    local ok, err = runStage(self, "set_screen_rotation", function()
        if type(mode) ~= "number" then error("Invalid screen rotation mode: " .. tostring(mode)) end
        local old_mode = Screen:getRotationMode()
        if mode == old_mode then return end

        -- Even rotation modes are portrait, odd ones landscape.
        local same_layout_orientation = (mode % 2) == (old_mode % 2)
        Screen:setRotationMode(mode)

        if same_layout_orientation then
            UIManager:setDirty(self.window, "full")
        else
            UIManager:setDirty(nil, "full")
            local new_size = Screen:getSize()
            if not new_size or type(new_size.w) ~= "number" or type(new_size.h) ~= "number" then
                error("KOReader returned invalid screen dimensions after rotation")
            end
            if not (self.window and self.session) then
                error("Parallel Reader window is no longer available")
            end
            self.window:onSetDimensions(new_size)
        end
    end)
    if not ok then
        showInfo(_("Could not rotate the screen:") .. "\n\n" .. tostring(err), 10)
        return false
    end
    return true
end

------------------------------------------------------------------------
-- Menus
------------------------------------------------------------------------

local function menuAction(text, callback, extra)
    local item = { text = text, callback = callback }
    if extra then for key, value in pairs(extra) do item[key] = value end end
    return item
end

function ParallelReader:buildReaderMenuTable(session)
    local function has_document()
        local record = session.records[session.active_panel or 1]
        return record ~= nil and record.doc ~= nil
    end
    local function has_reflowable()
        local record = session.records[session.active_panel or 1]
        return record ~= nil and record.doc ~= nil and record.kind == "reflowable"
    end
    local function active_record()
        return session.records[session.active_panel or 1]
    end
    local function has_paged_document()
        local record = active_record()
        return record ~= nil and record.doc ~= nil and record.kind == "paged"
    end
    local function can_zoom_in()
        local record = active_record()
        return has_paged_document()
            and (tonumber(record.zoom_factor) or MIN_PAGE_ZOOM) < MAX_PAGE_ZOOM - 0.001
    end
    local function can_zoom_out()
        local record = active_record()
        return has_paged_document()
            and (tonumber(record.zoom_factor) or MIN_PAGE_ZOOM) > MIN_PAGE_ZOOM + 0.001
    end
    local function can_reset_zoom()
        local record = active_record()
        return has_paged_document()
            and (tonumber(record.zoom_factor) or MIN_PAGE_ZOOM) > MIN_PAGE_ZOOM + 0.001
    end
    local function active() return session.active_panel or 1 end
    local function later(fn) return function() UIManager:nextTick(fn) end end
    local function rotation(label, mode_getter)
        return menuAction(label, function()
            UIManager:nextTick(function() self:setScreenRotationMode(mode_getter()) end)
        end, { enabled_func = function() return Screen:getRotationMode() ~= mode_getter() end })
    end
    local function splitModeItem(label, mode)
        return menuAction(label, function(menu)
            self:setSplitMode(mode)
            menu:updateItems()
        end, {
            keep_menu_open = true,
            checked_func = function() return (session.split_mode or 0) == mode end,
        })
    end

    return {
        {
            icon = "appbar.navigation",
            menuAction(_("Previous page"), function() self:changePage(active(), -1) end,
                { enabled_func = has_document }),
            menuAction(_("Next page"), function() self:changePage(active(), 1) end,
                { enabled_func = has_document }),
            menuAction(_("Go to page"), later(function() self:showGoToPageDialog(active()) end),
                { enabled_func = has_document }),
            menuAction(_("Table of contents"), later(function() self:showTableOfContents(active()) end),
                { enabled_func = has_document }),
            menuAction(_("Highlights and notes"), later(function() self:showAnnotationList(active()) end),
                { enabled_func = has_reflowable }),
            menuAction(_("Zoom in"), function() self:adjustPageZoom(active(), 1) end,
                { enabled_func = can_zoom_in }),
            menuAction(_("Zoom out"), function() self:adjustPageZoom(active(), -1) end,
                { enabled_func = can_zoom_out }),
            menuAction(_("Fit page / reset zoom"), function() self:adjustPageZoom(active(), 0) end,
                { enabled_func = can_reset_zoom }),
            menuAction(_("Text and layout settings"), later(function() self:showBottomMenu(active()) end),
                { enabled_func = has_document }),
        },
        {
            icon = "appbar.filebrowser",
            menuAction(_("Open document in active panel"), function() self:chooseDocument(active()) end),
            menuAction(_("Open document in other panel"), function() self:chooseDocument(3 - active()) end),
            menuAction(_("Resume last session"), function() self:resumeLastSession() end),
            menuAction(_("Switch active panel"), function(menu)
                session.active_panel = 3 - active()
                self:refreshWindow("ui")
                menu:updateItems()
            end, { keep_menu_open = true }),
            menuAction(_("Swap panel documents"), function() self:swapDocuments() end),
            menuAction(_("Close active panel document"), function() self:closeSlot(active()) end,
                { enabled_func = has_document }),
        },
        {
            icon = "appbar.settings",
            menuAction(_("Make active panel larger"), function() self:resizeActivePanel(true) end),
            menuAction(_("Make active panel smaller"), function() self:resizeActivePanel(false) end),
            menuAction(_("Make panels equal"), function() self:setSplitRatio(0.50) end),
            splitModeItem(_("Split direction: automatic"), 0),
            splitModeItem(_("Split direction: side by side"), 1),
            splitModeItem(_("Split direction: stacked"), 2),
            menuAction(_("Show page footer"), function(menu)
                self:setFooterVisible(not session.show_footer)
                menu:updateItems()
            end, {
                keep_menu_open = true,
                checked_func = function() return session.show_footer end,
            }),
            menuAction(_("Show book title bar at the top"), function(menu)
                self:setHeaderVisible(not session.show_header)
                menu:updateItems()
            end, {
                keep_menu_open = true,
                checked_func = function() return session.show_header end,
            }),
            menuAction(_("Hold on a word opens the dictionary"), function(menu)
                setPref("dict_on_hold", getPrefs().dict_on_hold == false)
                menu:updateItems()
            end, {
                keep_menu_open = true,
                checked_func = function() return getPrefs().dict_on_hold ~= false end,
            }),
            menuAction(_("Rotate screen 90° clockwise"), function()
                local current_mode = tonumber(Screen:getRotationMode()) or Screen.DEVICE_ROTATED_UPRIGHT
                local next_mode = (current_mode + 1) % 4
                UIManager:nextTick(function() self:setScreenRotationMode(next_mode) end)
            end),
            rotation(_("Screen orientation: upright"), function() return Screen.DEVICE_ROTATED_UPRIGHT end),
            rotation(_("Screen orientation: 90° clockwise"), function() return Screen.DEVICE_ROTATED_CLOCKWISE end),
            rotation(_("Screen orientation: upside down"), function() return Screen.DEVICE_ROTATED_UPSIDE_DOWN end),
            rotation(_("Screen orientation: 90° counterclockwise"),
                function() return Screen.DEVICE_ROTATED_COUNTER_CLOCKWISE end),
            menuAction(_("Restore initial screen orientation"), function()
                UIManager:nextTick(function() self:setScreenRotationMode(session.initial_rotation_mode) end)
            end, { enabled_func = function()
                return session.initial_rotation_mode ~= nil
                    and Screen:getRotationMode() ~= session.initial_rotation_mode
            end }),
        },
        {
            icon = "appbar.menu",
            menuAction(_("Show diagnostic information"), function()
                local message = self.last_error
                    and (tostring(self.last_error_stage) .. "\n\n" .. tostring(self.last_error))
                    or _("No Lua errors captured.")
                showInfo(message, 20)
            end),
            menuAction(_("Close and continue in the normal reader"), function()
                self:closeParallelReader(true)
            end, { enabled_func = has_document }),
            menuAction(_("Close Parallel Reader"), function()
                self:closeParallelReader(false)
            end),
        },
    }
end

function ParallelReader:showReaderMenu(session)
    self:openTouchMenu(session, self:buildReaderMenuTable(session), session.menu_tab_index or 1)
end

function ParallelReader:showPanelContextMenu(session, index)
    local function has_document()
        local record = session.records[index]
        return record ~= nil and record.doc ~= nil
    end
    local function has_paged_document()
        local record = session.records[index]
        return record ~= nil and record.doc ~= nil and record.kind == "paged"
    end
    local function can_zoom_in()
        local record = session.records[index]
        return has_paged_document()
            and (tonumber(record.zoom_factor) or MIN_PAGE_ZOOM) < MAX_PAGE_ZOOM - 0.001
    end
    local function can_zoom_out()
        local record = session.records[index]
        return has_paged_document()
            and (tonumber(record.zoom_factor) or MIN_PAGE_ZOOM) > MIN_PAGE_ZOOM + 0.001
    end
    local function can_reset_zoom()
        local record = session.records[index]
        return has_paged_document()
            and (tonumber(record.zoom_factor) or MIN_PAGE_ZOOM) > MIN_PAGE_ZOOM + 0.001
    end
    local tabs = {
        {
            icon = "appbar.navigation",
            menuAction(_("Previous page"), function() self:changePage(index, -1) end,
                { enabled_func = has_document }),
            menuAction(_("Next page"), function() self:changePage(index, 1) end,
                { enabled_func = has_document }),
            menuAction(_("Go to page"), function()
                UIManager:nextTick(function() self:showGoToPageDialog(index) end)
            end, { enabled_func = has_document }),
            menuAction(_("Table of contents"), function()
                UIManager:nextTick(function() self:showTableOfContents(index) end)
            end, { enabled_func = has_document }),
            menuAction(_("Zoom in"), function() self:adjustPageZoom(index, 1) end,
                { enabled_func = can_zoom_in }),
            menuAction(_("Zoom out"), function() self:adjustPageZoom(index, -1) end,
                { enabled_func = can_zoom_out }),
            menuAction(_("Fit page / reset zoom"), function() self:adjustPageZoom(index, 0) end,
                { enabled_func = can_reset_zoom }),
            menuAction(_("Text and layout settings"), function()
                UIManager:nextTick(function() self:showBottomMenu(index) end)
            end, { enabled_func = has_document }),
            menuAction(_("Open document in this panel"), function() self:chooseDocument(index) end),
            menuAction(_("Make this panel larger"), function()
                session.active_panel = index
                self:resizeActivePanel(true)
            end),
            menuAction(_("Make this panel smaller"), function()
                session.active_panel = index
                self:resizeActivePanel(false)
            end),
            menuAction(_("Close document in this panel"), function() self:closeSlot(index) end,
                { enabled_func = has_document }),
        },
    }
    self:openTouchMenu(session, tabs, 1)
end

return ParallelReader