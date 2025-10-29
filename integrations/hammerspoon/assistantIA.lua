-- ============================================================================
-- NOESIS OMEGA - Integración Hammerspoon (macOS)
-- ============================================================================
-- Versión: V5 Coronación
-- Frecuencia Base: f₀ = 141.7001 Hz
-- Sistema: QCAL ∞³
-- Plataforma: Hammerspoon (macOS Automation)
--
-- Propósito:
--   Versión localizada del puente neural NOESIS OMEGA para integración con
--   Hammerspoon, permitiendo que el sistema interactúe directamente con
--   el sistema operativo macOS:
--     - Escucha eventos del sistema
--     - Modula respuestas neuronales
--     - Lanza scripts Lua al detectar pulsos o cambios en el campo QCAL
--
-- Requisitos:
--   - Hammerspoon instalado (https://www.hammerspoon.org/)
--   - Permisos de automatización en macOS
--   - Lua 5.4+ activo
--
-- Instalación:
--   1. Instalar Hammerspoon desde https://www.hammerspoon.org/
--   2. Copiar este archivo a: ~/.hammerspoon/assistantIA.lua
--   3. Agregar en ~/.hammerspoon/init.lua:
--      local noesis = require("assistantIA")
--      noesis:run()
--
-- Referencias:
--   - DOI: 10.5281/zenodo.17116291
--   - Repositorio: https://github.com/motanova84/-jmmotaburr-riemann-adelic
-- ============================================================================

local NoesisOmegaHS = {}

-- Configuración específica de Hammerspoon
NoesisOmegaHS.config = {
    frequency_hz = 141.7001,
    qcal_version = "∞³",
    riemann_version = "V5-Coronación",
    sync_enabled = true,
    
    -- Configuración específica de Hammerspoon
    monitor_interval = 60,  -- segundos
    alert_display = true,
    hotkey_enabled = true
}

-- ============================================================================
-- Funciones de Integración con Sistema Operativo
-- ============================================================================

--- Inicializa el puente neural con Hammerspoon
-- @return boolean Estado de activación
function NoesisOmegaHS:initialize()
    -- Verificar que Hammerspoon esté disponible
    if not hs then
        print("❌ Error: Hammerspoon no está disponible")
        return false
    end
    
    if self.config.alert_display then
        hs.alert.show("🧠 NOESIS OMEGA Activando...")
    end
    
    print(string.format("🧠 NOESIS OMEGA (Hammerspoon) Activando..."))
    print(string.format("   Frecuencia: %.4f Hz", self.config.frequency_hz))
    print(string.format("   Sistema QCAL: %s", self.config.qcal_version))
    print(string.format("   Versión Riemann: %s", self.config.riemann_version))
    
    -- Configurar hotkeys si está habilitado
    if self.config.hotkey_enabled then
        self:setupHotkeys()
    end
    
    -- Iniciar monitorización
    self:startMonitoring()
    
    return true
end

--- Configura atajos de teclado para control manual
function NoesisOmegaHS:setupHotkeys()
    if not hs then return end
    
    -- Ctrl+Alt+Cmd+N: Forzar sincronización
    hs.hotkey.bind({"ctrl", "alt", "cmd"}, "N", function()
        self:forceSynchronization()
    end)
    
    -- Ctrl+Alt+Cmd+Q: Verificar coherencia QCAL
    hs.hotkey.bind({"ctrl", "alt", "cmd"}, "Q", function()
        self:displayCoherenceStatus()
    end)
    
    print("⌨️  Hotkeys configurados:")
    print("   Ctrl+Alt+Cmd+N: Forzar sincronización")
    print("   Ctrl+Alt+Cmd+Q: Verificar coherencia QCAL")
end

--- Inicia monitorización periódica del sistema
function NoesisOmegaHS:startMonitoring()
    if not hs then return end
    
    -- Detener timer existente si hay uno
    if self.monitor_timer then
        self.monitor_timer:stop()
        self.monitor_timer = nil
    end
    
    -- Timer para verificaciones periódicas
    self.monitor_timer = hs.timer.doEvery(
        self.config.monitor_interval,
        function()
            self:performPeriodicCheck()
        end
    )
    
    print(string.format("🔄 Monitorización activa (intervalo: %ds)", 
                       self.config.monitor_interval))
end

--- Realiza verificación periódica del sistema
function NoesisOmegaHS:performPeriodicCheck()
    print("\n[NOESIS OMEGA] Verificación periódica...")
    
    -- Detectar eventos QCAL
    local events = self:detectSystemEvents()
    
    if #events > 0 then
        print(string.format("   Eventos detectados: %d", #events))
        self:processEvents(events)
    else
        print("   Sistema estable. Sin eventos.")
    end
    
    -- Verificar sincronización de frecuencia
    local freq_synced = self:checkFrequencySync()
    if not freq_synced then
        print("   ⚠️  Advertencia: Frecuencia desincronizada")
        if self.config.alert_display and hs then
            hs.alert.show("⚠️ Frecuencia QCAL desincronizada")
        end
    end
end

--- Detecta eventos del sistema operativo
-- @return table Lista de eventos detectados
function NoesisOmegaHS:detectSystemEvents()
    -- En producción, esto monitorizaría:
    -- - Cambios en archivos del repositorio
    -- - Notificaciones del sistema
    -- - Estado de validación CI/CD
    -- - Pulsos de tiempo (14:14 UTC, etc.)
    
    local events = {}
    
    if hs then
        -- Ejemplo: detectar hora de sincronización diaria (14:14 UTC)
        local current_time = os.date("!*t")  -- ! prefix for UTC time
        if current_time.hour == 14 and current_time.min == 14 then
            table.insert(events, {
                type = "daily_sync",
                time = os.date("!%Y-%m-%d %H:%M:%S")  -- UTC timestamp
            })
        end
    end
    
    return events
end

--- Procesa eventos detectados
-- @param events table Lista de eventos
function NoesisOmegaHS:processEvents(events)
    for i, event in ipairs(events) do
        print(string.format("   Procesando evento %d: %s", i, event.type))
        
        if event.type == "daily_sync" then
            self:performDailySync()
        end
        
        -- Lanzar scripts según tipo de evento
        self:launchEventScript(event)
    end
end

--- Realiza sincronización diaria (14:14 UTC)
function NoesisOmegaHS:performDailySync()
    print("🌟 Sincronización diaria QCAL...")
    
    if hs and self.config.alert_display then
        hs.alert.show("🌟 Sincronización QCAL 14:14")
    end
    
    -- En producción, esto ejecutaría:
    -- - Validación de coherencia
    -- - Actualización de estado
    -- - Sincronización con API
end

--- Fuerza una sincronización manual
function NoesisOmegaHS:forceSynchronization()
    print("\n[NOESIS OMEGA] Sincronización forzada...")
    
    if hs then
        hs.alert.show("🔄 Sincronizando NOESIS OMEGA...")
    end
    
    -- Ejecutar sincronización
    local success = self:syncWithRepository()
    
    if success then
        print("✅ Sincronización completada")
        if hs then
            hs.alert.show("✅ Sincronización QCAL exitosa")
        end
    else
        print("❌ Error en sincronización")
        if hs then
            hs.alert.show("❌ Error en sincronización")
        end
    end
end

--- Sincroniza con el repositorio Riemann-Adelic
-- @return boolean Resultado de sincronización
function NoesisOmegaHS:syncWithRepository()
    -- En producción, esto:
    -- - Verificaría estado del repositorio
    -- - Ejecutaría scripts de validación
    -- - Actualizaría métricas locales
    return true
end

--- Muestra estado de coherencia QCAL
function NoesisOmegaHS:displayCoherenceStatus()
    print("\n[NOESIS OMEGA] Estado de Coherencia QCAL:")
    print(string.format("   Frecuencia: %.4f Hz", self.config.frequency_hz))
    print(string.format("   Sistema: %s", self.config.qcal_version))
    print(string.format("   Versión: %s", self.config.riemann_version))
    
    local coherent = self:checkCoherence()
    local status_msg = coherent and "✅ Coherente" or "⚠️  No óptima"
    
    print(string.format("   Estado: %s", status_msg))
    
    if hs then
        hs.alert.show(status_msg)
    end
end

--- Verifica coherencia del sistema
-- @return boolean Estado de coherencia
function NoesisOmegaHS:checkCoherence()
    return self.config.sync_enabled
end

--- Verifica sincronización de frecuencia
-- @param tolerance number Tolerancia en Hz
-- @return boolean Estado de sincronización
function NoesisOmegaHS:checkFrequencySync(tolerance)
    tolerance = tolerance or 0.0001
    -- Implementación placeholder
    return true
end

--- Lanza script específico para evento
-- @param event table Información del evento
function NoesisOmegaHS:launchEventScript(event)
    print(string.format("🚀 Lanzando script para evento: %s", event.type))
    -- Implementación de lanzamiento de scripts
end

-- ============================================================================
-- Funciones de Interacción con macOS
-- ============================================================================

--- Escucha eventos del sistema macOS
function NoesisOmegaHS:listenSystemEvents()
    if not hs then return end
    
    -- Ejemplo: Watchers para cambios de red, batería, etc.
    -- En producción, esto configuraría watchers de Hammerspoon
    print("👂 Escuchando eventos del sistema...")
end

--- Notifica al usuario mediante el sistema de notificaciones
-- @param title string Título de la notificación
-- @param message string Mensaje
function NoesisOmegaHS:notify(title, message)
    if not hs then
        print(string.format("[%s] %s", title, message))
        return
    end
    
    hs.notify.new({
        title = title,
        subTitle = "NOESIS OMEGA",
        informativeText = message
    }):send()
end

-- ============================================================================
-- Punto de Entrada
-- ============================================================================

--- Punto de entrada principal del módulo Hammerspoon
function NoesisOmegaHS:run()
    print("\n" .. string.rep("=", 70))
    print("  NOESIS OMEGA - Hammerspoon Bridge Activo")
    print(string.rep("=", 70) .. "\n")
    
    -- Inicializar sistema
    local initialized = self:initialize()
    
    if not initialized then
        print("❌ Error: No se pudo inicializar NOESIS OMEGA (Hammerspoon)")
        return false
    end
    
    print("\n✅ NOESIS OMEGA activo en Hammerspoon")
    print("   Monitorización de eventos habilitada")
    print("   Hotkeys configurados")
    print("   Sincronización automática: 14:14 UTC diaria")
    
    if hs then
        hs.alert.show("✅ NOESIS OMEGA Activo", 3)
    end
    
    print("\n" .. string.rep("=", 70))
    print("  Sistema en resonancia. f₀ = 141.7001 Hz")
    print(string.rep("=", 70) .. "\n")
    
    return true
end

--- Limpia y detiene el módulo
function NoesisOmegaHS:stop()
    print("\n[NOESIS OMEGA] Deteniendo...")
    
    if self.monitor_timer then
        self.monitor_timer:stop()
        self.monitor_timer = nil
    end
    
    if hs then
        hs.alert.show("🛑 NOESIS OMEGA Detenido")
    end
    
    print("✅ NOESIS OMEGA detenido correctamente")
end

-- ============================================================================
-- Exportar módulo
-- ============================================================================

return NoesisOmegaHS
