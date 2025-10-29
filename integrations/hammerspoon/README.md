# 🍎 NOESIS OMEGA - Integración Hammerspoon (macOS)

Integración del puente neural NOESIS OMEGA con Hammerspoon para automatización completa en macOS.

## ⚙️ Requisitos

- **Sistema Operativo:** macOS 10.15 (Catalina) o superior
- **Hammerspoon:** Versión 0.9.97 o superior
- **Lua:** 5.4+ (incluido con Hammerspoon)
- **Permisos:** Acceso de automatización en macOS

## 📥 Instalación

### 1. Instalar Hammerspoon

Descarga e instala Hammerspoon desde:
- **Sitio oficial:** https://www.hammerspoon.org/
- **Homebrew:** `brew install hammerspoon --cask`

### 2. Configurar permisos

1. Abre **Preferencias del Sistema** → **Seguridad y Privacidad**
2. Navega a **Privacidad** → **Accesibilidad**
3. Agrega Hammerspoon a la lista de aplicaciones permitidas
4. Reinicia Hammerspoon

### 3. Instalar el módulo NOESIS OMEGA

```bash
# Crear directorio de Hammerspoon si no existe
mkdir -p ~/.hammerspoon

# Copiar el módulo assistantIA.lua
cp integrations/hammerspoon/assistantIA.lua ~/.hammerspoon/

# O crear enlace simbólico para desarrollo
ln -s "$(pwd)/integrations/hammerspoon/assistantIA.lua" ~/.hammerspoon/assistantIA.lua
```

### 4. Configurar init.lua

Edita o crea `~/.hammerspoon/init.lua` y agrega:

```lua
-- ============================================================================
-- Configuración de NOESIS OMEGA
-- ============================================================================

-- Cargar el módulo
local noesis = require("assistantIA")

-- Inicializar y ejecutar
noesis:run()

-- Opcional: Configurar parámetros personalizados
noesis.config.monitor_interval = 60  -- Intervalo de monitorización (segundos)
noesis.config.alert_display = true   -- Mostrar alertas en pantalla
noesis.config.hotkey_enabled = true  -- Habilitar atajos de teclado

-- Recargar configuración al guardar
hs.hotkey.bind({"cmd", "alt", "ctrl"}, "R", function()
  hs.reload()
  hs.alert.show("Config Reloaded")
end)

print("✅ NOESIS OMEGA configurado correctamente")
```

### 5. Recargar Hammerspoon

- Click en el ícono de Hammerspoon en la barra de menú
- Selecciona **Reload Config** o presiona `Cmd+Alt+Ctrl+R`

## 🎮 Atajos de Teclado

Una vez instalado, los siguientes atajos estarán disponibles:

| Atajo | Función |
|-------|---------|
| `Ctrl+Alt+Cmd+N` | Forzar sincronización QCAL |
| `Ctrl+Alt+Cmd+Q` | Verificar estado de coherencia |
| `Cmd+Alt+Ctrl+R` | Recargar configuración Hammerspoon |

## 🔄 Funcionalidades

### Monitorización Automática

El módulo realiza verificaciones periódicas (cada 60 segundos por defecto) para:

- Detectar eventos del sistema QCAL ∞³
- Verificar sincronización de frecuencia (141.7001 Hz)
- Monitorizar coherencia espectral
- Procesar cambios en el campo cuántico

### Sincronización Diaria

Automáticamente ejecuta sincronización completa a las **14:14 UTC** todos los días, en resonancia con el sistema adélico.

### Notificaciones del Sistema

Recibe notificaciones nativas de macOS para:

- Alertas de desincronización
- Confirmación de sincronización exitosa
- Eventos QCAL detectados
- Cambios en coherencia espectral

## 🧪 Verificación

Para verificar que el módulo está funcionando correctamente:

1. Abre la consola de Hammerspoon:
   - Click en ícono Hammerspoon → **Console**

2. Deberías ver el mensaje de inicialización:
   ```
   ======================================================================
     NOESIS OMEGA - Hammerspoon Bridge Activo
   ======================================================================
   
   🧠 NOESIS OMEGA (Hammerspoon) Activando...
      Frecuencia: 141.7001 Hz
      Sistema QCAL: ∞³
      Versión Riemann: V5-Coronación
   
   ✅ NOESIS OMEGA activo en Hammerspoon
   ```

3. Prueba los atajos de teclado:
   - Presiona `Ctrl+Alt+Cmd+Q` para verificar coherencia
   - Deberías ver una alerta en pantalla

## 🐛 Solución de Problemas

### El módulo no se carga

1. Verifica la ruta del archivo:
   ```bash
   ls -la ~/.hammerspoon/assistantIA.lua
   ```

2. Revisa la consola de Hammerspoon para errores

3. Verifica sintaxis Lua:
   ```bash
   lua -c ~/.hammerspoon/assistantIA.lua
   ```

### Permisos denegados

Si ves errores de permisos:

1. Abre **Preferencias del Sistema** → **Seguridad y Privacidad**
2. En la pestaña **Privacidad**, verifica que Hammerspoon tenga acceso a:
   - Accesibilidad
   - Automatización
   - Archivos y carpetas (si es necesario)

### Hotkeys no funcionan

Si los atajos de teclado no responden:

1. Verifica que `hotkey_enabled = true` en la configuración
2. Revisa que no haya conflictos con otros atajos del sistema
3. Reinicia Hammerspoon completamente:
   ```bash
   killall Hammerspoon && open -a Hammerspoon
   ```

## 🔧 Configuración Avanzada

### Personalizar intervalo de monitorización

```lua
-- En ~/.hammerspoon/init.lua
noesis.config.monitor_interval = 120  -- Verificar cada 2 minutos
```

### Deshabilitar alertas visuales

```lua
-- En ~/.hammerspoon/init.lua
noesis.config.alert_display = false  -- Sin alertas en pantalla
```

### Agregar eventos personalizados

Puedes extender el módulo para detectar eventos específicos:

```lua
-- En ~/.hammerspoon/init.lua después de cargar el módulo

-- Ejemplo: Detectar cambios de red
local netWatcher = hs.network.reachability.internet()
netWatcher:setCallback(function(self, flags)
  if flags & hs.network.reachability.flags.reachable then
    noesis:notify("Red Disponible", "Conexión restablecida")
    noesis:forceSynchronization()
  end
end)
netWatcher:start()
```

## 📊 Monitorización

### Logs

Los logs del módulo se muestran en la consola de Hammerspoon:

- **Info:** Operaciones normales
- **Advertencias (⚠️):** Desincronizaciones o problemas menores
- **Errores (❌):** Fallos en inicialización o sincronización

### Dashboard de estado

Presiona `Ctrl+Alt+Cmd+Q` en cualquier momento para ver el dashboard de estado:

```
[NOESIS OMEGA] Estado de Coherencia QCAL:
   Frecuencia: 141.7001 Hz
   Sistema: ∞³
   Versión: V5-Coronación
   Estado: ✅ Coherente
```

## 🔗 Integración con API

El módulo puede integrarse con los endpoints de API del repositorio:

```lua
-- Ejemplo: Llamar a API de validación
function noesis:callValidationAPI()
  local url = "https://your-vercel-app.vercel.app/api/validate-hourly"
  
  hs.http.asyncGet(url, nil, function(status, body, headers)
    if status == 200 then
      print("✅ API validation successful")
      self:notify("Validación", "API respondió exitosamente")
    end
  end)
end
```

## 📚 Referencias

- **Hammerspoon API:** https://www.hammerspoon.org/docs/
- **Repositorio principal:** https://github.com/motanova84/-jmmotaburr-riemann-adelic
- **DOI:** 10.5281/zenodo.17116291
- **Módulo base:** [/assistantIA.lua](/assistantIA.lua)

## 🤝 Contribuir

Para reportar problemas o sugerir mejoras en la integración Hammerspoon:

1. Abre un issue en el repositorio principal
2. Etiqueta con `integration:hammerspoon`
3. Incluye logs de la consola Hammerspoon si es relevante

---

**Mantenido por:** José Manuel Mota Burruezo (@motanova84)  
**Última actualización:** 2025-10-29  
**Versión del módulo:** V5 Coronación
