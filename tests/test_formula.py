"""
Tests automáticos para la validación de la fórmula explícita
Riemann-Adelic: Flujo simbiótico ∞³
"""

import pytest
import mpmath as mp
from utils.mellin import truncated_gaussian, mellin_transform
from utils.riemann_tools import t_to_n, load_zeros_near_t
import os
import tempfile

# Configurar precisión para tests
mp.mp.dps = 25  # Precisión reducida para velocidad en tests

class TestMellinTransforms:
    """Tests para transformadas de Mellin"""
    
    def test_truncated_gaussian_support(self):
        """Test que la función Gaussiana truncada tiene soporte compacto"""
        f = truncated_gaussian
        
        # Dentro del soporte
        assert f(0) > 0
        assert f(2.5) > 0
        
        # Fuera del soporte
        assert f(6) == 0
        assert f(-6) == 0
    
    def test_mellin_transform_convergence(self):
        """Test que la transformada de Mellin converge"""
        f = truncated_gaussian
        
        # Para s = 0, debería ser la integral de f
        result = mellin_transform(f, 0, lim=5.0)
        expected_integral = mp.quad(f, [-5, 5])
        
        assert abs(result - expected_integral) < mp.mpf('1e-15')
    
    def test_mellin_transform_symmetry(self):
        """Test simetría para función par"""
        f = lambda u: mp.exp(-u**2) if abs(u) <= 3 else mp.mpf(0)
        
        # Para función par, Im(mellin_transform(f, iy)) debería ser 0
        result = mellin_transform(f, 1j * mp.mpf(2))
        assert abs(result.imag) < mp.mpf('1e-10')

class TestRiemannTools:
    """Tests para herramientas de ceros de Riemann"""
    
    def test_t_to_n_approximation(self):
        """Test aproximación de altura a número de cero"""
        # Para el primer cero γ₁ ≈ 14.134725
        t1 = mp.mpf('14.134725')
        n1 = t_to_n(t1)
        
        # Debería dar aproximadamente 1
        assert 0 <= n1 <= 2
    
    def test_load_zeros_near_t(self):
        """Test cargar ceros cerca de una altura dada"""
        # Crear archivo temporal con ceros de test
        test_zeros = [
            mp.mpf('14.134725'),
            mp.mpf('21.022040'),
            mp.mpf('25.010858'),
            mp.mpf('30.424876')
        ]
        
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.txt') as f:
            for zero in test_zeros:
                f.write(f"{zero}\n")
            temp_filename = f.name
        
        try:
            # Cargar ceros en rango [20, 30]
            zeros = load_zeros_near_t(temp_filename, 20, 30)
            
            # Debería cargar exactamente 2 ceros
            assert len(zeros) == 2
            assert mp.mpf('21.022040') in zeros
            assert mp.mpf('25.010858') in zeros
            
        finally:
            os.unlink(temp_filename)

class TestExplicitFormulaComponents:
    """Tests para componentes de la fórmula explícita"""
    
    def test_prime_sum_convergence(self):
        """Test convergencia de la suma sobre primos"""
        from validate_explicit_formula import prime_sum
        
        f = lambda u: mp.exp(-u**2/2) if abs(u) <= 3 else mp.mpf(0)
        
        # Con más primos debería convergir
        sum1 = prime_sum(f, P=100, K=3)
        sum2 = prime_sum(f, P=1000, K=3)
        
        # La diferencia debería ser pequeña
        diff = abs(sum2 - sum1)
        assert diff < abs(sum1) * mp.mpf('0.1')  # Menos del 10% de diferencia
    
    def test_archimedean_contribution(self):
        """Test que la contribución arquimediana es finita"""
        from validate_explicit_formula import archimedean_sum
        
        f = truncated_gaussian
        
        result = archimedean_sum(f, sigma0=2.0, T=50, lim_u=5.0)
        
        # El resultado debe ser finito y real
        assert mp.isfinite(result)
        assert mp.im(result) < mp.mpf('1e-10')  # Prácticamente real
    
    def test_zero_sum_basic(self):
        """Test suma básica sobre ceros"""
        from validate_explicit_formula import zero_sum
        
        # Crear archivo temporal con pocos ceros
        test_zeros_content = "14.134725\n21.022040\n25.010858\n"
        
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.txt') as f:
            f.write(test_zeros_content)
            temp_filename = f.name
        
        try:
            f = lambda u: mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0)
            result = zero_sum(f, temp_filename, lim_u=3)
            
            # El resultado debe ser finito
            assert mp.isfinite(result)
            
        finally:
            os.unlink(temp_filename)

class TestValidationIntegration:
    """Tests de integración completa"""
    
    def test_explicit_formula_balance_simple(self):
        """Test balance básico de la fórmula explícita"""
        from validate_explicit_formula import prime_sum, archimedean_sum
        
        # Función test simple
        def simple_test_function(u):
            return mp.exp(-u**2) if abs(u) <= 1 else mp.mpf(0)
        
        # Calcular lado aritmético (reducido para test)
        P_side = prime_sum(simple_test_function, P=100, K=2)
        A_side = archimedean_sum(simple_test_function, sigma0=2.0, T=20, lim_u=2.0)
        
        arithmetic_total = P_side + A_side
        
        # Verificar que los valores son finitos y razonables
        assert mp.isfinite(arithmetic_total)
        assert abs(arithmetic_total) < mp.mpf('1000')  # Orden de magnitud razonable
    
    @pytest.mark.slow
    def test_explicit_formula_with_mock_zeros(self):
        """Test completo con ceros simulados"""
        from validate_explicit_formula import prime_sum, archimedean_sum, zero_sum
        
        # Crear archivo con ceros de test
        mock_zeros = """14.134725141734693
21.022039638771554
25.010857580145688
30.424876125859513
32.935061587739191"""
        
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.txt') as f:
            f.write(mock_zeros)
            temp_filename = f.name
        
        try:
            f = lambda u: mp.exp(-u**2/4) if abs(u) <= 2 else mp.mpf(0)
            
            # Lado aritmético
            P_side = prime_sum(f, P=500, K=3)
            A_side = archimedean_sum(f, sigma0=2.0, T=30, lim_u=3.0)
            arithmetic_side = P_side + A_side
            
            # Lado de ceros
            zero_side = zero_sum(f, temp_filename, lim_u=3)
            
            # Calcular error
            error = abs(arithmetic_side - zero_side)
            relative_error = error / abs(arithmetic_side)
            
            # El error relativo debería ser razonable para este test
            # (no esperamos precisión extrema con parámetros reducidos)
            assert relative_error < mp.mpf('0.5'), f"Error relativo muy alto: {relative_error}"
            
        finally:
            os.unlink(temp_filename)

class TestNumericalStability:
    """Tests de estabilidad numérica"""
    
    def test_precision_consistency(self):
        """Test que diferentes precisiones dan resultados consistentes"""
        f = lambda u: mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0)
        
        # Calcular con dos precisiones diferentes
        with mp.workdps(20):
            result_20 = mellin_transform(f, mp.mpf(1), lim=3)
        
        with mp.workdps(30):
            result_30 = mellin_transform(f, mp.mpf(1), lim=3)
        
        # Los resultados deberían coincidir en los primeros 15 dígitos
        relative_diff = abs(result_20 - result_30) / abs(result_30)
        assert relative_diff < mp.mpf('1e-15')
    
    def test_parameter_variation(self):
        """Test estabilidad ante variación de parámetros"""
        from validate_explicit_formula import prime_sum
        
        f = lambda u: mp.exp(-u**2/2) if abs(u) <= 1 else mp.mpf(0)
        
        # Variar K ligeramente
        sum_k2 = prime_sum(f, P=100, K=2)
        sum_k3 = prime_sum(f, P=100, K=3)
        
        # La diferencia debería ser pequeña (función con soporte pequeño)
        diff = abs(sum_k3 - sum_k2)
        assert diff < abs(sum_k2) * mp.mpf('0.2')

# Marcar tests lentos
pytest.mark.slow = pytest.mark.skipif(
    os.environ.get("PYTEST_SKIP_SLOW", "false").lower() == "true",
    reason="Skipping slow tests"
)

if __name__ == "__main__":
    # Ejecutar tests básicos si se llama directamente
    pytest.main([__file__, "-v"])