#!/usr/bin/env python3
"""
Test CI/CD parameter consistency.

Ensures that CI/CD workflows use the standardized parameter presets
defined in utils/performance_monitor.py.
"""

import os
import sys
import yaml

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def test_parameter_presets_defined():
    """Test that parameter presets are defined in performance_monitor.py"""
    perf_monitor_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), 
                                      'utils', 'performance_monitor.py')
    
    assert os.path.exists(perf_monitor_path), "performance_monitor.py not found"
    
    with open(perf_monitor_path, 'r') as f:
        content = f.read()
    
    # Check that the three parameter presets are defined
    assert 'quick_test' in content, "quick_test preset not found"
    assert 'standard_ci' in content, "standard_ci preset not found"
    assert 'high_accuracy' in content, "high_accuracy preset not found"
    
    # Check specific parameter values
    assert '"max_primes": 50' in content, "quick_test max_primes should be 50"
    assert '"max_primes": 100' in content, "standard_ci max_primes should be 100"
    assert '"max_primes": 500' in content, "high_accuracy max_primes should be 500"


def test_quick_workflow_uses_quick_test_params():
    """Test that quick.yml uses quick_test parameters"""
    workflow_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), 
                                  '.github', 'workflows', 'quick.yml')
    
    if not os.path.exists(workflow_path):
        return  # Skip if workflow doesn't exist
    
    with open(workflow_path, 'r') as f:
        workflow = yaml.safe_load(f)
    
    env = workflow.get('env', {})
    
    # Check quick_test parameters
    assert env.get('MAX_PRIMES') == 50, f"quick.yml should use MAX_PRIMES=50, got {env.get('MAX_PRIMES')}"
    assert env.get('MAX_ZEROS') == 50, f"quick.yml should use MAX_ZEROS=50, got {env.get('MAX_ZEROS')}"
    assert env.get('PRECISION_DPS') == 15, f"quick.yml should use PRECISION_DPS=15, got {env.get('PRECISION_DPS')}"
    assert env.get('INTEGRATION_T') == 5, f"quick.yml should use INTEGRATION_T=5, got {env.get('INTEGRATION_T')}"


def test_full_workflow_uses_high_accuracy_params():
    """Test that full.yml uses high_accuracy parameters"""
    workflow_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), 
                                  '.github', 'workflows', 'full.yml')
    
    if not os.path.exists(workflow_path):
        return  # Skip if workflow doesn't exist
    
    with open(workflow_path, 'r') as f:
        workflow = yaml.safe_load(f)
    
    env = workflow.get('env', {})
    
    # Check high_accuracy parameters
    assert env.get('MAX_PRIMES') == 500, f"full.yml should use MAX_PRIMES=500, got {env.get('MAX_PRIMES')}"
    assert env.get('MAX_ZEROS') == 500, f"full.yml should use MAX_ZEROS=500, got {env.get('MAX_ZEROS')}"
    assert env.get('PRECISION_DPS') == 40, f"full.yml should use PRECISION_DPS=40, got {env.get('PRECISION_DPS')}"
    assert env.get('INTEGRATION_T') == 50, f"full.yml should use INTEGRATION_T=50, got {env.get('INTEGRATION_T')}"


def test_comprehensive_ci_uses_standard_ci_params():
    """Test that comprehensive-ci.yml uses standard_ci parameters by default"""
    workflow_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), 
                                  '.github', 'workflows', 'comprehensive-ci.yml')
    
    if not os.path.exists(workflow_path):
        return  # Skip if workflow doesn't exist
    
    with open(workflow_path, 'r') as f:
        content = f.read()
    
    # Check that standard_ci parameters are documented
    assert 'standard_ci' in content, "comprehensive-ci.yml should document standard_ci parameters"
    assert 'high_accuracy' in content, "comprehensive-ci.yml should document high_accuracy parameters"
    assert 'quick_test' in content, "comprehensive-ci.yml should document quick_test parameters"
    
    # Check that the default values match standard_ci (when run_full_validation is false)
    # The pattern is: "${{ github.event.inputs.run_full_validation == 'true' && '500' || '100' }}"
    # The '100' is the default (standard_ci)
    assert "'100'" in content, "comprehensive-ci.yml should use standard_ci max_primes=100 as default"
    assert "'25'" in content, "comprehensive-ci.yml should use standard_ci precision_dps=25 as default"
    assert "'10'" in content, "comprehensive-ci.yml should use standard_ci integration_t=10 as default"


def test_workflow_files_are_valid_yaml():
    """Test that all modified workflow files are valid YAML"""
    workflows_dir = os.path.join(os.path.dirname(os.path.dirname(__file__)), 
                                  '.github', 'workflows')
    
    if not os.path.exists(workflows_dir):
        return  # Skip if directory doesn't exist
    
    workflows_to_check = ['quick.yml', 'full.yml', 'comprehensive-ci.yml']
    
    for workflow_file in workflows_to_check:
        workflow_path = os.path.join(workflows_dir, workflow_file)
        if os.path.exists(workflow_path):
            with open(workflow_path, 'r') as f:
                try:
                    yaml.safe_load(f)
                except yaml.YAMLError as e:
                    raise AssertionError(f"{workflow_file} is not valid YAML: {e}")


if __name__ == '__main__':
    import pytest
    pytest.main([__file__, '-v'])
