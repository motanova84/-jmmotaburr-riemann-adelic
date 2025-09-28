#!/usr/bin/env node
/**
 * Riemann-Adelic Web Interface
 * 
 * Simple Node.js server to showcase the mathematical functions
 * and provide a web interface for the Riemann Hypothesis validation.
 */

const express = require('express');
const cors = require('cors');
const helmet = require('helmet');
const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');

const app = express();
const PORT = process.env.PORT || 3000;

// Middleware
app.use(helmet());
app.use(cors());
app.use(express.json());
app.use(express.static('public'));

// Routes
app.get('/', (req, res) => {
    res.json({
        name: 'Riemann-Adelic: The Definitive Proof of the Riemann Hypothesis',
        version: '1.0.0',
        author: 'José Manuel Mota Burruezo',
        institute: 'Instituto Conciencia Cuántica (ICQ)',
        endpoints: {
            '/': 'This info page',
            '/health': 'Health check',
            '/validate': 'Run quick validation',
            '/demo': 'Run critical line demonstration',
            '/functions': 'List available test functions',
            '/test-f1': 'Test enhanced f1 function'
        }
    });
});

app.get('/health', (req, res) => {
    res.json({ 
        status: 'healthy', 
        timestamp: new Date().toISOString(),
        python_available: fs.existsSync('validate_explicit_formula.py')
    });
});

app.get('/functions', (req, res) => {
    res.json({
        test_functions: {
            f1: 'Enhanced smooth bump function with improved numerical stability',
            f2: 'Cosine-based compactly supported function',
            f3: 'Polynomial cutoff function',
            truncated_gaussian: 'Smooth compactly supported Gaussian function'
        },
        archimedean_functions: {
            A_infty: 'Enhanced Archimedean contribution with improved convergence'
        },
        validation_scripts: {
            'validate_explicit_formula.py': 'Main explicit formula validation',
            'demo_critical_line.py': 'Critical line verification demonstration',
            'validate_v5_coronacion.py': 'V5 Coronación complete validation'
        }
    });
});

app.post('/validate', async (req, res) => {
    const { max_primes = 50, max_zeros = 50, test_function = 'f1' } = req.body;
    
    try {
        const python = spawn('python', [
            'validate_explicit_formula.py',
            '--max_primes', max_primes.toString(),
            '--max_zeros', max_zeros.toString(),
            '--test_functions', test_function,
            '--precision_dps', '15'
        ]);
        
        let stdout = '';
        let stderr = '';
        
        python.stdout.on('data', (data) => {
            stdout += data.toString();
        });
        
        python.stderr.on('data', (data) => {
            stderr += data.toString();
        });
        
        python.on('close', (code) => {
            res.json({
                success: code === 0,
                exit_code: code,
                output: stdout,
                error: stderr,
                parameters: { max_primes, max_zeros, test_function }
            });
        });
        
        // Timeout after 30 seconds
        setTimeout(() => {
            python.kill();
            res.status(408).json({ error: 'Validation timeout' });
        }, 30000);
        
    } catch (error) {
        res.status(500).json({ error: error.message });
    }
});

app.post('/demo', async (req, res) => {
    try {
        const python = spawn('python', ['demo_critical_line.py']);
        
        let stdout = '';
        let stderr = '';
        
        python.stdout.on('data', (data) => {
            stdout += data.toString();
        });
        
        python.stderr.on('data', (data) => {
            stderr += data.toString();
        });
        
        python.on('close', (code) => {
            res.json({
                success: code === 0,
                exit_code: code,
                output: stdout,
                error: stderr
            });
        });
        
        // Timeout after 60 seconds
        setTimeout(() => {
            python.kill();
            res.status(408).json({ error: 'Demo timeout' });
        }, 60000);
        
    } catch (error) {
        res.status(500).json({ error: error.message });
    }
});

app.post('/test-f1', async (req, res) => {
    try {
        const python = spawn('python', ['test_function_updates.py']);
        
        let stdout = '';
        let stderr = '';
        
        python.stdout.on('data', (data) => {
            stdout += data.toString();
        });
        
        python.stderr.on('data', (data) => {
            stderr += data.toString();
        });
        
        python.on('close', (code) => {
            res.json({
                success: code === 0,
                exit_code: code,
                output: stdout,
                error: stderr,
                message: 'Enhanced f1 function test completed'
            });
        });
        
        // Timeout after 30 seconds
        setTimeout(() => {
            python.kill();
            res.status(408).json({ error: 'Test timeout' });
        }, 30000);
        
    } catch (error) {
        res.status(500).json({ error: error.message });
    }
});

// Error handling middleware
app.use((err, req, res, next) => {
    console.error(err.stack);
    res.status(500).json({ error: 'Something went wrong!' });
});

// 404 handler
app.use((req, res) => {
    res.status(404).json({ error: 'Endpoint not found' });
});

// Start server
app.listen(PORT, () => {
    console.log(`🧮 Riemann-Adelic server running on http://localhost:${PORT}`);
    console.log(`📋 API endpoints available at http://localhost:${PORT}/`);
});

module.exports = app;