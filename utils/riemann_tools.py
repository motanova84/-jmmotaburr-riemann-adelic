#!/usr/bin/env python3
"""
Riemann Tools - Utility functions for the Riemann Hypothesis validation

This module provides helper functions for:
- Data organization and management  
- Result analysis and reporting
- Performance monitoring
- Original Riemann functions
"""

import os
import csv
import json
import logging
import mpmath as mp
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any, Optional

# Original functions (preserved)
def t_to_n(t):
    """Inversa aproximada de la fórmula de Riemann–von Mangoldt: estima n dado t."""
    return int((t / (2 * mp.pi)) * mp.log(t / (2 * mp.pi)) - (t / (2 * mp.pi)) + 0.875)

def load_zeros_near_t(filename, t_min, t_max):
    """Carga los ceros entre t_min y t_max desde un archivo de texto con un gamma por línea."""
    zeros = []
    with open(filename) as f:
        for line in f:
            gamma = float(line.strip())
            if t_min <= gamma <= t_max:
                zeros.append(mp.mpf(gamma))
    return zeros

# New enhanced functionality
def setup_directories(base_dir: str = ".") -> Dict[str, Path]:
    """
    Setup standard directory structure for the Riemann validation project.
    
    Returns:
        Dictionary mapping directory names to Path objects
    """
    base_path = Path(base_dir)
    
    directories = {
        'data': base_path / 'data',
        'logs': base_path / 'logs', 
        'docs': base_path / 'docs',
        'zeros': base_path / 'zeros',
        'notebooks': base_path / 'notebooks',
        'results': base_path / 'data' / 'results',
        'archives': base_path / 'data' / 'archives'
    }
    
    for name, path in directories.items():
        path.mkdir(parents=True, exist_ok=True)
        
    return directories

def organize_validation_results(source_dir: str = "data", archive: bool = True) -> None:
    """
    Organize validation results by timestamp and test parameters.
    
    Args:
        source_dir: Directory containing CSV result files
        archive: Whether to archive older results
    """
    source_path = Path(source_dir)
    if not source_path.exists():
        logging.warning(f"Source directory {source_dir} does not exist")
        return
        
    # Setup organized structure
    dirs = setup_directories()
    results_dir = dirs['results']
    archives_dir = dirs['archives']
    
    # Process CSV files
    csv_files = list(source_path.glob('validation_*.csv'))
    logging.info(f"Found {len(csv_files)} validation result files")
    
    for csv_file in csv_files:
        try:
            # Read and analyze the CSV
            with open(csv_file, 'r') as f:
                reader = csv.DictReader(f)
                rows = list(reader)
                
            if not rows:
                logging.warning(f"Empty CSV file: {csv_file}")
                continue
                
            # Extract metadata from first row
            first_row = rows[0] 
            timestamp = first_row.get('timestamp', 'unknown')
            
            if timestamp != 'unknown':
                try:
                    dt = datetime.fromisoformat(timestamp.replace('Z', '+00:00'))
                    date_str = dt.strftime('%Y-%m-%d')
                    time_str = dt.strftime('%H-%M-%S')
                except ValueError:
                    date_str = 'unknown-date'
                    time_str = 'unknown-time'
            else:
                date_str = 'unknown-date'
                time_str = 'unknown-time'
                
            # Create organized filename
            params = f"P{first_row.get('P', 'X')}_K{first_row.get('K', 'X')}_T{first_row.get('T', 'X')}"
            new_name = f"validation_{date_str}_{time_str}_{params}.csv"
            
            # Move to organized location
            if archive:
                dest = archives_dir / date_str / new_name
            else:
                dest = results_dir / new_name
                
            dest.parent.mkdir(parents=True, exist_ok=True)
            
            # Copy with metadata
            import shutil
            shutil.copy2(csv_file, dest)
            
            logging.info(f"Organized: {csv_file.name} -> {dest}")
            
        except Exception as e:
            logging.error(f"Error processing {csv_file}: {e}")

def generate_summary_report(results_dir: str = "data/results") -> str:
    """
    Generate a summary report of all validation results.
    
    Returns:
        Path to generated report file
    """
    results_path = Path(results_dir)
    if not results_path.exists():
        logging.warning(f"Results directory {results_path} does not exist")
        return ""
    
    # Find all result files
    csv_files = list(results_path.rglob('validation_*.csv'))
    
    if not csv_files:
        logging.warning("No validation result files found")
        return ""
    
    # Collect data from all files
    all_results = []
    for csv_file in csv_files:
        try:
            with open(csv_file, 'r') as f:
                reader = csv.DictReader(f)
                for row in reader:
                    row['source_file'] = str(csv_file.name)
                    all_results.append(row)
        except Exception as e:
            logging.warning(f"Could not read {csv_file}: {e}")
    
    if not all_results:
        logging.warning("No valid result data found")
        return ""
    
    # Generate report
    report_path = Path("data") / f"summary_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.md"
    
    with open(report_path, 'w') as f:
        f.write("# Riemann Hypothesis Validation Summary Report\n\n")
        f.write(f"Generated: {datetime.now().isoformat()}\n")
        f.write(f"Total validation runs: {len(all_results)}\n\n")
        
        # Group by test function
        by_function = {}
        for result in all_results:
            func = result.get('test_function', 'unknown')
            if func not in by_function:
                by_function[func] = []
            by_function[func].append(result)
        
        f.write("## Results by Test Function\n\n")
        for func_name, results in by_function.items():
            f.write(f"### {func_name}\n\n")
            passed = sum(1 for r in results if r.get('validation_passed', '').lower() == 'true')
            failed = len(results) - passed
            f.write(f"- Total runs: {len(results)}\n")
            f.write(f"- Passed: {passed} ({passed/len(results)*100:.1f}%)\n") 
            f.write(f"- Failed: {failed} ({failed/len(results)*100:.1f}%)\n")
            
            if results:
                # Best and worst errors
                errors = []
                for r in results:
                    try:
                        err = float(r.get('relative_error', float('inf')))
                        errors.append(err)
                    except (ValueError, TypeError):
                        pass
                        
                if errors:
                    f.write(f"- Best relative error: {min(errors):.2e}\n")
                    f.write(f"- Worst relative error: {max(errors):.2e}\n")
                    f.write(f"- Average relative error: {sum(errors)/len(errors):.2e}\n")
            f.write("\n")
        
        # Parameter analysis
        f.write("## Parameter Analysis\n\n")
        params = ['P', 'K', 'T', 'delta']
        for param in params:
            values = []
            for result in all_results:
                try:
                    val = float(result.get(param, 0))
                    values.append(val)
                except (ValueError, TypeError):
                    pass
            if values:
                f.write(f"### {param}\n")
                f.write(f"- Range: {min(values)} - {max(values)}\n")
                f.write(f"- Most common: {max(set(values), key=values.count)}\n\n")
    
    logging.info(f"Summary report generated: {report_path}")
    return str(report_path)

def clean_old_logs(logs_dir: str = "logs", keep_days: int = 30) -> None:
    """
    Clean old log files to save space.
    
    Args:
        logs_dir: Directory containing log files
        keep_days: Number of days to keep logs
    """
    logs_path = Path(logs_dir)
    if not logs_path.exists():
        return
    
    cutoff_time = datetime.now().timestamp() - (keep_days * 24 * 3600)
    
    removed_count = 0
    for log_file in logs_path.glob('*.log'):
        if log_file.stat().st_mtime < cutoff_time:
            try:
                log_file.unlink()
                removed_count += 1
            except OSError as e:
                logging.warning(f"Could not remove {log_file}: {e}")
    
    if removed_count > 0:
        logging.info(f"Cleaned {removed_count} old log files")

def check_data_integrity() -> Dict[str, Any]:
    """
    Check integrity of all project data files.
    
    Returns:
        Dictionary with integrity check results
    """
    results = {
        'timestamp': datetime.now().isoformat(),
        'zeros_files': {},
        'result_files': {},
        'log_files': {}
    }
    
    # Check zeros files
    zeros_path = Path('zeros')
    if zeros_path.exists():
        for zeros_file in zeros_path.glob('zeros_*.txt'):
            try:
                size = zeros_file.stat().st_size
                with open(zeros_file, 'r') as f:
                    line_count = sum(1 for _ in f)
                    
                results['zeros_files'][zeros_file.name] = {
                    'size_bytes': size,
                    'line_count': line_count,
                    'exists': True
                }
            except Exception as e:
                results['zeros_files'][zeros_file.name] = {
                    'error': str(e),
                    'exists': True
                }
    
    # Check result files  
    for results_dir in ['data', 'data/results', 'data/archives']:
        path = Path(results_dir)
        if path.exists():
            csv_files = list(path.rglob('*.csv'))
            results['result_files'][results_dir] = {
                'count': len(csv_files),
                'total_size': sum(f.stat().st_size for f in csv_files if f.exists())
            }
    
    # Check log files
    logs_path = Path('logs') 
    if logs_path.exists():
        log_files = list(logs_path.glob('*.log'))
        results['log_files'] = {
            'count': len(log_files),
            'total_size': sum(f.stat().st_size for f in log_files if f.exists())
        }
    
    return results

def main():
    """Main function for command-line usage."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Riemann validation data tools')
    parser.add_argument('--organize', action='store_true',
                       help='Organize validation result files')
    parser.add_argument('--report', action='store_true', 
                       help='Generate summary report')
    parser.add_argument('--clean-logs', type=int, default=0,
                       help='Clean log files older than N days')
    parser.add_argument('--check-integrity', action='store_true',
                       help='Check data file integrity')
    
    args = parser.parse_args()
    
    logging.basicConfig(level=logging.INFO,
                       format='%(asctime)s - %(levelname)s - %(message)s')
    
    if args.organize:
        organize_validation_results()
        
    if args.report:
        report_path = generate_summary_report()
        print(f"Summary report: {report_path}")
        
    if args.clean_logs > 0:
        clean_old_logs(keep_days=args.clean_logs)
        
    if args.check_integrity:
        integrity = check_data_integrity()
        print(json.dumps(integrity, indent=2))

if __name__ == "__main__":
    main()

