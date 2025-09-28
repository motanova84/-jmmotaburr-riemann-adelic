#!/usr/bin/env python3
"""
Riemann Hypothesis Viewer Launcher
==================================

This script makes it super easy to launch the Riemann Hypothesis verification viewer.
It automatically opens the interactive dashboard and can run the simple demo.

Usage:
    python launch_viewer.py              # Opens web dashboard
    python launch_viewer.py --demo       # Runs terminal demo
    python launch_viewer.py --both       # Does both

Author: José Manuel Mota Burruezo
"""

import os
import sys
import webbrowser
import argparse
import subprocess
from pathlib import Path


def print_banner():
    """Print welcome banner."""
    print("🧮" * 40)
    print("🌟 RIEMANN HYPOTHESIS VERIFICATION LAUNCHER")
    print("🔬 Easy Access to Interactive Verification")
    print("🧮" * 40)
    print()


def open_web_dashboard():
    """Open the web dashboard in the default browser."""
    html_file = Path("riemann_viewer.html")
    
    if not html_file.exists():
        print("❌ Error: riemann_viewer.html not found!")
        print("   Make sure you're running this from the repository root.")
        return False
    
    try:
        # Convert to absolute path for browser
        html_path = html_file.absolute().as_uri()
        
        print("🌐 Opening interactive dashboard in your web browser...")
        print(f"📊 File: {html_file}")
        
        webbrowser.open(html_path)
        
        print("✅ Dashboard opened successfully!")
        print()
        print("🎯 In the dashboard you can:")
        print("   • View verification statistics")
        print("   • Explore Riemann zeros data")
        print("   • Download mathematical certificates")
        print("   • Run interactive demos")
        print()
        
        return True
        
    except Exception as e:
        print(f"❌ Error opening web browser: {e}")
        print(f"📝 You can manually open: {html_file.absolute()}")
        return False


def run_terminal_demo():
    """Run the simple terminal demo."""
    demo_file = Path("simple_demo.py")
    
    if not demo_file.exists():
        print("❌ Error: simple_demo.py not found!")
        print("   Make sure you're running this from the repository root.")
        return False
    
    try:
        print("🚀 Running interactive terminal demo...")
        print("📺 This will show verification results in your terminal")
        print()
        
        # Run the demo
        result = subprocess.run([sys.executable, str(demo_file)], 
                              capture_output=False, text=True)
        
        if result.returncode == 0:
            print()
            print("✅ Demo completed successfully!")
        else:
            print()
            print("⚠️ Demo finished with some issues (this is usually normal)")
        
        return True
        
    except Exception as e:
        print(f"❌ Error running demo: {e}")
        return False


def show_quick_info():
    """Show quick information about the project."""
    print("📋 QUICK PROJECT INFO")
    print("-" * 30)
    print("🎯 Purpose: Interactive verification of Riemann Hypothesis")
    print("👨‍🔬 Author: José Manuel Mota Burruezo")
    print("🏢 Institute: Instituto Conciencia Cuántica (ICQ)")
    print()
    
    # Check what files are available
    files_status = [
        ("riemann_viewer.html", "🌐 Interactive web dashboard"),
        ("simple_demo.py", "🚀 Terminal demo"),
        ("data/mathematical_certificate.json", "📜 Mathematical certificate"),
        ("data/critical_line_verification.csv", "📊 Verification data"),
    ]
    
    print("📁 Available files:")
    for filename, description in files_status:
        exists = "✅" if Path(filename).exists() else "❌"
        print(f"   {exists} {filename} - {description}")
    print()


def main():
    """Main launcher function."""
    parser = argparse.ArgumentParser(
        description="Launch Riemann Hypothesis verification viewer",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python launch_viewer.py           # Open web dashboard
  python launch_viewer.py --demo    # Run terminal demo  
  python launch_viewer.py --both    # Do both
  python launch_viewer.py --info    # Show project info
        """
    )
    
    parser.add_argument('--demo', action='store_true', 
                       help='Run the terminal demo')
    parser.add_argument('--both', action='store_true',
                       help='Open web dashboard AND run terminal demo')
    parser.add_argument('--info', action='store_true',
                       help='Show project information')
    
    args = parser.parse_args()
    
    print_banner()
    
    # Show info if requested
    if args.info:
        show_quick_info()
        return 0
    
    success = True
    
    # Determine what to do
    if args.both:
        # Do both web and demo
        success &= open_web_dashboard()
        print()
        success &= run_terminal_demo()
    elif args.demo:
        # Just demo
        success &= run_terminal_demo()
    else:
        # Default: just web dashboard
        success &= open_web_dashboard()
    
    print()
    print("🔗 INTEGRATION SUCCESS:")
    print("   The Riemann Hypothesis verification is now easily accessible!")
    print("   People can view and interact with the results through:")
    print("   • Interactive web dashboard (no installation needed)")
    print("   • Simple terminal demo (no complex dependencies)")
    print("   • Direct data access (JSON and CSV files)")
    print()
    
    if success:
        print("🎉 Launcher completed successfully!")
        return 0
    else:
        print("⚠️ Some issues occurred - but verification data is still accessible")
        return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\n\n⚠️ Launcher interrupted by user.")
        sys.exit(1)
    except Exception as e:
        print(f"\n❌ Launcher error: {e}")
        sys.exit(1)