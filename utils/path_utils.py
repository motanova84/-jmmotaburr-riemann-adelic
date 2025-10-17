"""
Path resolution utilities for the Riemann-Adelic project.

This module provides utilities to resolve paths relative to the project root,
allowing scripts to be executed from any directory within the project.
"""

import os
from pathlib import Path


def get_project_root():
    """
    Find and return the project root directory.
    
    The project root is identified by the presence of README.md and the utils/ directory.
    This allows scripts to be run from any subdirectory within the project.
    
    Returns:
        Path: Absolute path to the project root directory
        
    Raises:
        RuntimeError: If project root cannot be found
    """
    # Start from the current file's directory
    current = Path(__file__).resolve().parent
    
    # Walk up the directory tree looking for project markers
    while current != current.parent:
        # Check for README.md as primary marker
        if (current / "README.md").exists() and (current / "utils").is_dir():
            return current
        # Also check for .git directory as secondary marker
        if (current / ".git").is_dir():
            return current
        current = current.parent
    
    # If we can't find the root, raise an error
    raise RuntimeError(
        "Could not find project root. Make sure you're running from within the project directory."
    )


def get_project_path(*path_parts):
    """
    Get an absolute path relative to the project root.
    
    Args:
        *path_parts: Path components relative to project root
        
    Returns:
        Path: Absolute path
        
    Example:
        >>> get_project_path("zeros", "zeros_t1e3.txt")
        Path("/path/to/project/zeros/zeros_t1e3.txt")
    """
    return get_project_root() / Path(*path_parts)


def ensure_project_in_path():
    """
    Ensure the project root is in sys.path for module imports.
    
    This allows 'from utils import ...' style imports to work
    regardless of where the script is executed from.
    """
    import sys
    project_root = str(get_project_root())
    if project_root not in sys.path:
        sys.path.insert(0, project_root)
