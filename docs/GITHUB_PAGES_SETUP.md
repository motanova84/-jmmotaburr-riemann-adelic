# GitHub Pages Setup Guide

## Overview

This document explains the GitHub Pages deployment configuration for the Riemann Hypothesis verification dashboard.

## Files and Configuration

### Key Files

1. **`riemann_viewer.html`** - Main interactive dashboard
2. **`.github/workflows/pages.yml`** - GitHub Actions workflow for deployment
3. **`data/`** - Directory containing verification results and certificates

### Workflow Configuration

The Pages deployment workflow includes:

- **Trigger**: Runs on push to `main` branch and pull requests
- **Permissions**: `pages: write` and `id-token: write` for deployment
- **Content**: Copies dashboard, data, and documentation to `_site` directory
- **Deployment**: Uses `actions/deploy-pages@v4` with proper enablement

### Key Fix Applied

The main issue was resolved by adding the `enablement: true` parameter to both:

1. `actions/configure-pages@v4` step:
   ```yaml
   - name: Setup Pages
     uses: actions/configure-pages@v4
     with:
       enablement: true
   ```

2. `actions/deploy-pages@v4` step:
   ```yaml
   - name: Deploy to GitHub Pages
     uses: actions/deploy-pages@v4
     with:
       token: ${{ secrets.GITHUB_TOKEN }}
       enablement: true
   ```

## Repository Settings

For the workflow to function properly, GitHub Pages must be enabled in repository settings:

1. Go to repository **Settings** → **Pages**
2. Select **Source**: "GitHub Actions"
3. Save the configuration

## Content Structure

The deployed site includes:

- **Main Dashboard** (`index.html`): Interactive verification interface
- **Data Files**: CSV and JSON files with verification results
- **Navigation**: Additional navigation page for easy access
- **Documentation**: Repository README and related docs

## Verification Dashboard Features

- 📊 Real-time verification status display
- 🎯 Critical line verification metrics
- 🔬 Technical implementation details
- 📈 Interactive data visualization
- 📜 Mathematical certificates download
- 📚 Complete documentation access

## URLs

Once deployed, the site will be available at:
- Main dashboard: `https://motanova84.github.io/-jmmotaburr-riemann-adelic/`
- Data files: `https://motanova84.github.io/-jmmotaburr-riemann-adelic/data/`
- Navigation: `https://motanova84.github.io/-jmmotaburr-riemann-adelic/navigation.html`

## Troubleshooting

### Common Issues

1. **"Get Pages site failed"** → Enable GitHub Pages in repository settings
2. **"Not Found" errors** → Check that `enablement: true` is set in workflow
3. **Missing content** → Verify all source files exist in repository
4. **Permission denied** → Ensure workflow has `pages: write` permission

### Debug Steps

1. Check workflow logs in **Actions** tab
2. Verify repository Pages settings
3. Confirm all referenced files exist
4. Test content creation locally

## Author

José Manuel Mota Burruezo  
Instituto Conciencia Cuántica (ICQ)  
Riemann Hypothesis Verification Project