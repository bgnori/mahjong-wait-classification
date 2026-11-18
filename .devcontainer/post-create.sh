#!/bin/bash
# Post-create script for Lean 4 DevContainer
# This script runs after the container is created.

set -e

echo "=== Lean 4 DevContainer Setup ==="

# Update Lake dependencies using the toolchain installed in the image.
echo "Updating lake dependencies..."
lake update

# If Mathlib is a dependency, fetch precompiled cache.
if grep -q "mathlib" lakefile.lean 2>/dev/null || grep -q "mathlib" lakefile.toml 2>/dev/null; then
    echo "Mathlib detected as dependency. Fetching precompiled cache..."
    echo "This may take a few minutes on first run."
    lake exe cache get || echo "WARNING: cache get failed. You may need to build Mathlib from source."
fi

echo ""
echo "=== Setup Complete ==="
echo "Lean version: $(lean --version)"
echo "Lake version: $(lake --version)"
