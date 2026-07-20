#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 <repository-url>"
  exit 2
fi

git init -b main
git add .
git commit -m "Initial reproducibility release"
git remote add origin "$1"
git push -u origin main

echo "Repository pushed. Next: enable it in Zenodo, add the paper DOI metadata, and publish release v1.0.0."
