param(
    [Parameter(Mandatory = $true)]
    [string]$RepositoryUrl
)

$ErrorActionPreference = "Stop"

git init -b main
git add .
git commit -m "Initial reproducibility release"
git remote add origin $RepositoryUrl
git push -u origin main

Write-Host "Repository pushed. Next: enable it in Zenodo, add the paper DOI metadata, and publish release v1.0.0."
