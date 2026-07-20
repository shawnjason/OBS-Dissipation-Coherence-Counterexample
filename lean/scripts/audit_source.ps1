$ErrorActionPreference = 'Stop'

$projectRoot = Split-Path -Parent $PSScriptRoot
$leanFiles = Get-ChildItem -LiteralPath $projectRoot -Recurse -File -Filter '*.lean' |
  Where-Object { $_.FullName -notlike '*\.lake\packages\*' }

$forbidden = '(?i)\b(sorry|admit|axiom|unsafe|native_decide)\b|sorryAx'
$hits = $leanFiles | Select-String -Pattern $forbidden
if ($hits) {
  $hits | ForEach-Object {
    Write-Error ("Forbidden proof-bypass token at {0}:{1}: {2}" -f
      $_.Path, $_.LineNumber, $_.Line.Trim())
  }
  exit 1
}

Write-Output ("PASS: scanned {0} project Lean source files; no forbidden proof-bypass tokens." -f
  $leanFiles.Count)
