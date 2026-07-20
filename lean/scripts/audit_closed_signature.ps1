$ErrorActionPreference = 'Stop'

$projectRoot = Split-Path -Parent $PSScriptRoot
$generatorFile = Join-Path $projectRoot 'OBS\CoreBranch\GeneratorThreeFactor.lean'
$source = Get-Content -LiteralPath $generatorFile -Raw -Encoding UTF8

$theorems = @(
  'rowMarkov_currentWeighted_threeFactor_closed',
  'rowMarkov_Y_eq_tau_mul_kappa_mul_etaCur',
  'rowMarkov_Y_gt_etaCur_ge_eta',
  'rowMarkov_paperCore',
  'rowMarkov_etaCur_eq_eta_iff'
)

$forbidden = '(?i)hthermo|hBrep|hDrep|hKrep|hKH|hlocal|B\s*\^\s*2\s*<\s*D\s*\*\s*H'

foreach ($name in $theorems) {
  $start = $source.IndexOf("theorem $name")
  if ($start -lt 0) {
    throw "Missing required closed theorem: $name"
  }
  $proof = $source.IndexOf(':= by', $start)
  if ($proof -lt 0) {
    throw "Could not delimit theorem signature: $name"
  }
  $signature = $source.Substring($start, $proof - $start)
  if ($signature -match $forbidden) {
    throw "Forbidden bridge assumption or conclusion-as-input detected in signature: $name"
  }
}

$structureStart = $source.IndexOf('structure BidirectionalRowMarkovData')
if ($structureStart -ge 0) {
  throw 'BidirectionalRowMarkovData must be defined only in ConcreteEdgeData.lean.'
}

$edgeFile = Join-Path $projectRoot 'OBS\CoreBranch\ConcreteEdgeData.lean'
$edgeSource = Get-Content -LiteralPath $edgeFile -Raw -Encoding UTF8
$structureStart = $edgeSource.IndexOf('structure BidirectionalRowMarkovData')
$structureEnd = $edgeSource.IndexOf('namespace BidirectionalRowMarkovData', $structureStart)
if ($structureStart -lt 0 -or $structureEnd -lt 0) {
  throw 'Could not delimit BidirectionalRowMarkovData structure.'
}
$structureBody = $edgeSource.Substring($structureStart, $structureEnd - $structureStart)
if ($structureBody -match $forbidden) {
  throw 'Forbidden bridge assumption detected in BidirectionalRowMarkovData fields.'
}

Write-Output ("PASS: {0} closed public theorem signatures and the generator structure contain no prior bridge assumptions." -f $theorems.Count)
