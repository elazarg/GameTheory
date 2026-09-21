param(
  [string]$ExpectedVersion = '',
  [string]$RepositoryRoot = (Split-Path $PSScriptRoot -Parent)
)

$ErrorActionPreference = 'Stop'
$RepositoryRoot = (Resolve-Path -LiteralPath $RepositoryRoot).Path

function Read-Version([string]$Path, [string]$Pattern) {
  $versionMatches = [regex]::Matches([IO.File]::ReadAllText($Path), $Pattern)
  if ($versionMatches.Count -ne 1) {
    throw "Expected exactly one version declaration in $Path"
  }
  return $versionMatches[0].Groups['version'].Value
}

$toolchainVersion = Read-Version (Join-Path $RepositoryRoot 'lean-toolchain') `
  '^leanprover/lean4:v(?<version>\S+)\s*$'
if ($ExpectedVersion -eq '') {
  $ExpectedVersion = $toolchainVersion
}
$ExpectedVersion = $ExpectedVersion -replace '^v', ''
if ($ExpectedVersion -notmatch '^\d+\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?$') {
  throw "Expected a release version, got '$ExpectedVersion'"
}

$lakefile = Join-Path $RepositoryRoot 'lakefile.lean'
$packageVersion = Read-Version $lakefile `
  '(?m)^\s*version\s*:=\s*v!"(?<version>[^"]+)"\s*$'
$mathlibVersion = Read-Version $lakefile `
  'require\s+"leanprover-community"\s*/\s*"mathlib"\s*@\s*git\s*"v(?<version>[^"]+)"'
$manifest = Get-Content -Raw -LiteralPath (Join-Path $RepositoryRoot 'lake-manifest.json') |
  ConvertFrom-Json
$mathlibPackages = @($manifest.packages | Where-Object { $_.name -eq 'mathlib' })
if ($mathlibPackages.Count -ne 1) {
  throw 'The generated manifest must resolve exactly one Mathlib package'
}
$versions = [ordered]@{
  Package = $packageVersion
  Lean = $toolchainVersion
  Mathlib = $mathlibVersion
  ManifestMathlib = $mathlibPackages[0].inputRev -replace '^v', ''
}
foreach ($entry in $versions.GetEnumerator()) {
  if ($entry.Value -ne $ExpectedVersion) {
    throw "$($entry.Key) version '$($entry.Value)' does not match release '$ExpectedVersion'"
  }
}
Write-Output "RELEASE_VERSION=$ExpectedVersion"
Write-Output 'VERIFIED=1'
