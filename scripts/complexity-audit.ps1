#Requires -Version 7.0
param()

$ErrorActionPreference = 'Stop'
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path

# Ignore comments and quoted strings so documentation does not create imports.
function Remove-LeanCommentsAndStrings([string] $Source, [switch] $PreserveStrings) {
  $result = [Text.StringBuilder]::new()
  $stringValue = [Text.StringBuilder]::new()
  $depth = 0
  $inString = $false
  $escaped = $false
  for ($i = 0; $i -lt $Source.Length; $i++) {
    $c = $Source[$i]
    $next = if ($i + 1 -lt $Source.Length) { $Source[$i + 1] } else { [char]0 }
    if ($depth -gt 0) {
      if ($c -eq '/' -and $next -eq '-') { $depth++; $i++ }
      elseif ($c -eq '-' -and $next -eq '/') { $depth--; $i++ }
      elseif ($c -eq "`n") { [void] $result.Append("`n") }
      continue
    }
    if ($inString) {
      if (-not $escaped -and $c -eq '"') {
        $inString = $false
        if ($PreserveStrings) {
          # A literal stays one token on one line, even if its contents contain
          # a newline followed by a fake `require` directive.
          $literal = $stringValue.ToString().Replace("`r", '\r').Replace("`n", '\n')
          [void] $result.Append('"').Append($literal).Append('"')
        }
      } else {
        [void] $stringValue.Append($c)
        if ($escaped) { $escaped = $false }
        elseif ($c -eq '\') { $escaped = $true }
        if (-not $PreserveStrings -and $c -eq "`n") { [void] $result.Append("`n") }
      }
      continue
    }
    if ($c -eq '/' -and $next -eq '-') {
      [void] $result.Append(' ')
      $depth = 1; $i++; continue
    }
    if ($c -eq '-' -and $next -eq '-') {
      while ($i -lt $Source.Length -and $Source[$i] -ne "`n") { $i++ }
      [void] $result.Append("`n")
      continue
    }
    if ($c -eq '"') {
      [void] $result.Append(' ')
      [void] $stringValue.Clear()
      $inString = $true; continue
    }
    [void] $result.Append($c)
  }
  $result.ToString()
}

$forbidden = '^(?:GameTheory\.Complexity(?:\.|$)|GameTheoryComplexity(?:\.|$)|Complexitylib(?:\.|$)|Cslib(?:\.|$))'
$baseSources = @(Get-ChildItem -LiteralPath (Join-Path $RepoRoot 'GameTheory') -Recurse -Filter '*.lean')
$baseSources += Get-Item -LiteralPath (Join-Path $RepoRoot 'GameTheory.lean')
foreach ($source in $baseSources) {
  $text = Remove-LeanCommentsAndStrings (Get-Content -LiteralPath $source.FullName -Raw)
  foreach ($import in [regex]::Matches($text, '(?m)^\s*(?:public\s+)?import\s+([^\r\n]+)')) {
    foreach ($module in ($import.Groups[1].Value -split '\s+')) {
      if ($module -match $forbidden) { throw "Base module imports optional complexity surface: $($source.FullName) ($module)" }
    }
  }
}

$baseConfig = Remove-LeanCommentsAndStrings (Get-Content -LiteralPath (Join-Path $RepoRoot 'lakefile.lean') -Raw) -PreserveStrings
if ($baseConfig -match '(?m)^\s*require\s+(?:(?:"[^"\r\n]+"|[\w-]+)\s*/\s*)?["«]?(?:complexitylib|cslib|GameTheoryComplexity)(?:["»\s]|$)') {
  throw 'Base Lake configuration directly requires an optional dependency'
}

$baseManifest = Get-Content -LiteralPath (Join-Path $RepoRoot 'lake-manifest.json') -Raw | ConvertFrom-Json
foreach ($dependency in $baseManifest.packages) {
  if ($dependency.name -match '^(complexitylib|cslib|GameTheoryComplexity)$') {
    throw "Base manifest requires optional dependency: $($dependency.name)"
  }
}
$extensionRoot = Join-Path $RepoRoot 'extensions/complexity'
if ((Get-Content -LiteralPath (Join-Path $RepoRoot 'lean-toolchain') -Raw).Trim() -ne
    (Get-Content -LiteralPath (Join-Path $extensionRoot 'lean-toolchain') -Raw).Trim()) {
  throw 'Base and complexity toolchains differ'
}
$extensionManifestPath = Join-Path $extensionRoot 'lake-manifest.json'
if (Test-Path -LiteralPath $extensionManifestPath) {
  $extensionManifest = Get-Content -LiteralPath $extensionManifestPath -Raw | ConvertFrom-Json
  $baseMathlib = @($baseManifest.packages | Where-Object name -eq 'mathlib')
  $extensionMathlib = @($extensionManifest.packages | Where-Object name -eq 'mathlib')
  if ($baseMathlib.Count -ne 1 -or $extensionMathlib.Count -ne 1 -or
      $baseMathlib[0].rev -ne $extensionMathlib[0].rev) {
    throw 'Base and complexity Mathlib pins differ'
  }
  foreach ($dependency in $extensionManifest.packages) {
    if ($dependency.type -eq 'git' -and $dependency.url -match 'gili-b/VI-NP-verification') {
      throw 'Private compatibility fork is not a distributable dependency'
    }
  }
}
Write-Output 'COMPLEXITY_OPTIONAL_BOUNDARY=PASS'
