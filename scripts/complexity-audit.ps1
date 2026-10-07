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
  $inIdentifier = $false
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
    if ($inIdentifier) {
      [void] $result.Append($c)
      if ($c -eq '»') { $inIdentifier = $false }
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
    if ($c -eq '«') {
      $inIdentifier = $true
      [void] $result.Append($c)
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

function Get-LeanImports([string] $Source) {
  $text = Remove-LeanCommentsAndStrings $Source
  $header = '(?m)^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\r\n]+)'
  $component = '«[^»\r\n]*»|[^\s.«»]+'
  $identifier = "(?:$component)(?:\.(?:$component))*"
  foreach ($import in [regex]::Matches($text, $header)) {
    foreach ($module in [regex]::Matches($import.Groups[1].Value, $identifier)) {
      $components = @([regex]::Matches($module.Value, $component) | ForEach-Object {
        if ($_.Value.StartsWith('«')) { $_.Value.Substring(1, $_.Value.Length - 2) }
        else { $_.Value }
      })
      # Components distinguish a quoted identifier containing a literal dot
      # from two actual module-name components.
      [pscustomobject]@{
        Name = $module.Value
        Components = $components
        Key = $components -join ([char]0x1f)
      }
    }
  }
}

$baseSources = @(Get-ChildItem -LiteralPath (Join-Path $RepoRoot 'GameTheory') -Recurse -Filter '*.lean')
$baseSources += Get-Item -LiteralPath (Join-Path $RepoRoot 'GameTheory.lean')
foreach ($source in $baseSources) {
  foreach ($module in (Get-LeanImports (Get-Content -LiteralPath $source.FullName -Raw))) {
    $components = $module.Components
    if ($components[0] -cin @('GameTheoryComplexity', 'Complexitylib', 'Cslib') -or
        ($components.Count -ge 2 -and $components[0] -ceq 'GameTheory' -and $components[1] -ceq 'Complexity')) {
      throw "Base module imports optional complexity surface: $($source.FullName) ($($module.Name))"
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
$publicSources = @()
$sourceRoot = Join-Path $extensionRoot 'GameTheoryComplexity'
if (Test-Path -LiteralPath $sourceRoot) {
  $publicSources += Get-ChildItem -LiteralPath $sourceRoot -Recurse -Filter '*.lean' | Where-Object {
    $_.FullName -notmatch '[\\/](Tests|Experimental)[\\/]' -and $_.BaseName -notlike '*Test'
  }
}
$umbrella = Join-Path $extensionRoot 'GameTheoryComplexity.lean'
if (Test-Path -LiteralPath $umbrella) { $publicSources += Get-Item -LiteralPath $umbrella }
if ($publicSources.Count -gt 0) {
  $lintPath = Join-Path $extensionRoot 'lint/GameTheoryComplexity/LintAll.lean'
  if (-not (Test-Path -LiteralPath $lintPath)) { throw 'Complexity public modules have no lint import driver' }
  $lintImports = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach ($module in (Get-LeanImports (Get-Content -LiteralPath $lintPath -Raw))) {
    [void] $lintImports.Add($module.Key)
  }
  foreach ($source in $publicSources) {
    $relative = [IO.Path]::GetRelativePath($extensionRoot, $source.FullName)
    $parts = @($relative -split '[\\/]')
    $parts[-1] = [IO.Path]::GetFileNameWithoutExtension($parts[-1])
    if (-not $lintImports.Contains($parts -join ([char]0x1f))) {
      throw "Complexity public module missing from lint imports: $($parts -join '.')"
    }
  }
}
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
