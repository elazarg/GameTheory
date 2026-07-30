param(
  [switch] $UpdateIndex,
  [switch] $VerifyExpected
)

$ErrorActionPreference = 'Stop'
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$PinnedRoot = Join-Path $RepoRoot 'reference/GameTheory-v1'
$CoverageRoot = Join-Path $RepoRoot 'docs/coverage'
$ScopePath = Join-Path $CoverageRoot 'FamilyScopes.tsv'
$IndexPath = Join-Path $CoverageRoot 'PinnedDeclarations.tsv'
$PinnedCommit = 'a3d8c67ed91d58e197b8c978ddcc00ba96f87c29'

function Remove-LeanCommentsAndStrings([string] $Source) {
  $result = [Text.StringBuilder]::new()
  $depth = 0
  $inString = $false
  $escaped = $false
  for ($i = 0; $i -lt $Source.Length; $i++) {
    $c = $Source[$i]
    $next = if ($i + 1 -lt $Source.Length) { $Source[$i + 1] } else { [char] 0 }
    if ($depth -gt 0) {
      if ($c -eq '/' -and $next -eq '-') { $depth++; $i++ }
      elseif ($c -eq '-' -and $next -eq '/') { $depth--; $i++ }
      elseif ($c -eq "`n") { [void] $result.Append("`n") }
      continue
    }
    if ($inString) {
      if ($escaped) { $escaped = $false }
      elseif ($c -eq '\') { $escaped = $true }
      elseif ($c -eq '"') { $inString = $false }
      elseif ($c -eq "`n") {
        $inString = $false
        [void] $result.Append("`n")
      }
      continue
    }
    if ($c -eq '/' -and $next -eq '-') { $depth = 1; $i++ }
    elseif ($c -eq '-' -and $next -eq '-') {
      while ($i -lt $Source.Length -and $Source[$i] -ne "`n") { $i++ }
      [void] $result.Append("`n")
    }
    elseif ($c -eq '"') { $inString = $true }
    else { [void] $result.Append($c) }
  }
  return $result.ToString()
}

function Read-Scopes {
  $rows = @()
  foreach ($line in [IO.File]::ReadAllLines($ScopePath)) {
    if ($line.Trim().Length -eq 0 -or $line.StartsWith('#')) { continue }
    $cells = $line.Split("`t")
    if ($cells.Count -ne 3) {
      throw "Malformed family scope row: $line"
    }
    $rows += [pscustomobject]@{
      Family = $cells[0]
      Recovery = $cells[1]
      Pattern = $cells[2]
    }
  }
  return $rows
}

function Get-PinnedFiles {
  return @(Get-ChildItem (Join-Path $PinnedRoot 'GameTheory'),
      (Join-Path $PinnedRoot 'Math') -Recurse -Filter '*.lean' |
    ForEach-Object {
      $_.FullName.Substring($PinnedRoot.Length + 1).Replace('\', '/')
    } | Sort-Object)
}

function Get-Owners([string] $Path, $Scopes) {
  return @($Scopes | Where-Object { $Path -match $_.Pattern })
}

function Get-Declarations([string] $Relative, [string] $Family) {
  $source = [IO.File]::ReadAllText((Join-Path $PinnedRoot $Relative)).Replace("`r", '')
  $code = Remove-LeanCommentsAndStrings $source
  $lines = $code.Split("`n")
  $pattern =
    '^\s*(?:@\[[^\]]+\]\s*)*' +
    '(?:(?<modifier>private|protected|noncomputable|unsafe|partial|opaque)\s+)*' +
    '(?<kind>def|theorem|lemma|structure|class|inductive|abbrev|instance)\b' +
    '(?:\s+(?<name>[^\s(:{\[\],]+))?'
  $result = @()
  for ($i = 0; $i -lt $lines.Count; $i++) {
    $match = [regex]::Match($lines[$i], $pattern)
    if (-not $match.Success) { continue }
    $kind = $match.Groups['kind'].Value
    $name = $match.Groups['name'].Value
    if ($name.Length -eq 0 -or $name.StartsWith('(') -or $name.StartsWith(':')) {
      $name = "<anonymous@$($i + 1)>"
    }
    $visibility =
      if ($lines[$i] -match '^\s*(?:@\[[^\]]+\]\s*)*private\b') { 'private' }
      else { 'public' }
    $result += [pscustomobject]@{
      Path = $Relative
      Line = $i + 1
      Family = $Family
      Kind = $kind
      Declaration = $name
      Visibility = $visibility
    }
  }
  return $result
}

function Render-Index($Declarations) {
  $lines = @(
    "# pinned_commit`t$PinnedCommit",
    '# generated_by	scripts/coverage-audit.ps1 -UpdateIndex',
    "path`tline`tfamily_id`tkind`tdeclaration`tvisibility"
  )
  foreach ($decl in $Declarations) {
    $lines += "$($decl.Path)`t$($decl.Line)`t$($decl.Family)`t" +
      "$($decl.Kind)`t$($decl.Declaration)`t$($decl.Visibility)"
  }
  return ($lines -join "`n") + "`n"
}

function Strip-Code([string] $Cell) {
  $value = $Cell.Trim()
  if ($value.StartsWith('`') -and $value.EndsWith('`') -and $value.Length -ge 2) {
    return $value.Substring(1, $value.Length - 2)
  }
  return $value
}

function Resolve-LedgerPath([string] $Cell, [string[]] $PinnedFiles) {
  $candidate = Strip-Code $Cell
  $matches = @($PinnedFiles | Where-Object {
    $_ -eq $candidate -or $_.EndsWith("/$candidate")
  })
  if ($matches.Count -eq 1) { return $matches[0] }
  return $null
}

function Read-LedgerRows([string[]] $PinnedFiles) {
  $allowed = @('port', 'adapt', 'subsumed', 'refuted', 'deferred',
    'retired', 'out of scope', 'unreviewed')
  $rows = @()
  $issues = [ordered]@{
    UnknownDisposition = 0
    MissingPath = 0
    UnknownDispositionRows = @()
    MissingPathRows = @()
  }
  $ledgers = @(Get-ChildItem $CoverageRoot -Filter '*.md' |
    Where-Object { $_.Name -ne 'README.md' } | Sort-Object Name)
  foreach ($ledger in $ledgers) {
    $statusLine = [IO.File]::ReadAllLines($ledger.FullName) |
      Where-Object { $_ -match '^Status:\s*' } | Select-Object -First 1
    $status = if ($null -eq $statusLine) { '' } else {
      ($statusLine -replace '^Status:\s*', '').Trim()
    }
    $currentPath = $null
    foreach ($line in [IO.File]::ReadAllLines($ledger.FullName)) {
      if (-not $line.StartsWith('|')) { continue }
      $cells = @($line.Split('|') | Select-Object -Skip 1 |
        Select-Object -First 7 | ForEach-Object { $_.Trim() })
      if ($cells.Count -ne 7 -or $cells[0] -in @('Pinned path', '---')) { continue }
      if ($cells[0] -ne 'same') {
        $currentPath = Resolve-LedgerPath $cells[0] $PinnedFiles
        if ($null -eq $currentPath) {
          $issues.MissingPath++
          $issues.MissingPathRows += "$($ledger.Name): $($cells[0])"
        }
      }
      $disposition = $cells[3].ToLowerInvariant()
      if ($allowed -notcontains $disposition) {
        $issues.UnknownDisposition++
        $issues.UnknownDispositionRows +=
          "$($ledger.Name): $($cells[1]) => $disposition"
      }
      $rows += [pscustomobject]@{
        Ledger = $ledger.Name
        LedgerStatus = $status
        Path = $currentPath
        Declaration = Strip-Code $cells[1]
        Kind = $cells[2]
        Disposition = $disposition
        Target = $cells[4]
        Evidence = $cells[5]
      }
    }
  }
  return [pscustomobject]@{
    Ledgers = $ledgers
    Rows = $rows
    Issues = $issues
  }
}

$Results = [ordered]@{}
function Report([string] $Key, $Value) {
  $script:Results[$Key] = $Value
  Write-Output "$Key=$Value"
}

$scopes = Read-Scopes
$pinnedFiles = Get-PinnedFiles
$allowedRecovery = @('partial', 'not-started', 'retired-open',
  'out-of-scope', 'frontier', 'complete')
$unknownRecovery = @($scopes |
  Where-Object { $allowedRecovery -notcontains $_.Recovery }).Count
$recoveryConflicts = @($scopes | Group-Object Family | Where-Object {
  @($_.Group | Select-Object -ExpandProperty Recovery -Unique).Count -ne 1
}).Count
$missingOwners = 0
$duplicateOwners = 0
$declarations = @()
foreach ($path in $pinnedFiles) {
  $owners = Get-Owners $path $scopes
  if ($owners.Count -eq 0) {
    $missingOwners++
    Write-Output "PINNED_FILE_WITHOUT_OWNER=$path"
    continue
  }
  if ($owners.Count -gt 1) {
    $duplicateOwners++
    Write-Output "PINNED_FILE_WITH_DUPLICATE_OWNER=$path"
    continue
  }
  $declarations += Get-Declarations $path $owners[0].Family
}
$declarations = @($declarations | Sort-Object Path, Line)
$renderedIndex = Render-Index $declarations

if ($UpdateIndex) {
  [IO.File]::WriteAllText($IndexPath, $renderedIndex,
    [Text.UTF8Encoding]::new($false))
}

$indexCurrent = 0
if (Test-Path $IndexPath) {
  $existing = [IO.File]::ReadAllText($IndexPath).Replace("`r", '')
  if ($existing -eq $renderedIndex) { $indexCurrent = 1 }
}

$familyIds = @($scopes | Select-Object -ExpandProperty Family -Unique)
$ledgerIndex = Read-LedgerRows $pinnedFiles
$matchedRows = @()
$missingDeclarations = 0
foreach ($row in $ledgerIndex.Rows) {
  if ($null -eq $row.Path) { continue }
  $candidates = @($declarations | Where-Object {
    $_.Path -eq $row.Path -and (
      $_.Declaration -eq $row.Declaration -or
      $_.Declaration.EndsWith(".$($row.Declaration)") -or
      $row.Declaration.EndsWith(".$($_.Declaration)")
    )
  })
  if ($candidates.Count -eq 1) {
    $matchedRows += [pscustomobject]@{
      Key = "$($candidates[0].Path)`t$($candidates[0].Line)"
      Family = $candidates[0].Family
      Row = $row
    }
  } else {
    $missingDeclarations++
    $reason = if ($candidates.Count -eq 0) { 'missing' } else { 'ambiguous' }
    Write-Output "MISSING_LEDGER_DECLARATION=$reason`:$($row.Ledger):" +
      "$($row.Path):$($row.Declaration)"
  }
}

$duplicates = @($matchedRows |
  Group-Object Key |
  Where-Object { $_.Count -gt 1 })
$accountedKeys = @($matchedRows |
  ForEach-Object { $_.Key } |
  Sort-Object -Unique)
$unaccounted = $declarations.Count - $accountedKeys.Count

$completeLedgerOpenRows = @($ledgerIndex.Rows | Where-Object {
  $_.LedgerStatus -eq 'complete' -and
    $_.Disposition -in @('unreviewed', 'deferred')
}).Count

$completeFamiliesWithOpenDeclarations = 0
$completeFamilies = @($scopes | Where-Object { $_.Recovery -eq 'complete' } |
  Select-Object -ExpandProperty Family -Unique)
foreach ($family in $completeFamilies) {
  $familyKeys = @($declarations | Where-Object { $_.Family -eq $family } |
    ForEach-Object { "$($_.Path)`t$($_.Line)" })
  $familyMatched = @($matchedRows | Where-Object { $_.Family -eq $family })
  $familyAccounted = @($familyMatched | ForEach-Object { $_.Key } |
    Sort-Object -Unique)
  $hasOpenRow = @($familyMatched | Where-Object {
    $_.Row.Disposition -in @('unreviewed', 'deferred')
  }).Count -gt 0
  if ($familyAccounted.Count -ne $familyKeys.Count -or $hasOpenRow) {
    $completeFamiliesWithOpenDeclarations++
  }
}

$ledgerFamilies = @()
$ledgerText = [IO.File]::ReadAllText(
  (Join-Path $RepoRoot 'docs/V1CoverageLedger.md'))
foreach ($family in $familyIds) {
  if ($ledgerText -match "\|\s*$([regex]::Escape($family))\s*\|") {
    $ledgerFamilies += $family
  }
}

Report 'PINNED_FILES' $pinnedFiles.Count
Report 'PINNED_DECLARATIONS' $declarations.Count
Report 'FAMILY_SCOPE_RULES' $scopes.Count
Report 'FAMILY_IDS' $familyIds.Count
Report 'UNKNOWN_FAMILY_RECOVERY' $unknownRecovery
Report 'FAMILY_RECOVERY_CONFLICTS' $recoveryConflicts
Report 'FAMILY_IDS_MISSING_FROM_LEDGER' ($familyIds.Count - $ledgerFamilies.Count)
Report 'PINNED_FILES_WITHOUT_OWNER' $missingOwners
Report 'PINNED_FILES_WITH_DUPLICATE_OWNER' $duplicateOwners
Report 'GENERATED_INDEX_CURRENT' $indexCurrent
Report 'DECLARATION_LEDGERS' $ledgerIndex.Ledgers.Count
Report 'DECLARATION_LEDGER_ROWS' $ledgerIndex.Rows.Count
Report 'UNKNOWN_DISPOSITIONS' $ledgerIndex.Issues.UnknownDisposition
Report 'MISSING_LEDGER_PATHS' $ledgerIndex.Issues.MissingPath
Report 'MISSING_LEDGER_DECLARATIONS' $missingDeclarations
Report 'DUPLICATE_LEDGER_DECLARATIONS' $duplicates.Count
Report 'COMPLETE_LEDGER_OPEN_ROWS' $completeLedgerOpenRows
Report 'COMPLETE_FAMILIES_WITH_OPEN_DECLARATIONS' `
  $completeFamiliesWithOpenDeclarations
Report 'ACCOUNTED_PINNED_DECLARATIONS' $accountedKeys.Count
Report 'UNACCOUNTED_PINNED_DECLARATIONS' $unaccounted
foreach ($issue in $ledgerIndex.Issues.UnknownDispositionRows) {
  Write-Output "UNKNOWN_DISPOSITION_ROW=$issue"
}
foreach ($issue in $ledgerIndex.Issues.MissingPathRows) {
  Write-Output "MISSING_LEDGER_PATH_ROW=$issue"
}

if ($VerifyExpected) {
  $expectedZero = @(
    'FAMILY_IDS_MISSING_FROM_LEDGER',
    'UNKNOWN_FAMILY_RECOVERY',
    'FAMILY_RECOVERY_CONFLICTS',
    'PINNED_FILES_WITHOUT_OWNER',
    'PINNED_FILES_WITH_DUPLICATE_OWNER',
    'UNKNOWN_DISPOSITIONS',
    'MISSING_LEDGER_PATHS',
    'MISSING_LEDGER_DECLARATIONS',
    'DUPLICATE_LEDGER_DECLARATIONS',
    'COMPLETE_LEDGER_OPEN_ROWS',
    'COMPLETE_FAMILIES_WITH_OPEN_DECLARATIONS')
  foreach ($key in $expectedZero) {
    if ($Results[$key] -ne 0) {
      throw "$key expected 0, got $($Results[$key])"
    }
  }
  if ($Results['GENERATED_INDEX_CURRENT'] -ne 1) {
    throw 'Generated declaration index is stale; run with -UpdateIndex'
  }
  Write-Output 'VERIFIED=1'
}
