param(
  [switch] $UpdateIndex,
  [switch] $VerifyExpected,
  # Validate tracked declaration/ledger/capability relationships without the
  # ignored pinned source snapshot.  This is deliberately not the full gate.
  [switch] $TrackedIndexOnly
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

function Read-TrackedIndex {
  if (-not (Test-Path $IndexPath)) {
    throw "Tracked declaration index not found: $IndexPath"
  }
  $lines = [IO.File]::ReadAllLines($IndexPath)
  $expectedHeader = "path`tline`tfamily_id`tkind`tdeclaration`tvisibility"
  $commitLine = "# pinned_commit`t$PinnedCommit"
  $malformed = 0
  $declarations = @()
  if ($lines.Count -lt 3 -or $lines[0] -ne $commitLine -or
      $lines[2] -ne $expectedHeader) {
    $malformed++
  }
  for ($i = 3; $i -lt $lines.Count; $i++) {
    if ($lines[$i].Trim().Length -eq 0) { continue }
    $cells = $lines[$i].Split("`t")
    $line = 0
    if ($cells.Count -ne 6 -or -not [int]::TryParse($cells[1], [ref] $line) -or
        $line -le 0 -or [string]::IsNullOrWhiteSpace($cells[0]) -or
        [string]::IsNullOrWhiteSpace($cells[2]) -or
        [string]::IsNullOrWhiteSpace($cells[3]) -or
        [string]::IsNullOrWhiteSpace($cells[4]) -or
        [string]::IsNullOrWhiteSpace($cells[5])) {
      $malformed++
      Write-Output "MALFORMED_TRACKED_INDEX_ROW=$($lines[$i])"
      continue
    }
    $declarations += [pscustomobject]@{
      Path = $cells[0]
      Line = $line
      Family = $cells[2]
      Kind = $cells[3]
      Declaration = $cells[4]
      Visibility = $cells[5]
    }
  }
  return [pscustomobject]@{
    Declarations = @($declarations | Sort-Object Path, Line)
    Malformed = $malformed
  }
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
if ($TrackedIndexOnly -and $UpdateIndex) {
  throw '-TrackedIndexOnly cannot regenerate the index; use the full audit with -UpdateIndex'
}
$allowedRecovery = @('partial', 'not-started', 'retired-open',
  'out-of-scope', 'frontier', 'complete')
$unknownRecovery = @($scopes |
  Where-Object { $allowedRecovery -notcontains $_.Recovery }).Count
$recoveryConflicts = @($scopes | Group-Object Family | Where-Object {
  @($_.Group | Select-Object -ExpandProperty Recovery -Unique).Count -ne 1
}).Count
$missingOwners = 0
$duplicateOwners = 0
$trackedIndexMalformed = 0
if ($TrackedIndexOnly) {
  $trackedIndex = Read-TrackedIndex
  $declarations = $trackedIndex.Declarations
  $trackedIndexMalformed = $trackedIndex.Malformed
  $pinnedFiles = @($declarations | Select-Object -ExpandProperty Path -Unique)
  $indexCurrent = $null
} else {
  $pinnedFiles = Get-PinnedFiles
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
}

$familyIds = @($scopes | Select-Object -ExpandProperty Family -Unique)
$unknownTrackedIndexFamilies = @($declarations | Where-Object {
  $_.Family -notin $familyIds
}).Count
$trackedIndexScopeMismatches = 0
if ($TrackedIndexOnly) {
  foreach ($indexedPath in @($declarations | Group-Object Path)) {
    $owners = @(Get-Owners $indexedPath.Name $scopes)
    $storedFamilies = @($indexedPath.Group | Select-Object -ExpandProperty Family -Unique)
    if ($owners.Count -ne 1 -or $storedFamilies.Count -ne 1 -or
        ($owners.Count -eq 1 -and $storedFamilies.Count -eq 1 -and
         $owners[0].Family -ne $storedFamilies[0])) {
      $trackedIndexScopeMismatches++
      $ownerText = @($owners | Select-Object -ExpandProperty Family) -join ','
      $storedText = $storedFamilies -join ','
      Write-Output "TRACKED_INDEX_SCOPE_MISMATCH=$($indexedPath.Name):" +
        "owners=$ownerText:stored=$storedText"
    }
  }
}
$ledgerIndex = Read-LedgerRows $pinnedFiles
$matchedRows = @()
$missingDeclarations = 0
foreach ($row in $ledgerIndex.Rows) {
  if ($null -eq $row.Path) { continue }
  $declaration = $row.Declaration
  $lineNumber = $null
  $qualified = [regex]::Match($declaration, '^(?<name>.+)@(?<line>[0-9]+)$')
  if ($qualified.Success) {
    $declaration = $qualified.Groups['name'].Value
    $lineNumber = [int] $qualified.Groups['line'].Value
  }
  $pathCandidates = @($declarations | Where-Object {
    $_.Path -eq $row.Path -and
      ($null -eq $lineNumber -or $_.Line -eq $lineNumber)
  })
  $exactCandidates = @($pathCandidates | Where-Object {
    $_.Declaration -ceq $declaration
  })
  $candidates = if ($exactCandidates.Count -gt 0) {
    $exactCandidates
  } else {
    @($pathCandidates | Where-Object {
      $_.Declaration.EndsWith(".$declaration", [StringComparison]::Ordinal) -or
      $declaration.EndsWith(".$($_.Declaration)", [StringComparison]::Ordinal)
    })
  }
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

$capabilityPath = Join-Path $RepoRoot 'docs/V1CapabilityMatrix.md'
$capabilityText = [IO.File]::ReadAllText($capabilityPath)
$allowedCapabilityVerdicts = @(
  'better',
  'comparable',
  'partial',
  'critical gap',
  'deliberately retired or out of scope')
$capabilityRows = @()
$unknownCapabilityVerdicts = 0
$malformedCapabilityRows = 0
$capabilityFamilyEvidence = @()
foreach ($line in [IO.File]::ReadAllLines($capabilityPath)) {
  $tableLine = $line.TrimStart()
  if (-not $tableLine.StartsWith('|')) { continue }
  $cells = $tableLine.Split('|')
  if ($cells.Count -ne 7) {
    $malformedCapabilityRows++
    Write-Output "MALFORMED_CAPABILITY_ROW=$tableLine"
    continue
  }
  $verdict = $cells[4].Trim()
  if ($verdict -eq 'Verdict' -or $verdict -match '^[-:]+$') { continue }
  if ($verdict -notin $allowedCapabilityVerdicts) {
    $unknownCapabilityVerdicts++
    Write-Output "UNKNOWN_CAPABILITY_VERDICT=$verdict`:$tableLine"
    continue
  }
  $capabilityRows += [pscustomobject]@{
    Verdict = $verdict
    FamilyEvidence = $cells[2].Trim()
  }
  $capabilityFamilyEvidence += $cells[2].Trim()
}

$capabilityFamilyText = $capabilityFamilyEvidence -join "`n"
$familiesMissingFromCapabilities = @($familyIds | Where-Object {
  $capabilityFamilyText -notmatch
    "(?<![A-Z0-9-])$([regex]::Escape($_))(?![A-Z0-9-])"
})
foreach ($family in $familiesMissingFromCapabilities) {
  Write-Output "FAMILY_ID_MISSING_FROM_CAPABILITIES=$family"
}

$capabilityCounts = [ordered]@{}
foreach ($verdict in $allowedCapabilityVerdicts) {
  $capabilityCounts[$verdict] = @($capabilityRows | Where-Object {
    $_.Verdict -eq $verdict
  }).Count
}
$dashboardPattern =
  'The (?<rows>\d+) workflow rows below contain (?<better>\d+) better, ' +
  '(?<comparable>\d+) comparable, and (?<partial>\d+) partial\s+' +
  'verdicts; (?<critical>\d+) (?:are critical gaps|is a critical gap) and ' +
  '(?<retired>\d+) are deliberately'
$dashboard = [regex]::Match($capabilityText, $dashboardPattern)
$capabilityDashboardMismatch = if (-not $dashboard.Success) { 1 } elseif (
  [int] $dashboard.Groups['rows'].Value -ne $capabilityRows.Count -or
  [int] $dashboard.Groups['better'].Value -ne $capabilityCounts['better'] -or
  [int] $dashboard.Groups['comparable'].Value -ne $capabilityCounts['comparable'] -or
  [int] $dashboard.Groups['partial'].Value -ne $capabilityCounts['partial'] -or
  [int] $dashboard.Groups['critical'].Value -ne $capabilityCounts['critical gap'] -or
  [int] $dashboard.Groups['retired'].Value -ne
    $capabilityCounts['deliberately retired or out of scope']) { 1 } else { 0 }

if ($TrackedIndexOnly) {
  # These are properties of the committed index, not a measurement of the
  # ignored source snapshot.  Do not present this mode as a full coverage run.
  Report 'TRACKED_INDEX_ONLY' 1
  Report 'TRACKED_INDEX_FILES' $pinnedFiles.Count
  Report 'TRACKED_INDEX_DECLARATIONS' $declarations.Count
  Report 'MALFORMED_TRACKED_INDEX' $trackedIndexMalformed
  Report 'UNKNOWN_TRACKED_INDEX_FAMILIES' $unknownTrackedIndexFamilies
  Report 'TRACKED_INDEX_SCOPE_MISMATCHES' $trackedIndexScopeMismatches
  Report 'PINNED_SOURCE_FILE_OWNERSHIP_SKIPPED' 1
  Report 'SOURCE_FILES_WITHOUT_INDEXED_DECLARATIONS_NOT_CHECKED' 1
  Report 'GENERATED_INDEX_FRESHNESS_SKIPPED' 1
} else {
  Report 'PINNED_FILES' $pinnedFiles.Count
  Report 'PINNED_DECLARATIONS' $declarations.Count
}
Report 'FAMILY_SCOPE_RULES' $scopes.Count
Report 'FAMILY_IDS' $familyIds.Count
Report 'UNKNOWN_FAMILY_RECOVERY' $unknownRecovery
Report 'FAMILY_RECOVERY_CONFLICTS' $recoveryConflicts
Report 'FAMILY_IDS_MISSING_FROM_LEDGER' ($familyIds.Count - $ledgerFamilies.Count)
Report 'FAMILY_IDS_MISSING_FROM_CAPABILITIES' `
  $familiesMissingFromCapabilities.Count
if (-not $TrackedIndexOnly) {
  Report 'PINNED_FILES_WITHOUT_OWNER' $missingOwners
  Report 'PINNED_FILES_WITH_DUPLICATE_OWNER' $duplicateOwners
  Report 'GENERATED_INDEX_CURRENT' $indexCurrent
}
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
Report 'CAPABILITY_ROWS' $capabilityRows.Count
Report 'UNKNOWN_CAPABILITY_VERDICTS' $unknownCapabilityVerdicts
Report 'MALFORMED_CAPABILITY_ROWS' $malformedCapabilityRows
Report 'CAPABILITY_DASHBOARD_MISMATCH' $capabilityDashboardMismatch
foreach ($issue in $ledgerIndex.Issues.UnknownDispositionRows) {
  Write-Output "UNKNOWN_DISPOSITION_ROW=$issue"
}
foreach ($issue in $ledgerIndex.Issues.MissingPathRows) {
  Write-Output "MISSING_LEDGER_PATH_ROW=$issue"
}

if ($VerifyExpected) {
  $expectedZero = @(
    'FAMILY_IDS_MISSING_FROM_LEDGER',
    'FAMILY_IDS_MISSING_FROM_CAPABILITIES',
    'UNKNOWN_FAMILY_RECOVERY',
    'FAMILY_RECOVERY_CONFLICTS',
    'UNKNOWN_DISPOSITIONS',
    'MISSING_LEDGER_PATHS',
    'MISSING_LEDGER_DECLARATIONS',
    'DUPLICATE_LEDGER_DECLARATIONS',
    'COMPLETE_LEDGER_OPEN_ROWS',
    'COMPLETE_FAMILIES_WITH_OPEN_DECLARATIONS',
    'UNKNOWN_CAPABILITY_VERDICTS',
    'MALFORMED_CAPABILITY_ROWS',
    'CAPABILITY_DASHBOARD_MISMATCH')
  if ($TrackedIndexOnly) {
    $expectedZero += @(
      'MALFORMED_TRACKED_INDEX',
      'UNKNOWN_TRACKED_INDEX_FAMILIES',
      'TRACKED_INDEX_SCOPE_MISMATCHES')
  } else {
    $expectedZero += @(
      'PINNED_FILES_WITHOUT_OWNER',
      'PINNED_FILES_WITH_DUPLICATE_OWNER')
  }
  foreach ($key in $expectedZero) {
    if ($Results[$key] -ne 0) {
      throw "$key expected 0, got $($Results[$key])"
    }
  }
  if (-not $TrackedIndexOnly -and $Results['GENERATED_INDEX_CURRENT'] -ne 1) {
    throw 'Generated declaration index is stale; run with -UpdateIndex'
  }
  if ($TrackedIndexOnly -and
      ($Results['PINNED_SOURCE_FILE_OWNERSHIP_SKIPPED'] -ne 1 -or
       $Results['SOURCE_FILES_WITHOUT_INDEXED_DECLARATIONS_NOT_CHECKED'] -ne 1 -or
       $Results['GENERATED_INDEX_FRESHNESS_SKIPPED'] -ne 1)) {
    throw 'Tracked-index mode must explicitly report its source-snapshot limits'
  }
  Write-Output 'VERIFIED=1'
}
