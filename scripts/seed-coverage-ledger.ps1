param(
  [Parameter(Mandatory = $true)]
  [string] $FamilyId,

  [Parameter(Mandatory = $true)]
  [string] $OutputName,

  [Parameter(Mandatory = $true)]
  [string] $Title,

  [Parameter(Mandatory = $true)]
  [string] $CanonicalDestination,

  [Parameter(Mandatory = $true)]
  [string] $DomainContract,

  [Parameter(Mandatory = $true)]
  [string] $Owner,

  [string] $LastVerified = (Get-Date -Format 'yyyy-MM-dd')
)

$ErrorActionPreference = 'Stop'
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$CoverageRoot = (Resolve-Path (Join-Path $RepoRoot 'docs/coverage')).Path
$IndexPath = Join-Path $CoverageRoot 'PinnedDeclarations.tsv'
$PinnedCommit = 'a3d8c67ed91d58e197b8c978ddcc00ba96f87c29'

if (-not $OutputName.EndsWith('.md')) {
  throw 'OutputName must end in .md'
}
$OutputPath = [IO.Path]::GetFullPath((Join-Path $CoverageRoot $OutputName))
$coveragePrefix = $CoverageRoot.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
if (-not $OutputPath.StartsWith($coveragePrefix, [StringComparison]::OrdinalIgnoreCase)) {
  throw "Output path escapes docs/coverage: $OutputPath"
}
if (Test-Path -LiteralPath $OutputPath) {
  throw "Refusing to overwrite existing ledger: $OutputPath"
}

function Strip-Code([string] $Cell) {
  $value = $Cell.Trim()
  if ($value.StartsWith('`') -and $value.EndsWith('`') -and $value.Length -ge 2) {
    return $value.Substring(1, $value.Length - 2)
  }
  return $value
}

function Resolve-Declaration([string] $PathCell, [string] $DeclarationCell, $Rows) {
  $path = Strip-Code $PathCell
  $declaration = Strip-Code $DeclarationCell
  $lineNumber = $null
  $qualified = [regex]::Match($declaration, '^(?<name>.+)@(?<line>[0-9]+)$')
  if ($qualified.Success) {
    $declaration = $qualified.Groups['name'].Value
    $lineNumber = [int] $qualified.Groups['line'].Value
  }
  $pathCandidates = @($Rows | Where-Object {
    ($_.path -eq $path -or $_.path.EndsWith("/$path")) -and
      ($null -eq $lineNumber -or [int] $_.line -eq $lineNumber)
  })
  $exactCandidates = @($pathCandidates | Where-Object {
    $_.declaration -ceq $declaration
  })
  $candidates = if ($exactCandidates.Count -gt 0) {
    $exactCandidates
  } else {
    @($pathCandidates | Where-Object {
      $_.declaration.EndsWith(".$declaration", [StringComparison]::Ordinal) -or
      $declaration.EndsWith(".$($_.declaration)", [StringComparison]::Ordinal)
    })
  }
  if ($candidates.Count -eq 1) {
    return "$($candidates[0].path)`t$($candidates[0].line)"
  }
  return $null
}

$allRows = @(Import-Csv $IndexPath -Delimiter "`t")
$familyRows = @($allRows | Where-Object { $_.family_id -eq $FamilyId } |
  Sort-Object path, { [int] $_.line })
if ($familyRows.Count -eq 0) {
  throw "No declarations found for family $FamilyId"
}

$accounted = [Collections.Generic.HashSet[string]]::new(
  [StringComparer]::Ordinal)
foreach ($ledger in Get-ChildItem $CoverageRoot -Filter '*.md' |
    Where-Object { $_.Name -ne 'README.md' }) {
  $currentPath = $null
  foreach ($line in [IO.File]::ReadAllLines($ledger.FullName)) {
    if (-not $line.StartsWith('|')) { continue }
    $cells = @($line.Split('|') | Select-Object -Skip 1 |
      Select-Object -First 7 | ForEach-Object { $_.Trim() })
    if ($cells.Count -ne 7 -or $cells[0] -in @('Pinned path', '---')) {
      continue
    }
    if ($cells[0] -ne 'same') {
      $currentPath = $cells[0]
    }
    if ($null -eq $currentPath) { continue }
    $key = Resolve-Declaration $currentPath $cells[1] $allRows
    if ($null -ne $key) {
      [void] $accounted.Add($key)
    }
  }
}

$unaccounted = @($familyRows | Where-Object {
  -not $accounted.Contains("$($_.path)`t$($_.line)")
})
$nameCounts = [Collections.Generic.Dictionary[string, int]]::new(
  [StringComparer]::Ordinal)
foreach ($row in $familyRows) {
  $key = "$($row.path)`t$($row.declaration)"
  if ($nameCounts.ContainsKey($key)) {
    $nameCounts[$key]++
  } else {
    $nameCounts[$key] = 1
  }
}
$duplicateNames = [Collections.Generic.HashSet[string]]::new(
  [StringComparer]::Ordinal)
foreach ($entry in $nameCounts.GetEnumerator()) {
  if ($entry.Value -gt 1) {
    [void] $duplicateNames.Add($entry.Key)
  }
}
$roots = @($familyRows | Select-Object -ExpandProperty path -Unique)
$baseline = (& git -C $RepoRoot rev-parse --short HEAD).Trim()

$lines = [Collections.Generic.List[string]]::new()
$lines.Add("# ${FamilyId}: $Title")
$lines.Add('')
$lines.Add("Title: $Title")
$lines.Add("Family ID: $FamilyId")
$lines.Add('Pinned roots: ' + (($roots | ForEach-Object { "``$_``" }) -join '; '))
$lines.Add("Pinned commit: ``$PinnedCommit``")
$lines.Add("Successor baseline: ``$baseline``")
$lines.Add("Canonical destination: $CanonicalDestination")
$lines.Add("Domain contract / decision: $DomainContract")
$lines.Add("Owner: $Owner")
$lines.Add('Status: in progress; exact seed, classification pending')
$lines.Add("Last verified: $LastVerified")
$lines.Add('')
$lines.Add("This ledger is an exact generated review queue for the $FamilyId family.")
$lines.Add("$($familyRows.Count - $unaccounted.Count) declarations are already accounted for in")
$lines.Add('earlier bounded ledgers and are not duplicated here. Every row below is')
$lines.Add('deliberately `unreviewed`: the generated index supplies spelling, location,')
$lines.Add('kind, and visibility only. It does not infer a mathematical disposition.')
$lines.Add('')
$lines.Add('| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |')
$lines.Add('|---|---|---|---|---|---|---|')

$previousPath = $null
foreach ($row in $unaccounted) {
  $pathCell = if ($row.path -eq $previousPath) { 'same' } else { "``$($row.path)``" }
  $previousPath = $row.path
  $declaration = if ($duplicateNames.Contains(
      "$($row.path)`t$($row.declaration)")) {
    "$($row.declaration)@$($row.line)"
  } else {
    $row.declaration
  }
  $lines.Add("| $pathCell | ``$declaration`` | $($row.kind) | unreviewed | review required | generated index seed only | $($row.visibility), pinned line $($row.line) |")
}

$lines.Add('')
$lines.Add('Before this ledger can become complete, each row must be reviewed against')
$lines.Add('the canonical successor API and assigned an allowed non-`unreviewed`')
$lines.Add('disposition with concrete build, theorem, decision, or counterexample')
$lines.Add('evidence. Generated name similarity is never sufficient.')
$content = ($lines -join "`n") + "`n"
[IO.File]::WriteAllText($OutputPath, $content, [Text.UTF8Encoding]::new($false))

Write-Output "FAMILY_ID=$FamilyId"
Write-Output "FAMILY_DECLARATIONS=$($familyRows.Count)"
Write-Output "ALREADY_ACCOUNTED=$($familyRows.Count - $unaccounted.Count)"
Write-Output "SEEDED_UNREVIEWED=$($unaccounted.Count)"
Write-Output "OUTPUT=$OutputPath"
