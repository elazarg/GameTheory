param(
  [string] $SnapshotRoot = (Join-Path $PSScriptRoot '..\reference\GameTheory-v1'),
  [switch] $VerifyExpected
)

$ErrorActionPreference = 'Stop'

$SnapshotRoot = (Resolve-Path $SnapshotRoot).Path
$GameTheoryRoot = Join-Path $SnapshotRoot 'GameTheory'
$MathRoot = Join-Path $SnapshotRoot 'Math'

function Get-LeanFiles([string] $Root) {
  $files = @(& rg --files $Root -g '*.lean')
  if ($LASTEXITCODE -ne 0) {
    throw "rg failed while enumerating $Root"
  }
  return $files
}

function Measure-Corpus([string[]] $Files) {
  $nonblank = 0
  foreach ($file in $Files) {
    $nonblank += ([IO.File]::ReadAllLines($file) |
        Where-Object { $_.Trim().Length -gt 0 }).Count
  }
  return [pscustomobject]@{
    Files = $Files.Count
    NonblankLines = $nonblank
  }
}

function Measure-FileNonblank([string] $RelativePath) {
  $path = Join-Path $SnapshotRoot $RelativePath
  return ([IO.File]::ReadAllLines($path) |
      Where-Object { $_.Trim().Length -gt 0 }).Count
}

function Count-FilesContaining(
    [string[]] $Files,
    [string] $Pattern) {
  $count = 0
  foreach ($file in $Files) {
    if ([regex]::IsMatch([IO.File]::ReadAllText($file), $Pattern)) {
      $count++
    }
  }
  return $count
}

function Remove-LeanCommentsAndStrings([string] $Source) {
  $result = [Text.StringBuilder]::new()
  $commentDepth = 0
  $inString = $false
  $escaped = $false

  for ($index = 0; $index -lt $Source.Length; $index++) {
    $char = $Source[$index]
    $next = if ($index + 1 -lt $Source.Length) {
      $Source[$index + 1]
    } else {
      [char] 0
    }

    if ($commentDepth -gt 0) {
      if ($char -eq '/' -and $next -eq '-') {
        $commentDepth++
        $index++
      } elseif ($char -eq '-' -and $next -eq '/') {
        $commentDepth--
        $index++
      } elseif ($char -eq "`n") {
        [void] $result.Append("`n")
      }
      continue
    }

    if ($inString) {
      if ($escaped) {
        $escaped = $false
      } elseif ($char -eq '\') {
        $escaped = $true
      } elseif ($char -eq '"') {
        $inString = $false
      } elseif ($char -eq "`n") {
        $inString = $false
        [void] $result.Append("`n")
      }
      continue
    }

    if ($char -eq '/' -and $next -eq '-') {
      $commentDepth = 1
      $index++
    } elseif ($char -eq '-' -and $next -eq '-') {
      while ($index -lt $Source.Length -and $Source[$index] -ne "`n") {
        $index++
      }
      [void] $result.Append("`n")
    } elseif ($char -eq '"') {
      $inString = $true
    } else {
      [void] $result.Append($char)
    }
  }

  return $result.ToString()
}

function Measure-CodePattern(
    [string[]] $Files,
    [string] $Pattern) {
  $total = 0
  $perFile = @()
  foreach ($file in $Files) {
    $source = [IO.File]::ReadAllText($file).Replace("`r", '')
    $code = Remove-LeanCommentsAndStrings $source
    $count = [regex]::Matches($code, $Pattern).Count
    if ($count -gt 0) {
      $total += $count
      $perFile += [pscustomobject]@{ File = $file; Count = $count }
    }
  }
  return [pscustomobject]@{
    Files = $perFile.Count
    Occurrences = $total
    PerFile = @($perFile | Sort-Object `
        @{ Expression = 'Count'; Descending = $true }, File)
  }
}

function Count-MatchingLines(
    [string[]] $Files,
    [string] $Pattern) {
  $count = 0
  foreach ($file in $Files) {
    foreach ($line in [IO.File]::ReadAllLines($file)) {
      if ($line -match $Pattern) {
        $count++
      }
    }
  }
  return $count
}

function Resolve-SnapshotImport([string] $Module) {
  $relative = ($Module -replace '\.', [IO.Path]::DirectorySeparatorChar) + '.lean'
  $path = Join-Path $SnapshotRoot $relative
  if (Test-Path $path) {
    return (Resolve-Path $path).Path
  }
  return $null
}

function Measure-ImportClosure([string] $RelativePath) {
  $start = (Resolve-Path (Join-Path $SnapshotRoot $RelativePath)).Path
  $queue = [Collections.Generic.Queue[string]]::new()
  $seen = [Collections.Generic.HashSet[string]]::new()
  $queue.Enqueue($start)

  while ($queue.Count -gt 0) {
    $path = $queue.Dequeue()
    if (-not $seen.Add($path)) {
      continue
    }
    foreach ($line in [IO.File]::ReadAllLines($path)) {
      if ($line -match '^import\s+(.+?)\s*$') {
        foreach ($module in ($Matches[1] -split '\s+')) {
          $dependency = Resolve-SnapshotImport $module
          if ($null -ne $dependency) {
            $queue.Enqueue($dependency)
          }
        }
      }
    }
  }

  $nonblank = 0
  foreach ($path in $seen) {
    $nonblank += ([IO.File]::ReadAllLines($path) |
        Where-Object { $_.Trim().Length -gt 0 }).Count
  }
  return [pscustomobject]@{ Files = $seen.Count; NonblankLines = $nonblank }
}

function Measure-Declaration(
    [string] $RelativePath,
    [string] $Name) {
  $path = Join-Path $SnapshotRoot $RelativePath
  $lines = [IO.File]::ReadAllLines($path)
  $declarationPattern =
    '^(?:@\[[^]]+\]\s*)?(?:(?:private|noncomputable)\s+)*' +
    '(?:theorem|def|structure|abbrev|class)\s+'
  $namePattern = '\b' + [regex]::Escape($Name) + '\b'
  $start = -1

  for ($index = 0; $index -lt $lines.Count; $index++) {
    if ($lines[$index] -match $declarationPattern -and
        $lines[$index] -match $namePattern) {
      $start = $index
      break
    }
  }
  if ($start -lt 0) {
    throw "Declaration $Name not found in $RelativePath"
  }

  $end = $lines.Count
  for ($index = $start + 1; $index -lt $lines.Count; $index++) {
    if ($lines[$index] -match $declarationPattern) {
      $end = $index
      break
    }
  }
  $nonblank = ($lines[$start..($end - 1)] |
      Where-Object { $_.Trim().Length -gt 0 }).Count
  return [pscustomobject]@{
    Name = $Name
    File = $RelativePath
    Line = $start + 1
    NonblankLines = $nonblank
  }
}

function Add-Result(
    [Collections.Specialized.OrderedDictionary] $Results,
    [string] $Name,
    [int] $Value) {
  $Results.Add($Name, $Value)
  Write-Output ("{0}={1}" -f $Name, $Value)
}

$gameFiles = @(Get-LeanFiles $GameTheoryRoot)
$mathFiles = @(Get-LeanFiles $MathRoot)
$allFiles = @($gameFiles + $mathFiles)
$languageFiles = @(Get-LeanFiles (Join-Path $GameTheoryRoot 'Languages'))
$bridgeFiles = @(Get-LeanFiles (Join-Path $GameTheoryRoot 'Languages\Bridges'))
$transportFiles = @(Get-LeanFiles (Join-Path $GameTheoryRoot 'Concepts\Transport'))

$gameCorpus = Measure-Corpus $gameFiles
$mathCorpus = Measure-Corpus $mathFiles
$fullCorpus = Measure-Corpus $allFiles
$bridgeCorpus = Measure-Corpus $bridgeFiles
$transportCorpus = Measure-Corpus $transportFiles

$gameMorphismRelative = @(
  'GameTheory\Core\GameMorphism.lean',
  'GameTheory\Concepts\Foundations\GameMorphism.lean',
  'GameTheory\Concepts\Mixed\GameMorphism.lean',
  'GameTheory\Concepts\Correlation\GameMorphism.lean',
  'GameTheory\Concepts\Potential\GameMorphism.lean'
)
$gameMorphismFiles = @($gameMorphismRelative | ForEach-Object {
    Join-Path $SnapshotRoot $_
  })
$gameMorphismCorpus = Measure-Corpus $gameMorphismFiles

$castMeasure = Measure-CodePattern $languageFiles `
  '(?<![A-Za-z0-9_])cast(?![A-Za-z0-9_])|Eq\.ndrec'

$results = [ordered]@{}
Add-Result $results 'GAME_FILES' $gameCorpus.Files
Add-Result $results 'GAME_NONBLANK' $gameCorpus.NonblankLines
Add-Result $results 'MATH_FILES' $mathCorpus.Files
Add-Result $results 'MATH_NONBLANK' $mathCorpus.NonblankLines
Add-Result $results 'FULL_FILES' $fullCorpus.Files
Add-Result $results 'FULL_NONBLANK' $fullCorpus.NonblankLines
Add-Result $results 'GAME_FILES_MENTIONING_KERNELGAME' `
  (Count-FilesContaining $gameFiles '\bKernelGame\b')
Add-Result $results 'GAME_FILES_MENTIONING_GAMEFORM' `
  (Count-FilesContaining $gameFiles '\bGameForm\b')
Add-Result $results 'LANGUAGE_FILES_MENTIONING_KERNELGAME' `
  (Count-FilesContaining $languageFiles '\bKernelGame\b')
Add-Result $results 'BRIDGE_FILES' $bridgeCorpus.Files
Add-Result $results 'BRIDGE_NONBLANK' $bridgeCorpus.NonblankLines
Add-Result $results 'GAMEFORM_NONBLANK' `
  (Measure-FileNonblank 'GameTheory\Core\GameForm.lean')
Add-Result $results 'KERNELGAME_NONBLANK' `
  (Measure-FileNonblank 'GameTheory\Core\KernelGame.lean')
Add-Result $results 'T1_EFG_NFG_NONBLANK' `
  (Measure-FileNonblank 'GameTheory\Languages\Bridges\EFG_NFG.lean')
Add-Result $results 'T2_EFG_KUHN_NONBLANK' `
  (Measure-FileNonblank 'GameTheory\Languages\EFG\Kuhn.lean')
Add-Result $results 'T3_MAID_EFG_NONBLANK' `
  (Measure-FileNonblank 'GameTheory\Languages\Bridges\MAID_EFG.lean')
Add-Result $results 'T4_NFG_FOSG_NONBLANK' `
  (Measure-FileNonblank 'GameTheory\Languages\Bridges\NFG_FOSG.lean')
Add-Result $results 'LANGUAGE_CODE_TRANSPORT_FILES' $castMeasure.Files
Add-Result $results 'LANGUAGE_CODE_TRANSPORT_OCCURRENCES' $castMeasure.Occurrences
Add-Result $results 'TRANSPORT_FILES' $transportCorpus.Files
Add-Result $results 'TRANSPORT_NONBLANK' $transportCorpus.NonblankLines
Add-Result $results 'GAMEMORPHISM_FILES' $gameMorphismCorpus.Files
Add-Result $results 'GAMEMORPHISM_NONBLANK' $gameMorphismCorpus.NonblankLines
Add-Result $results 'BRIDGE_MORPHISM_DEFS' `
  (Count-MatchingLines $bridgeFiles `
    '^(?:noncomputable )?def .*morphism|^(?:noncomputable )?def .*Morphism')
Add-Result $results 'BRIDGE_BISIMULATION_DEFS' `
  (Count-MatchingLines $bridgeFiles `
    '^(?:noncomputable )?def .*bisimulation|^(?:noncomputable )?def .*Bisimulation')
Add-Result $results 'LANGUAGE_GAMEFORM_TRANSPORT_COMPOSITIONS' `
  (Count-MatchingLines $languageFiles `
    'Transport\.comp|\.compSameMiddle|\.compOfHom')
Add-Result $results 'LANGUAGE_KERNEL_COMPOSITIONS' `
  (Count-MatchingLines $languageFiles `
    'KernelGame\.(Morphism|Simulation|Bisimulation)\.comp')

Write-Output 'TRANSPORT_OCCURRENCES_BY_FILE'
foreach ($entry in $castMeasure.PerFile) {
  $relative = [IO.Path]::GetRelativePath($SnapshotRoot, $entry.File).Replace('\', '/')
  Write-Output ("{0}={1}" -f $relative, $entry.Count)
}

$closures = [ordered]@{
  KERNELGAME = 'GameTheory\Core\KernelGame.lean'
  T1_EFG_NFG = 'GameTheory\Languages\Bridges\EFG_NFG.lean'
  T2_EFG_KUHN = 'GameTheory\Languages\EFG\Kuhn.lean'
  T3_MAID_EFG = 'GameTheory\Languages\Bridges\MAID_EFG.lean'
  T4_NFG_FOSG = 'GameTheory\Languages\Bridges\NFG_FOSG.lean'
}
foreach ($entry in $closures.GetEnumerator()) {
  $measure = Measure-ImportClosure $entry.Value
  Add-Result $results ($entry.Name + '_CLOSURE_FILES') $measure.Files
  Add-Result $results ($entry.Name + '_CLOSURE_NONBLANK') $measure.NonblankLines
}

$declarations = @(
  @('GameTheory\Languages\Bridges\EFG_NFG.lean', 'EFGGame.toNFGGame_eu', 8),
  @('GameTheory\Languages\Bridges\EFG_NFG.lean', 'EFGGame.toNFGGameDet_morphism', 12),
  @('GameTheory\Languages\EFG\Kuhn.lean', 'kuhn_behavioral_to_mixed_udist', 9),
  @('GameTheory\Languages\EFG\Kuhn.lean', 'kuhn_mixed_to_behavioral_udist', 11),
  @('GameTheory\Languages\EFG\Kuhn.lean', 'kuhn_mixed_to_behavioral_core', 31),
  @('GameTheory\Languages\EFG\Kuhn.lean', 'compiledCore_runEq_to_evalDistEq', 98),
  @('GameTheory\Languages\Bridges\MAID_EFG.lean', 'maidToEFGAt_outcomeKernel', 8),
  @('GameTheory\Languages\Bridges\MAID_EFG.lean', 'maidToEFGAt_udist', 12),
  @('GameTheory\Languages\Bridges\MAID_EFG.lean', 'maidToEFGAt_bisimulation', 20),
  @('GameTheory\Languages\Bridges\MAID_EFG.lean', 'maidToEFGAt_morphism', 25),
  @('GameTheory\Languages\Bridges\NFG_FOSG.lean', 'toFOSG_udist_eq', 21),
  @('GameTheory\Languages\Bridges\NFG_FOSG.lean', 'toFOSG_morphism', 9)
)
Write-Output 'DECLARATION_NONBLANK_LINES'
foreach ($declaration in $declarations) {
  $measure = Measure-Declaration $declaration[0] $declaration[1]
  Write-Output ("{0}|{1}:{2}|nonblank={3}" -f
      $measure.Name, $measure.File, $measure.Line, $measure.NonblankLines)
  if ($VerifyExpected -and $measure.NonblankLines -ne $declaration[2]) {
    throw ("{0}: expected {1} nonblank lines, measured {2}" -f
        $measure.Name, $declaration[2], $measure.NonblankLines)
  }
}

if ($VerifyExpected) {
  $expected = [ordered]@{
    GAME_FILES = 380
    GAME_NONBLANK = 99301
    MATH_FILES = 56
    MATH_NONBLANK = 17793
    FULL_FILES = 436
    FULL_NONBLANK = 117094
    GAME_FILES_MENTIONING_KERNELGAME = 187
    GAME_FILES_MENTIONING_GAMEFORM = 38
    LANGUAGE_FILES_MENTIONING_KERNELGAME = 47
    BRIDGE_FILES = 14
    BRIDGE_NONBLANK = 6243
    GAMEFORM_NONBLANK = 259
    KERNELGAME_NONBLANK = 197
    T1_EFG_NFG_NONBLANK = 75
    T2_EFG_KUHN_NONBLANK = 308
    T3_MAID_EFG_NONBLANK = 981
    T4_NFG_FOSG_NONBLANK = 374
    LANGUAGE_CODE_TRANSPORT_FILES = 12
    LANGUAGE_CODE_TRANSPORT_OCCURRENCES = 84
    TRANSPORT_FILES = 15
    TRANSPORT_NONBLANK = 3210
    GAMEMORPHISM_FILES = 5
    GAMEMORPHISM_NONBLANK = 1015
    BRIDGE_MORPHISM_DEFS = 4
    BRIDGE_BISIMULATION_DEFS = 7
    LANGUAGE_GAMEFORM_TRANSPORT_COMPOSITIONS = 0
    LANGUAGE_KERNEL_COMPOSITIONS = 3
    KERNELGAME_CLOSURE_FILES = 12
    KERNELGAME_CLOSURE_NONBLANK = 4934
    T1_EFG_NFG_CLOSURE_FILES = 23
    T1_EFG_NFG_CLOSURE_NONBLANK = 7269
    T2_EFG_KUHN_CLOSURE_FILES = 38
    T2_EFG_KUHN_CLOSURE_NONBLANK = 12942
    T3_MAID_EFG_CLOSURE_FILES = 46
    T3_MAID_EFG_CLOSURE_NONBLANK = 15903
    T4_NFG_FOSG_CLOSURE_FILES = 31
    T4_NFG_FOSG_CLOSURE_NONBLANK = 11031
  }
  foreach ($entry in $expected.GetEnumerator()) {
    if ($results[$entry.Name] -ne $entry.Value) {
      throw ("{0}: expected {1}, measured {2}" -f
          $entry.Name, $entry.Value, $results[$entry.Name])
    }
  }
  $expectedTransportFiles = [ordered]@{
    'GameTheory/Languages/Bridges/OpenGame_MAID.lean' = 23
    'GameTheory/Languages/EFG/CompileObsFacts.lean' = 17
    'GameTheory/Languages/Bridges/FOSG/AugmentedEFG.lean' = 16
    'GameTheory/Languages/MultiRound/CompileObsLinAdequacy.lean' = 14
  }
  $actualTransportFiles = @{}
  foreach ($entry in $castMeasure.PerFile) {
    $relative = [IO.Path]::GetRelativePath($SnapshotRoot, $entry.File).Replace('\', '/')
    $actualTransportFiles[$relative] = $entry.Count
  }
  foreach ($entry in $expectedTransportFiles.GetEnumerator()) {
    if ($actualTransportFiles[$entry.Name] -ne $entry.Value) {
      throw ("{0}: expected {1} transport tokens, measured {2}" -f
          $entry.Name, $entry.Value, $actualTransportFiles[$entry.Name])
    }
  }
  Write-Output 'EXPECTED_MEASUREMENTS=ok'
}
