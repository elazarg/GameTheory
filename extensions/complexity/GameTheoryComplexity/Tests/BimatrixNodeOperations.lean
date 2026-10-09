import GameTheoryComplexity.Backend.BimatrixNodeOperations

namespace GameTheory.Complexity.Backend.Tests.BimatrixNodeOperations
open GameTheory.Complexity.Backend

-- The all-slack source exchanges its slack for the dropped payoff variable.
example : bimatrixNodeExchangeWord ![[true], [false, false, false, false], [], [false]] =
    [true, true, true, true] := by decide

-- The opposite exchange restores both source fields.
example : bimatrixNodeExchangeWord ![[false], [true, true, true, true], [true], []] =
    [false, false, false, false] := by decide

-- Clearing takes priority when a malformed request names the same variable twice.
example : bimatrixNodeExchangeWord ![[true], [false, false, false, false], [], []] =
    [true, false, true, true] := by decide

-- A duplicated nonzero label switches from its slack port to its payoff port.
example : bimatrixNodeSwitchWord
    ![[false, true], [false, true, true, false, false, true, true, false], [false, true]] =
    [false, true, true, false, false, true, false, true] := by decide

-- Switching the twin restores the original entering field.
example : bimatrixNodeSwitchWord
    ![[true, true], [false, true, true, false, false, true, false, true], [true, false, false]] =
    [false, true, true, false, false, true, true, false] := by decide

-- Dropped-label endpoints are fixed.
example : bimatrixNodeSwitchWord ![[true], [false, false, false, false], [false]] =
    [false, false, false, false] := by decide

-- A nonduplicated label retains the supplied entering position.
example : bimatrixNodeSwitchWord
    ![[true, true], [false, false, false, false, false, true, true, false], [true, false]] =
    [false, false, false, false, false, true, true, false] := by decide

-- Malformed widths preserve the original word.
example : bimatrixNodeExchangeWord ![[true], [true, false], [], []] = [true, false] := by decide
example : bimatrixNodeSwitchWord ![[true], [true, false], []] = [true, false] := by decide

example : bimatrixNodeExchangeWord ![[], [], [], []] = [] := by decide
example : bimatrixNodeSwitchWord ![[], [], []] = [] := by decide

end GameTheory.Complexity.Backend.Tests.BimatrixNodeOperations
