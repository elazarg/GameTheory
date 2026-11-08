module

public import GameTheoryComplexity.Backend.RawEndOfLineReduction
public import GameTheoryComplexity.Backend.EndOfLineMembership
public import GameTheoryComplexity.Backend.NativeEndOfLineReduction

@[expose] public section

/-! Native directed-parity classification of concrete End-of-Line problems.
Uniform circuit generation realizes every encoded polynomial-time pointer
family, and each decoder preserves every target answer, including failed source
promises. Verification and witness bounds are supplied independently.
-/

namespace GameTheory.Complexity

open Turing.MultiTapeTM
open Backend

/-- Asymmetric pointer search belongs to the native directed-parity class. -/
theorem rawEndOfLineRelation_mem_PPAD :
    rawEndOfLineRelation ∈ Cslib.Complexity.PPAD encBits :=
  rawToEndpointReduction.mem_PPAD rawEndOfLineRelation_mem_FNP
    Backend.endOfLineRelation_mem_PPAD

/-- Every native directed-parity problem reduces to concrete endpoint search,
for arbitrary encoded instance types. -/
theorem endOfLineRelation_PPADHard :
    Cslib.Complexity.SearchHard @Cslib.Complexity.PPAD encBits endOfLineRelation := by
  intro α enc R hR
  obtain ⟨_, n, P, S, hn, hP, hS, hP_length, hS_length, hred⟩ :=
    Cslib.Complexity.mem_PPAD.mp hR
  exact hred.trans (nativeEndOfLine_searchReducible hn hP hS hP_length hS_length)

/-- Concrete endpoint search belongs to native PPAD. -/
theorem endOfLineRelation_mem_PPAD :
    endOfLineRelation ∈ Cslib.Complexity.PPAD encBits :=
  Backend.endOfLineRelation_mem_PPAD

/-- Consistent-edge endpoint search is complete for native directed parity. -/
theorem endOfLineRelation_PPADComplete :
    Cslib.Complexity.SearchComplete @Cslib.Complexity.PPAD encBits endOfLineRelation :=
  ⟨endOfLineRelation_mem_PPAD, endOfLineRelation_PPADHard⟩

/-- Every native directed-parity problem reduces to asymmetric pointer search,
with every raw inconsistency decoded. -/
theorem rawEndOfLineRelation_PPADHard :
    Cslib.Complexity.SearchHard @Cslib.Complexity.PPAD encBits rawEndOfLineRelation := by
  intro α enc R hR
  obtain ⟨_, n, P, S, hn, hP, hS, hP_length, hS_length, hred⟩ :=
    Cslib.Complexity.mem_PPAD.mp hR
  exact hred.trans (nativeEndOfLine_raw_searchReducible hn hP hS hP_length hS_length)

/-- Asymmetric pointer search is complete for native directed parity. -/
theorem rawEndOfLineRelation_PPADComplete :
    Cslib.Complexity.SearchComplete @Cslib.Complexity.PPAD encBits rawEndOfLineRelation :=
  ⟨rawEndOfLineRelation_mem_PPAD, rawEndOfLineRelation_PPADHard⟩

end GameTheory.Complexity
