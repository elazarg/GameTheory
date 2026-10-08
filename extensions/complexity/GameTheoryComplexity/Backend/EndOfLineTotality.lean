import GameTheory.Math.EndOfLine
import Mathlib.Data.Fintype.Vector

/-! Finite End-of-Line totality for fixed-width binary words. -/

namespace GameTheory.Complexity.Backend

/-- Length-preserving binary pointers with a known source have another endpoint. -/
theorem exists_word_endpoint (n : ℕ) (P S : List Bool → List Bool)
    (hPwidth : ∀ w, w.length = n → (P w).length = n)
    (hSwidth : ∀ w, w.length = n → (S w).length = n)
    (hP : P (List.replicate n false) = List.replicate n false)
    (hS : S (List.replicate n false) ≠ List.replicate n false)
    (hlink : P (S (List.replicate n false)) = List.replicate n false) :
    ∃ w, w.length = n ∧ w ≠ List.replicate n false ∧
      GameTheory.Math.EndOfLine.IsEndpoint P S w := by
  let p : List.Vector Bool n → List.Vector Bool n := fun w => ⟨P w.1, hPwidth w.1 w.2⟩
  let s : List.Vector Bool n → List.Vector Bool n := fun w => ⟨S w.1, hSwidth w.1 w.2⟩
  let origin : List.Vector Bool n := ⟨List.replicate n false, List.length_replicate⟩
  have hp : p origin = origin := Subtype.ext hP
  have hs : s origin ≠ origin := fun h => hS (congrArg Subtype.val h)
  have hl : p (s origin) = origin := Subtype.ext hlink
  obtain ⟨w, hw, hend⟩ :=
    GameTheory.Math.EndOfLine.exists_endpoint_ne_origin p s origin hp hs hl
  rcases w with ⟨w, hlen⟩
  have hsuc : GameTheory.Math.EndOfLine.HasSuccessor p s ⟨w, hlen⟩ ↔
      GameTheory.Math.EndOfLine.HasSuccessor P S w := by
    constructor
    · rintro ⟨hne, heq⟩
      exact ⟨fun h => hne (Subtype.ext h), congrArg Subtype.val heq⟩
    · rintro ⟨hne, heq⟩
      exact ⟨fun h => hne (congrArg Subtype.val h), Subtype.ext heq⟩
  have hpred : GameTheory.Math.EndOfLine.HasPredecessor p s ⟨w, hlen⟩ ↔
      GameTheory.Math.EndOfLine.HasPredecessor P S w := by
    constructor
    · rintro ⟨hne, heq⟩
      exact ⟨fun h => hne (Subtype.ext h), congrArg Subtype.val heq⟩
    · rintro ⟨hne, heq⟩
      exact ⟨fun h => hne (congrArg Subtype.val h), Subtype.ext heq⟩
  refine ⟨w, hlen, ?_, ?_⟩
  · exact fun h => hw (Subtype.ext h)
  · simpa only [GameTheory.Math.EndOfLine.IsEndpoint, hsuc, hpred] using hend

end GameTheory.Complexity.Backend
