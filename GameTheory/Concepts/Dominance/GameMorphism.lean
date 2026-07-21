/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Dominance.DominanceSolvability
import GameTheory.Concepts.Dominance.Rationalizability
import GameTheory.Concepts.Foundations.GameMorphism

/-!
# Dominance and Rationalizability under Game Isomorphism

Expected-utility game isomorphisms preserve dominant-strategy solvability and
the pure recursive elimination procedures used by IESDS and pure
rationalizability. Mixed rationalizability is treated in the same module.
-/

namespace GameTheory
namespace KernelGame
namespace EUGameIsomorphism

open Math.Probability

variable {ι : Type} [DecidableEq ι] {G H : KernelGame ι}

/-- Existence of a strictly dominant strategy for every player is invariant
under expected-utility game isomorphism. -/
theorem isDominantStrategySolvable_iff (e : EUGameIsomorphism G H) :
    G.IsDominantStrategySolvable ↔ H.IsDominantStrategySolvable := by
  constructor
  · intro h who
    obtain ⟨s, hs⟩ := h who
    exact ⟨e.stratEquiv who s, (e.isStrictDominant_iff who s).mp hs⟩
  · intro h who
    obtain ⟨t, ht⟩ := h who
    refine ⟨(e.stratEquiv who).symm t, ?_⟩
    exact (e.isStrictDominant_iff who _).mpr (by simpa using ht)

/-- Survival through a fixed number of rounds of pure strict-dominance
elimination is invariant under strategy relabeling. -/
theorem survivesStrictDominance_iff (e : EUGameIsomorphism G H)
    (n : ℕ) (who : ι) (s : G.Strategy who) :
    G.SurvivesStrictDominance n who s ↔
      H.SurvivesStrictDominance n who (e.stratEquiv who s) := by
  induction n generalizing who s with
  | zero => simp [KernelGame.SurvivesStrictDominance]
  | succ n ih =>
    constructor
    · rintro ⟨hs, hnot⟩
      refine ⟨(ih who s).mp hs, ?_⟩
      rintro ⟨t, ht, hdom⟩
      apply hnot
      refine ⟨(e.stratEquiv who).symm t, ?_, ?_⟩
      · exact (ih who _).mpr (by simpa using ht)
      · intro σ hσ
        have h := hdom (e.profileEquiv σ) (fun j => (ih j (σ j)).mp (hσ j))
        calc
          G.eu (Function.update σ who ((e.stratEquiv who).symm t)) who =
              H.eu (Function.update (e.profileEquiv σ) who
                (e.stratEquiv who ((e.stratEquiv who).symm t))) who :=
            (e.eu_update_preserved σ who _).symm
          _ = H.eu (Function.update (e.profileEquiv σ) who t) who := by simp
          _ > H.eu (Function.update (e.profileEquiv σ) who (e.stratEquiv who s)) who := h
          _ = G.eu (Function.update σ who s) who := e.eu_update_preserved σ who s
    · rintro ⟨hs, hnot⟩
      refine ⟨(ih who s).mpr hs, ?_⟩
      rintro ⟨t, ht, hdom⟩
      apply hnot
      refine ⟨e.stratEquiv who t, (ih who t).mp ht, ?_⟩
      intro τ hτ
      have h := hdom (e.profileEquiv.symm τ) (fun j =>
        (ih j (e.profileEquiv.symm τ j)).mpr (by simpa using hτ j))
      calc
        H.eu (Function.update τ who (e.stratEquiv who t)) who =
            G.eu (Function.update (e.profileEquiv.symm τ) who t) who := by
          simpa using e.eu_update_preserved (e.profileEquiv.symm τ) who t
        _ > G.eu (Function.update (e.profileEquiv.symm τ) who s) who := h
        _ = H.eu (Function.update τ who (e.stratEquiv who s)) who := by
          symm
          simpa using e.eu_update_preserved (e.profileEquiv.symm τ) who s

/-- IESDS solvability at a profile is invariant under expected-utility game
isomorphism. -/
theorem isIESDSSolvable_iff (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsIESDSSolvable σ ↔ H.IsIESDSSolvable (e.profileEquiv σ) := by
  unfold KernelGame.IsIESDSSolvable
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun i t => ?_⟩
    calc
      H.SurvivesStrictDominance N i t ↔
          G.SurvivesStrictDominance N i ((e.stratEquiv i).symm t) := by
        simpa using (e.survivesStrictDominance_iff N i ((e.stratEquiv i).symm t)).symm
      _ ↔ (e.stratEquiv i).symm t = σ i := hN i _
      _ ↔ t = e.profileEquiv σ i := by simp [profileEquiv_apply, Equiv.symm_apply_eq]
  · rintro ⟨N, hN⟩
    refine ⟨N, fun i s => ?_⟩
    calc
      G.SurvivesStrictDominance N i s ↔
          H.SurvivesStrictDominance N i (e.stratEquiv i s) :=
        e.survivesStrictDominance_iff N i s
      _ ↔ e.stratEquiv i s = e.profileEquiv σ i := hN i _
      _ ↔ s = σ i := by simp [profileEquiv_apply]

/-- Survival through a fixed number of pure-rationalizability rounds is
invariant under strategy relabeling. -/
theorem survivesPure_iff (e : EUGameIsomorphism G H)
    (n : ℕ) (who : ι) (s : G.Strategy who) :
    G.SurvivesPure n who s ↔ H.SurvivesPure n who (e.stratEquiv who s) := by
  induction n generalizing who s with
  | zero => simp [KernelGame.SurvivesPure]
  | succ n ih =>
    constructor
    · rintro ⟨hs, hnot⟩
      refine ⟨(ih who s).mp hs, ?_⟩
      rintro ⟨t, ht, hdom⟩
      apply hnot
      refine ⟨(e.stratEquiv who).symm t, ?_, ?_⟩
      · exact (ih who _).mpr (by simpa using ht)
      · intro σ hσ
        have h := hdom (e.profileEquiv σ) (fun j => (ih j (σ j)).mp (hσ j))
        calc
          G.eu (Function.update σ who ((e.stratEquiv who).symm t)) who =
              H.eu (Function.update (e.profileEquiv σ) who
                (e.stratEquiv who ((e.stratEquiv who).symm t))) who :=
            (e.eu_update_preserved σ who _).symm
          _ = H.eu (Function.update (e.profileEquiv σ) who t) who := by simp
          _ > H.eu (Function.update (e.profileEquiv σ) who (e.stratEquiv who s)) who := h
          _ = G.eu (Function.update σ who s) who := e.eu_update_preserved σ who s
    · rintro ⟨hs, hnot⟩
      refine ⟨(ih who s).mpr hs, ?_⟩
      rintro ⟨t, ht, hdom⟩
      apply hnot
      refine ⟨e.stratEquiv who t, (ih who t).mp ht, ?_⟩
      intro τ hτ
      have h := hdom (e.profileEquiv.symm τ) (fun j =>
        (ih j (e.profileEquiv.symm τ j)).mpr (by simpa using hτ j))
      calc
        H.eu (Function.update τ who (e.stratEquiv who t)) who =
            G.eu (Function.update (e.profileEquiv.symm τ) who t) who := by
          simpa using e.eu_update_preserved (e.profileEquiv.symm τ) who t
        _ > G.eu (Function.update (e.profileEquiv.symm τ) who s) who := h
        _ = H.eu (Function.update τ who (e.stratEquiv who s)) who := by
          symm
          simpa using e.eu_update_preserved (e.profileEquiv.symm τ) who s

/-- Pure rationalizability is invariant under expected-utility game
isomorphism. -/
theorem isPureRationalizable_iff (e : EUGameIsomorphism G H)
    (who : ι) (s : G.Strategy who) :
    G.IsPureRationalizable who s ↔
      H.IsPureRationalizable who (e.stratEquiv who s) := by
  unfold KernelGame.IsPureRationalizable
  exact forall_congr' fun n => e.survivesPure_iff n who s

/-- Survival through a fixed number of mixed-dominance elimination rounds is
invariant under strategy relabeling. The dominating PMF is transported through
the equivalence on the deviating player's pure strategies. -/
theorem survives_iff (e : EUGameIsomorphism G H)
    (n : ℕ) (who : ι) (s : G.Strategy who) :
    G.Survives n who s ↔ H.Survives n who (e.stratEquiv who s) := by
  induction n generalizing who s with
  | zero => simp [KernelGame.Survives]
  | succ n ih =>
    constructor
    · rintro ⟨hs, hnot⟩
      refine ⟨(ih who s).mp hs, ?_⟩
      rintro ⟨q, hq, hdom⟩
      let p : PMF (G.Strategy who) :=
        (Math.ProbabilityMassFunction.mapEquiv (e.stratEquiv who)).symm q
      apply hnot
      refine ⟨p, ?_, ?_⟩
      · intro a ha
        have ha' : a ∈ (q.map (e.stratEquiv who).symm).support := by
          simpa [p, Math.ProbabilityMassFunction.mapEquiv_symm_apply] using ha
        rcases (PMF.mem_support_map_iff _ _ _).mp ha' with ⟨b, hb, hba⟩
        subst a
        exact (ih who _).mpr (by simpa using hq b hb)
      · intro σ hσ
        have h := hdom (e.profileEquiv σ) (fun j => (ih j (σ j)).mp (hσ j))
        calc
          expect p (fun a => G.eu (Function.update σ who a) who) =
              expect q (fun b =>
                G.eu (Function.update σ who ((e.stratEquiv who).symm b)) who) := by
            simp [p, Math.ProbabilityMassFunction.mapEquiv_symm_apply, expect_map]
          _ = expect q (fun b =>
                H.eu (Function.update (e.profileEquiv σ) who b) who) := by
            congr 1
            funext b
            simpa using (e.eu_update_preserved σ who ((e.stratEquiv who).symm b)).symm
          _ > H.eu (Function.update (e.profileEquiv σ) who (e.stratEquiv who s)) who := h
          _ = G.eu (Function.update σ who s) who := e.eu_update_preserved σ who s
    · rintro ⟨hs, hnot⟩
      refine ⟨(ih who s).mpr hs, ?_⟩
      rintro ⟨p, hp, hdom⟩
      let q : PMF (H.Strategy who) :=
        Math.ProbabilityMassFunction.mapEquiv (e.stratEquiv who) p
      apply hnot
      refine ⟨q, ?_, ?_⟩
      · intro b hb
        have hb' : b ∈ (p.map (e.stratEquiv who)).support := by
          simpa [q, Math.ProbabilityMassFunction.mapEquiv_apply] using hb
        rcases (PMF.mem_support_map_iff _ _ _).mp hb' with ⟨a, ha, hab⟩
        subst b
        exact (ih who a).mp (hp a ha)
      · intro τ hτ
        have h := hdom (e.profileEquiv.symm τ) (fun j =>
          (ih j (e.profileEquiv.symm τ j)).mpr (by simpa using hτ j))
        calc
          expect q (fun b => H.eu (Function.update τ who b) who) =
              expect p (fun a =>
                H.eu (Function.update τ who (e.stratEquiv who a)) who) := by
            simp [q, Math.ProbabilityMassFunction.mapEquiv_apply, expect_map]
          _ = expect p (fun a =>
                G.eu (Function.update (e.profileEquiv.symm τ) who a) who) := by
            congr 1
            funext a
            simpa using e.eu_update_preserved (e.profileEquiv.symm τ) who a
          _ > G.eu (Function.update (e.profileEquiv.symm τ) who s) who := h
          _ = H.eu (Function.update τ who (e.stratEquiv who s)) who := by
            symm
            simpa using e.eu_update_preserved (e.profileEquiv.symm τ) who s

/-- Rationalizability by iterated mixed-strategy dominance is invariant under
expected-utility game isomorphism. -/
theorem isRationalizable_iff (e : EUGameIsomorphism G H)
    (who : ι) (s : G.Strategy who) :
    G.IsRationalizable who s ↔ H.IsRationalizable who (e.stratEquiv who s) := by
  unfold KernelGame.IsRationalizable
  exact forall_congr' fun n => e.survives_iff n who s

end EUGameIsomorphism
end KernelGame
end GameTheory
