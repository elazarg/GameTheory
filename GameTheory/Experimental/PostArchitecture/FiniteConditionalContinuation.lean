/-
# EXP-105: conditional continuation from a finite law

This file reconstructs a continuation kernel from a joint finite law.  Under
division-free conditional independence, binding that kernel after the full
context law recovers the exact joint law of context and term, including over
kept values with zero mass.
-/

import GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation

open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence

universe uΩ uFull uTerm uKept

variable {Ω : Type uΩ} {Full : Type uFull}
variable {Term : Type uTerm} {Kept : Type uKept}

/-- A pushforward point mass is the mass of the corresponding observable
atom. -/
theorem map_prob_eq_probOf_atom (law : FinDist Ω) (observable : Ω → Full)
    (value : Full) :
    (law.map observable).prob value = law.probOf (atom observable value) := by
  classical
  rw [FinDist.prob_map, ← FinDist.expect_indicator_eq_probOf]
  apply FinDist.expect_congr
  intro omega _
  simp [atom, eq_comm]

/-- The same point-mass bridge for a pair of observables. -/
theorem map_pair_prob_eq_probOf_pairAtom (law : FinDist Ω)
    (first : Ω → Full) (second : Ω → Term)
    (firstValue : Full) (secondValue : Term) :
    (law.map fun omega => (first omega, second omega)).prob
        (firstValue, secondValue) =
      law.probOf (pairAtom first second firstValue secondValue) := by
  rw [map_prob_eq_probOf_atom law
    (fun omega => (first omega, second omega)) (firstValue, secondValue)]
  congr 1
  ext omega
  simp [atom, pairAtom]

/-- Condition the law of `(kept context, term)` on its kept coordinate and
project away that coordinate.  `condOnFibre` supplies a total fallback at
zero-mass kept values. -/
def continuation (law : FinDist Ω) (context : Ω → Full) (term : Ω → Term)
    (keep : Full → Kept) (kept : Kept) : FinDist Term :=
  let keptTermLaw := law.map fun omega => (keep (context omega), term omega)
  (keptTermLaw.condOnFibre Prod.fst kept).map Prod.snd

private theorem condOnFibre_fst_map_snd_prob
    (joint : FinDist (Kept × Term)) (kept : Kept) (termValue : Term)
    (hfibre : ∃ pair ∈ Prod.fst ⁻¹' {kept}, pair ∈ joint.support) :
    ((joint.condOnFibre Prod.fst kept).map Prod.snd).prob termValue =
      joint.prob (kept, termValue) / (joint.map Prod.fst).prob kept := by
  classical
  have hconditional :
      joint.condOnFibre Prod.fst kept =
        joint.condOn (Prod.fst ⁻¹' {kept}) hfibre := by
    rw [FinDist.condOnFibre, dif_pos hfibre]
  rw [hconditional, FinDist.prob_map]
  let conditional := joint.condOn (Prod.fst ⁻¹' {kept}) hfibre
  calc
    conditional.expect
        (fun pair => if termValue = pair.snd then 1 else 0) =
        conditional.expect
          (fun pair => if (kept, termValue) = pair then 1 else 0) := by
      apply FinDist.expect_congr
      intro pair hpair
      have hfirst :=
        (FinDist.support_condOn joint (Prod.fst ⁻¹' {kept}) hfibre hpair).1
      have heq : pair.1 = kept := by simpa using hfirst
      rcases pair with ⟨first, second⟩
      have hfirstEq : first = kept := by simpa only using heq
      subst first
      simp
    _ = conditional.prob (kept, termValue) := by
      rw [FinDist.expect_ite_eq, mul_one]
    _ = joint.prob (kept, termValue) /
        joint.probOf (Prod.fst ⁻¹' {kept}) := by
      unfold conditional
      rw [FinDist.prob_condOn, if_pos]
      simp
    _ = joint.prob (kept, termValue) / (joint.map Prod.fst).prob kept := by
      rw [map_prob_eq_probOf_atom joint Prod.fst kept]
      have hevent :
          atom (fun pair : Kept × Term => pair.1) kept =
            (fun pair : Kept × Term => pair.1) ⁻¹' {kept} := by
        ext pair
        simp [atom]
      rw [hevent]

private theorem bind_mapped_pair_prob (outer : FinDist Full)
    (kernel : Full → FinDist Term) (full : Full) (termValue : Term) :
    (outer.bind fun candidate =>
        (kernel candidate).map fun value => (candidate, value)).prob
        (full, termValue) =
      outer.prob full * (kernel full).prob termValue := by
  classical
  rw [FinDist.prob_bind]
  calc
    outer.expect (fun candidate =>
        ((kernel candidate).map fun value => (candidate, value)).prob
          (full, termValue)) =
        outer.expect (fun candidate =>
          if full = candidate then (kernel full).prob termValue else 0) := by
      apply FinDist.expect_congr
      intro candidate _
      by_cases heq : full = candidate
      · subst candidate
        rw [if_pos rfl]
        exact FinDist.prob_map_of_injective
          (fun value => (full, value)) (fun _ _ h => (Prod.mk.inj h).2)
          (kernel full) termValue
      · rw [if_neg heq, FinDist.prob_eq_zero_iff]
        intro hsupport
        rw [FinDist.support_map] at hsupport
        obtain ⟨value, _, hvalue⟩ := hsupport
        exact heq (congrArg Prod.fst hvalue).symm
    _ = outer.prob full * (kernel full).prob termValue := by
      rw [FinDist.expect_ite_eq]

/-- Conditional independence of the full context and term given the retained
context makes the canonical conditional continuation an exact factorization
of their joint law.  The statement contains no division and remains exact at
zero-mass retained contexts because those branches are never drawn. -/
theorem contextTermLaw_eq_bind_continuation
    (law : FinDist Ω) (context : Ω → Full) (term : Ω → Term)
    (keep : Full → Kept)
    (hindependent : IsConditionallyIndependent law context term
      (keep ∘ context)) :
    law.map (fun omega => (context omega, term omega)) =
      (law.map context).bind fun full =>
        (continuation law context term keep (keep full)).map
          fun termValue => (full, termValue) := by
  classical
  apply FinDist.ext_of_prob
  rintro ⟨full, termValue⟩
  rw [bind_mapped_pair_prob]
  rw [map_pair_prob_eq_probOf_pairAtom,
    map_prob_eq_probOf_atom]
  by_cases hfull : full ∈ (law.map context).support
  · rw [FinDist.support_map] at hfull
    obtain ⟨omega, homega, hcontext⟩ := hfull
    let keptTermLaw :=
      law.map fun state => (keep (context state), term state)
    have hkeptTerm :
        (keep full, term omega) ∈ keptTermLaw.support := by
      unfold keptTermLaw
      rw [FinDist.support_map]
      exact ⟨omega, homega, by simp [hcontext]⟩
    have hfibre :
        ∃ pair ∈ Prod.fst ⁻¹' {keep full},
          pair ∈ keptTermLaw.support := by
      exact ⟨(keep full, term omega), by simp, hkeptTerm⟩
    have hcontinuation :=
      condOnFibre_fst_map_snd_prob keptTermLaw (keep full) termValue hfibre
    have hfirstMap :
        keptTermLaw.map Prod.fst = law.map (keep ∘ context) := by
      unfold keptTermLaw
      rw [FinDist.map_comp]
      rfl
    have hkeptPair :
        keptTermLaw.prob (keep full, termValue) =
      law.probOf
            (pairAtom term (keep ∘ context) termValue (keep full)) := by
      unfold keptTermLaw
      rw [map_pair_prob_eq_probOf_pairAtom]
      congr 1
      ext state
      simp only [pairAtom, Set.mem_setOf_eq, Function.comp_apply]
      exact and_comm
    have hcontinuation' :
        (continuation law context term keep (keep full)).prob termValue =
          law.probOf
              (pairAtom term (keep ∘ context) termValue (keep full)) /
            law.probOf (atom (keep ∘ context) (keep full)) := by
      unfold continuation
      rw [hcontinuation, hkeptPair, hfirstMap,
        map_prob_eq_probOf_atom]
    rw [hcontinuation']
    have hevidence :
        0 < law.probOf (atom (keep ∘ context) (keep full)) := by
      apply FinDist.probOf_pos
      exact ⟨omega, by simp [atom, hcontext], homega⟩
    have hcross := hindependent full termValue (keep full)
    have htriple :
        tripleAtom context term (keep ∘ context)
            full termValue (keep full) =
          pairAtom context term full termValue := by
      ext state
      constructor
      · rintro ⟨hstate, hterm, _⟩
        exact ⟨hstate, hterm⟩
      · rintro ⟨hstate, hterm⟩
        exact ⟨hstate, hterm, by simp [hstate]⟩
    have hcontextEvidence :
        pairAtom context (keep ∘ context) full (keep full) =
      atom context full := by
      ext state
      simp only [pairAtom, atom, Set.mem_setOf_eq, Function.comp_apply]
      constructor
      · exact fun hstate => hstate.1
      · intro hstate
        exact ⟨hstate, by simp [hstate]⟩
    rw [htriple, hcontextEvidence] at hcross
    calc
      law.probOf (pairAtom context term full termValue) =
          law.probOf (atom context full) *
              law.probOf
                (pairAtom term (keep ∘ context) termValue (keep full)) /
            law.probOf (atom (keep ∘ context) (keep full)) :=
        (eq_div_iff hevidence.ne').2 hcross
      _ = law.probOf (atom context full) *
          (law.probOf
              (pairAtom term (keep ∘ context) termValue (keep full)) /
            law.probOf (atom (keep ∘ context) (keep full))) := by
        ring
  · have hcontextZero : law.probOf (atom context full) = 0 := by
      rw [← map_prob_eq_probOf_atom]
      exact FinDist.prob_eq_zero_iff.mpr hfull
    rw [hcontextZero, zero_mul]
    exact probOf_eq_zero_of_subset law (by
      intro state hstate
      exact hstate.1) hcontextZero

end GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation
