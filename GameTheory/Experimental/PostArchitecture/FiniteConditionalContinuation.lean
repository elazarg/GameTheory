/-
# EXP-105: conditional continuation from an ordinary PMF

This file reconstructs a continuation kernel from a joint PMF. Under
division-free conditional independence, binding that kernel after the full
context law recovers the exact joint law of context and term. The kernel uses
the canonical fiber posterior on supported kept values and a total fallback
law elsewhere.
-/

import GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence
import GameTheory.Math.Probability.Conditioning
import GameTheory.Math.Probability.Joint

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation

open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence

universe uΩ uFull uTerm uKept

variable {Ω : Type uΩ} {Full : Type uFull}
variable {Term : Type uTerm} {Kept : Type uKept}

/-- The real outer mass of an observable point is the real outer mass of its
preimage atom. -/
theorem map_mass_eq_atomMass (law : PMF Ω) (observable : Ω → Full)
    (value : Full) :
    ((law.map observable).toOuterMeasure {value}).toReal =
      (law.toOuterMeasure (atom observable value)).toReal := by
  classical
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- The same event-mass bridge for a pair of observables. -/
theorem map_pair_mass_eq_pairAtomMass (law : PMF Ω)
    (first : Ω → Full) (second : Ω → Term)
    (firstValue : Full) (secondValue : Term) :
    ((law.map fun omega => (first omega, second omega)).toOuterMeasure
        {(firstValue, secondValue)}).toReal =
      (law.toOuterMeasure
        (pairAtom first second firstValue secondValue)).toReal := by
  classical
  have hset :
      (fun omega => (first omega, second omega)) ⁻¹'
        {(firstValue, secondValue)} =
      pairAtom first second firstValue secondValue := by
    ext omega
    simp [pairAtom]
  rw [PMF.toOuterMeasure_map_apply, hset]

/-- Condition the law of `(kept context, term)` on its kept coordinate and
project away that coordinate. Supported kept values use the canonical fiber
posterior; unsupported values use the source term marginal as a total fallback. -/
def continuation (law : PMF Ω) (context : Ω → Full) (term : Ω → Term)
    (keep : Full → Kept) (kept : Kept) : PMF Term := by
  classical
  let keptTermLaw := law.map fun omega => (keep (context omega), term omega)
  let keptLaw := law.map (keep ∘ context)
  exact if hkept : kept ∈ keptLaw.support then
    (fiberPosterior keptTermLaw Prod.fst kept (by
      simpa [keptTermLaw, keptLaw, PMF.map_comp] using hkept)).map Prod.snd
  else keptTermLaw.map Prod.snd

private theorem joint_kept_marginal (law : PMF Ω)
    (context : Ω → Full) (term : Ω → Term) (keep : Full → Kept) :
    (law.map fun omega => (keep (context omega), term omega)).map Prod.fst =
      law.map (keep ∘ context) := by
  rw [PMF.map_comp]
  rfl

private theorem continuation_apply_of_mem (law : PMF Ω)
    (context : Ω → Full) (term : Ω → Term) (keep : Full → Kept)
    (kept : Kept) (hkept : kept ∈ (law.map (keep ∘ context)).support)
    (termValue : Term) :
    continuation law context term keep kept termValue =
      (law.map fun omega => (keep (context omega), term omega))
          (kept, termValue) *
        ((law.map (keep ∘ context)) kept)⁻¹ := by
  let keptTermLaw := law.map fun omega => (keep (context omega), term omega)
  have hmarginal := joint_kept_marginal law context term keep
  have hkeptTerm : kept ∈ (keptTermLaw.map Prod.fst).support := by
    rw [hmarginal]
    exact hkept
  unfold continuation
  simp only [dite_eq_left hkept]
  simpa only [keptTermLaw, hmarginal] using
    fiberPosterior_map_snd_apply keptTermLaw kept hkeptTerm termValue

/-- Conditional independence makes the continuation kernel an exact
factorization of the context-term joint PMF.  Unsupported kept values use a
total fallback, but receive no mass from the bind. -/
theorem contextTermLaw_eq_bind_continuation
    (law : PMF Ω) (context : Ω → Full) (term : Ω → Term)
    (keep : Full → Kept)
    (hindependent : IsConditionallyIndependent law context term
      (keep ∘ context)) :
    law.map (fun omega => (context omega, term omega)) =
      (law.map context).bind fun full =>
        (continuation law context term keep (keep full)).map
          fun termValue => (full, termValue) := by
  classical
  apply PMF.ext
  rintro ⟨full, termValue⟩
  let contextLaw := law.map context
  by_cases hfull : full ∈ contextLaw.support
  · rcases (PMF.mem_support_map_iff context law full).mp hfull with
      ⟨omega, homega, hcontext⟩
    have hkept : keep full ∈ (law.map (keep ∘ context)).support := by
      apply (PMF.mem_support_map_iff (keep ∘ context) law (keep full)).mpr
      exact ⟨omega, homega, by rw [Function.comp_apply, hcontext]⟩
    have hkeptOuterPos := outerMeasure_pos_of_mem_support (μ := law)
      (event := atom (keep ∘ context) (keep full)) omega
      (by simp [atom, hcontext]) homega
    let contextMass :=
      (law.toOuterMeasure (atom context full)).toReal
    let keptMass :=
      (law.toOuterMeasure (atom (keep ∘ context) (keep full))).toReal
    let termKeptMass :=
      (law.toOuterMeasure
        (pairAtom term (keep ∘ context) termValue (keep full))).toReal
    let jointMass :=
      (law.toOuterMeasure (pairAtom context term full termValue)).toReal
    have hkeptPos : 0 < keptMass := by
      dsimp [keptMass]
      exact ENNReal.toReal_pos hkeptOuterPos.ne'
        (outerMeasure_ne_top law (atom (keep ∘ context) (keep full)))
    have htriple :
        tripleAtom context term (keep ∘ context) full termValue (keep full) =
          pairAtom context term full termValue := by
      ext state
      simp only [tripleAtom, pairAtom, Set.mem_ofPred_eq,
        Function.comp_apply]
      tauto
    have hcontextPair :
      pairAtom context (keep ∘ context) full (keep full) =
          atom context full := by
      ext state
      simp only [pairAtom, atom, Set.mem_ofPred_eq, Function.comp_apply]
      tauto
    have hcross : jointMass * keptMass = contextMass * termKeptMass := by
      simpa [jointMass, keptMass, contextMass, termKeptMass,
        htriple, hcontextPair] using
        hindependent full termValue (keep full)
    have hratio : jointMass = contextMass * (termKeptMass / keptMass) := by
      simpa [mul_div_assoc] using (eq_div_iff hkeptPos.ne').2 hcross
    have hleft :
        ((law.map fun omega => (context omega, term omega))
            (full, termValue)).toReal = jointMass := by
      simpa only [PMF.toOuterMeasure_apply_singleton] using
        map_pair_mass_eq_pairAtomMass law context term full termValue
    have htermPoint :
        ((law.map fun omega => (keep (context omega), term omega))
          (keep full, termValue)).toReal = termKeptMass := by
      have hterm :=
        map_pair_mass_eq_pairAtomMass law (keep ∘ context) term
          (keep full) termValue
      have hswap :
          pairAtom (keep ∘ context) term (keep full) termValue =
            pairAtom term (keep ∘ context) termValue (keep full) := by
        ext state
        simp only [pairAtom, Set.mem_ofPred_eq, Function.comp_apply]
        tauto
      simpa only [PMF.toOuterMeasure_apply_singleton, termKeptMass,
        Function.comp_apply, hswap] using hterm
    have hdenPoint :
        ((law.map (keep ∘ context)) (keep full)).toReal = keptMass := by
      have hden := map_mass_eq_atomMass law (keep ∘ context) (keep full)
      simpa only [PMF.toOuterMeasure_apply_singleton] using hden
    have hcont :
        (continuation law context term keep (keep full) termValue).toReal =
          termKeptMass / keptMass := by
      rw [continuation_apply_of_mem law context term keep (keep full)
        hkept termValue]
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
      rw [htermPoint, hdenPoint]
      simp [div_eq_mul_inv]
    have hcontextPoint : (contextLaw full).toReal = contextMass := by
      simpa only [contextLaw, PMF.toOuterMeasure_apply_singleton, contextMass]
        using map_mass_eq_atomMass law context full
    have hbindPair :
        contextLaw.bind (fun candidate =>
          (continuation law context term keep (keep candidate)).map
            (fun value => (candidate, value))) =
          bindPairLaw contextLaw
            (fun candidate =>
              continuation law context term keep (keep candidate)) := rfl
    apply (ENNReal.toReal_eq_toReal_iff'
      ((law.map (fun omega => (context omega, term omega))).apply_ne_top
        (full, termValue))
      ((contextLaw.bind fun candidate =>
        (continuation law context term keep (keep candidate)).map
          fun value => (candidate, value)).apply_ne_top (full, termValue))).mp
    rw [hbindPair, bindPairLaw_apply]
    rw [ENNReal.toReal_mul]
    rw [hcontextPoint, hcont]
    simpa only [hleft] using hratio
  · have hcontextZero : contextLaw full = 0 := by
      exact (contextLaw.apply_eq_zero_iff full).mpr hfull
    have hjointUnsupported :
        (full, termValue) ∉
          (law.map fun omega => (context omega, term omega)).support := by
      intro hpair
      rcases (PMF.mem_support_map_iff
        (fun omega => (context omega, term omega)) law
        (full, termValue)).mp hpair with
        ⟨omega, homega, hpairEq⟩
      exact hfull <| (PMF.mem_support_map_iff context law full).mpr
        ⟨omega, homega, congrArg Prod.fst hpairEq⟩
    have hbindPair :
        contextLaw.bind (fun candidate =>
          (continuation law context term keep (keep candidate)).map
            (fun value => (candidate, value))) =
          bindPairLaw contextLaw
            (fun candidate =>
              continuation law context term keep (keep candidate)) := rfl
    rw [hbindPair, bindPairLaw_apply]
    rw [(PMF.apply_eq_zero_iff _ _).mpr hjointUnsupported, hcontextZero,
      zero_mul]

end GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation
