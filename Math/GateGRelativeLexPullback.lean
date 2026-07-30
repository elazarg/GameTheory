import Math.GateGLexIsolation
import Math.GateGRelativeFiberPullback

set_option autoImplicit false
set_option linter.unusedFintypeInType false

noncomputable section

open Filter Set

namespace Math
namespace GateGRelativeLexPullback

open GateGLexIsolationScratch
open GateGRelativeFiberPullback
open GateGRelativePresentation

/--
A lexicographically restricted local extremum on a fixed-parameter
relative zero locus pulls back to the corresponding restricted presentation
fiber.  Every preceding objective level is preserved because its relative
polynomial and its chosen element of the presented algebra have the same
evaluation at every presentation point.
-/
theorem isLocalExtrOn_presentationFiber_previous_relative
    {S ι κ ν E : Type*} {d : ℕ}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Fintype ι]
    (P :
      Algebra.Presentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (coordinate : ν → S)
    (equation :
      E → MvPolynomial ν (Polynomial ℝ))
    (hzero :
      ∀ e : E,
        MvPolynomial.eval₂
          (algebraMap (Polynomial ℝ) S)
          coordinate (equation e) = 0)
    (objective :
      Fin d → MvPolynomial ν (Polynomial ℝ))
    (objectiveValue : Fin d → S)
    (hobjective :
      ∀ j,
        MvPolynomial.eval₂
          (algebraMap (Polynomial ℝ) S)
          coordinate (objective j) =
        objectiveValue j)
    (x : ι → ℝ) (y : ν → ℝ)
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) x
          (P.relation j) = 0)
    (hsection :
      presentationSectionMap
        P t coordinate x = y)
    (j : Fin d)
    (hlocal :
      IsLocalExtrOn
        (fun w : ν → ℝ =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom t) w
            (objective j))
        ({w |
            ∀ e : E,
              MvPolynomial.eval₂
                (Polynomial.evalRingHom t) w
                (equation e) = 0} ∩
          previousObjectiveLevelSet
            (fun l w =>
              MvPolynomial.eval₂
                (Polynomial.evalRingHom t) w
                (objective l))
            y j)
        y) :
    IsLocalExtrOn
      (fun z : ι → ℝ =>
        MvPolynomial.eval z
          (specializeParameterPolynomial t
            (P.σ (objectiveValue j))))
      ({z |
          ∀ k : κ,
            MvPolynomial.eval z
                (specializeParameterPolynomial t
                  (P.relation k)) =
              MvPolynomial.eval x
                (specializeParameterPolynomial t
                  (P.relation k))} ∩
        previousObjectiveLevelSet
          (fun l z =>
            MvPolynomial.eval z
              (specializeParameterPolynomial t
                (P.σ (objectiveValue l))))
          x j)
      x := by
  let fiber : Set (ι → ℝ) :=
    {z |
      ∀ k : κ,
        MvPolynomial.eval z
            (specializeParameterPolynomial t
              (P.relation k)) =
          MvPolynomial.eval x
            (specializeParameterPolynomial t
              (P.relation k))}
  let presentationLevels : Set (ι → ℝ) :=
    previousObjectiveLevelSet
      (fun l z =>
        MvPolynomial.eval z
          (specializeParameterPolynomial t
            (P.σ (objectiveValue l))))
      x j
  let zeroLocus : Set (ν → ℝ) :=
    {w |
      ∀ e : E,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) w
          (equation e) = 0}
  let sourceLevels : Set (ν → ℝ) :=
    previousObjectiveLevelSet
      (fun l w =>
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) w
          (objective l))
      y j
  have hxmem : x ∈ fiber ∩ presentationLevels := by
    refine ⟨?_, ?_⟩
    · intro k
      rfl
    · intro l
      rfl
  have hrelation_of_mem :
      ∀ z ∈ fiber,
        ∀ k : κ,
          MvPolynomial.eval₂
            (Polynomial.evalRingHom t) z
            (P.relation k) = 0 := by
    intro z hz k
    rw [← eval_specializeParameterPolynomial]
    exact
      (hz k).trans
        (by
          rw [eval_specializeParameterPolynomial]
          exact hrelation k)
  have hobjective_section :
      ∀ z ∈ fiber, ∀ l,
        MvPolynomial.eval₂
            (Polynomial.evalRingHom t)
            (presentationSectionMap P t coordinate z)
            (objective l) =
          MvPolynomial.eval z
            (specializeParameterPolynomial t
              (P.σ (objectiveValue l))) := by
    intro z hz l
    simpa only [eval_specializeParameterPolynomial] using
      eval₂_presentationSectionMap_eq_rep
        P t coordinate z
        (hrelation_of_mem z hz)
        (objective l) (objectiveValue l)
        (hobjective l)
  have hmaps :
      fiber ∩ presentationLevels ⊆
        presentationSectionMap P t coordinate ⁻¹'
          (zeroLocus ∩ sourceLevels) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · exact
        presentationSectionMap_mem_relativeZeroLocus
          P t coordinate equation hzero
          (hrelation_of_mem z hz.1)
    · intro l
      rw [← hsection]
      change
        MvPolynomial.eval₂
            (Polynomial.evalRingHom t)
            (presentationSectionMap P t coordinate z)
            (objective l.1) =
          MvPolynomial.eval₂
            (Polynomial.evalRingHom t)
            (presentationSectionMap P t coordinate x)
            (objective l.1)
      rw [hobjective_section z hz.1 l.1,
        hobjective_section x (fun _ => rfl) l.1]
      exact hz.2 l
  have hlocalAt :
      IsLocalExtrOn
        (fun w : ν → ℝ =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom t) w
            (objective j))
        (zeroLocus ∩ sourceLevels)
        (presentationSectionMap P t coordinate x) := by
    simpa [zeroLocus, sourceLevels, hsection] using hlocal
  have hpull :
      IsLocalExtrOn
        ((fun w : ν → ℝ =>
            MvPolynomial.eval₂
              (Polynomial.evalRingHom t) w
              (objective j)) ∘
          presentationSectionMap P t coordinate)
        (fiber ∩ presentationLevels) x :=
    hlocalAt.comp_continuousOn
      (presentationSectionMap P t coordinate)
      hmaps
      (continuous_presentationSectionMap
        P t coordinate).continuousOn
      hxmem
  have heq :
      ((fun z : ι → ℝ =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom t)
            (presentationSectionMap
              P t coordinate z) (objective j)) :
        (ι → ℝ) → ℝ) =ᶠ[
          nhdsWithin x (fiber ∩ presentationLevels)]
        (fun z : ι → ℝ =>
          MvPolynomial.eval z
            (specializeParameterPolynomial t
              (P.σ (objectiveValue j)))) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hobjective_section z hz.1 j
  change
    IsLocalExtrOn
      (fun z : ι → ℝ =>
        MvPolynomial.eval z
          (specializeParameterPolynomial t
            (P.σ (objectiveValue j))))
      (fiber ∩ presentationLevels) x
  exact hpull.congr heq hxmem

end GateGRelativeLexPullback
end Math
