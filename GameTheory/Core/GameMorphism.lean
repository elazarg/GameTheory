/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameIsomorphism
import Math.Probability

/-!
# Game Morphisms

Morphisms between kernel-based games: structure-preserving maps that relate the
strategic structure of different games.

This file is distribution-first:
- morphisms preserve utility distributions (`udist`) under profile mapping;
- EU-based corollaries (Nash, dominance) are stated in explicitly EU-specialized
  structures.

## Main definitions

* `KernelGame.Morphism` -- strategy map preserving `udist`
* `KernelGame.EUMorphism` -- morphism with additional EU preservation
* `KernelGame.EUGameIsomorphism` -- game isomorphism with additional EU preservation

Solution-concept corollaries live in `GameTheory.Concepts.Foundations.GameMorphism`.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

-- ============================================================================
-- Game morphisms (distribution-preserving)
-- ============================================================================

/-- A morphism from game `G` to game `H`: per-player strategy maps that preserve
    the induced joint utility distribution. -/
structure Morphism (G H : KernelGame ι) where
  /-- Per-player strategy map. -/
  stratMap : ∀ i, G.Strategy i → H.Strategy i
  /-- Utility-distribution preservation under mapped profiles. -/
  udist_preserved : ∀ (σ : Profile G),
    H.udist (fun i => stratMap i (σ i)) = G.udist σ

namespace Morphism

/-- Two game morphisms are equal when their strategy maps agree pointwise. -/
@[ext]
theorem ext {G H : KernelGame ι} {f g : Morphism G H}
    (h : ∀ who strategy,
      f.stratMap who strategy = g.stratMap who strategy) :
    f = g := by
  cases f with
  | mk fStrat fUdist =>
      cases g with
      | mk gStrat gUdist =>
          have hStrat : fStrat = gStrat := by
            funext who strategy
            exact h who strategy
          cases hStrat
          rfl

/-- Identity morphism. -/
def id (G : KernelGame ι) : Morphism G G where
  stratMap := fun _i => _root_.id
  udist_preserved := by intro σ; rfl

/-- Composition of morphisms. -/
def comp {G H K : KernelGame ι} (g : Morphism H K) (f : Morphism G H) : Morphism G K where
  stratMap := fun i => g.stratMap i ∘ f.stratMap i
  udist_preserved := by
    intro σ
    let τ : Profile H := fun i => f.stratMap i (σ i)
    have hg : K.udist (fun i => g.stratMap i (τ i)) = H.udist τ := g.udist_preserved τ
    have hf : H.udist τ = G.udist σ := by simpa [τ] using f.udist_preserved σ
    simpa [τ, Function.comp] using hg.trans hf

@[simp] theorem id_comp {G H : KernelGame ι} (f : Morphism G H) :
    comp (id H) f = f := by
  cases f
  rfl

@[simp] theorem comp_id {G H : KernelGame ι} (f : Morphism G H) :
    comp f (id G) = f := by
  cases f
  rfl

theorem comp_assoc {G H K L : KernelGame ι}
    (h : Morphism K L) (g : Morphism H K) (f : Morphism G H) :
    comp h (comp g f) = comp (comp h g) f := by
  cases h; cases g; cases f
  rfl

end Morphism

/-- Forget invertibility and view a game isomorphism as a morphism. -/
def GameIsomorphism.toMorphism {G H : KernelGame ι}
    (e : GameIsomorphism G H) : Morphism G H where
  stratMap := fun i => e.stratEquiv i
  udist_preserved := e.udist_preserved

/-- Build a `Morphism` from an outcome embedding: when `G`'s outcome
distribution pushes forward to `H`'s under `embed`, and utilities agree
along the embedding, the embedding witnesses that `G` refines into `H`.

The natural recipe when `H` has *more* structure than `G` and `G`'s
outcomes inject into `H`'s — e.g., `G ↪ G.toOneStepStepwise` via
`some : G.Outcome → Option G.Outcome`. Utility agreement is required
only on the image, not on potential sentinels in `H.Outcome \ image embed`.
-/
def Morphism.ofOutcomeEmbedding {G H : KernelGame ι}
    (stratMap : ∀ i, G.Strategy i → H.Strategy i)
    (embed : G.Outcome → H.Outcome)
    (h_outcome : ∀ σ : Profile G,
      H.outcomeKernel (fun i => stratMap i (σ i))
        = (G.outcomeKernel σ).map embed)
    (h_util : ∀ ω, H.utility (embed ω) = G.utility ω) :
    Morphism G H where
  stratMap := stratMap
  udist_preserved := by
    intro σ
    change (H.outcomeKernel (fun i => stratMap i (σ i))).bind
        (fun ω => PMF.pure (H.utility ω))
      = (G.outcomeKernel σ).bind (fun ω => PMF.pure (G.utility ω))
    rw [h_outcome σ, PMF.bind_map]
    congr 1
    funext ω
    simp only [Function.comp, h_util]

/-- Build a `Morphism` from an outcome projection plus utility- and
outcome-kernel-along-projection equality. The recipe when `H` *abstracts*
`G` — `G`'s outcomes are read off as a projection of `H`'s. Utility
agreement is required only on the support of the target outcome kernel,
since `H` may carry sentinels off-support whose projected utility is
irrelevant.

Companion to `Morphism.ofOutcomeEmbedding` (the dual recipe when `G`
refines into `H`); each fits a different family of bridges. -/
def Morphism.ofOutcomeProjection {G H : KernelGame ι}
    (stratMap : ∀ i, G.Strategy i → H.Strategy i)
    (proj : H.Outcome → G.Outcome)
    (h_outcome : ∀ σ : Profile G,
      (H.outcomeKernel (fun i => stratMap i (σ i))).map proj
        = G.outcomeKernel σ)
    (h_util : ∀ σ : Profile G, ∀ ω ∈
        (H.outcomeKernel (fun i => stratMap i (σ i))).support,
      H.utility ω = G.utility (proj ω)) :
    Morphism G H where
  stratMap := stratMap
  udist_preserved := by
    intro σ
    change (H.outcomeKernel (fun i => stratMap i (σ i))).bind
        (fun ω => PMF.pure (H.utility ω))
      = (G.outcomeKernel σ).bind (fun ω => PMF.pure (G.utility ω))
    rw [← h_outcome σ, PMF.bind_map]
    refine (Math.ProbabilityMassFunction.bind_congr_on_support
      (H.outcomeKernel (fun i => stratMap i (σ i)))
      (fun ω => PMF.pure (H.utility ω))
      (fun ω => PMF.pure (G.utility (proj ω))) ?_).trans ?_
    · intro ω hω
      simp only [h_util σ ω hω]
    · rfl

@[simp] theorem Morphism.ofOutcomeEmbedding_stratMap {G H : KernelGame ι}
    (stratMap : ∀ i, G.Strategy i → H.Strategy i)
    (embed : G.Outcome → H.Outcome)
    (h_outcome : ∀ σ : Profile G,
      H.outcomeKernel (fun i => stratMap i (σ i))
        = (G.outcomeKernel σ).map embed)
    (h_util : ∀ ω, H.utility (embed ω) = G.utility ω) :
    (Morphism.ofOutcomeEmbedding stratMap embed h_outcome h_util).stratMap
      = stratMap := rfl

@[simp] theorem Morphism.ofOutcomeProjection_stratMap {G H : KernelGame ι}
    (stratMap : ∀ i, G.Strategy i → H.Strategy i)
    (proj : H.Outcome → G.Outcome)
    (h_outcome : ∀ σ : Profile G,
      (H.outcomeKernel (fun i => stratMap i (σ i))).map proj
        = G.outcomeKernel σ)
    (h_util : ∀ σ : Profile G, ∀ ω ∈
        (H.outcomeKernel (fun i => stratMap i (σ i))).support,
      H.utility ω = G.utility (proj ω)) :
    (Morphism.ofOutcomeProjection stratMap proj h_outcome h_util).stratMap
      = stratMap := rfl

/-- `udist` preservation implies per-player utility-distribution preservation. -/
theorem Morphism.udistPlayer_preserved {G H : KernelGame ι} (f : Morphism G H)
    (σ : Profile G) (who : ι) :
    H.udistPlayer (fun i => f.stratMap i (σ i)) who = G.udistPlayer σ who := by
  have h :=
    congrArg (fun d : PMF (Payoff ι) => d.bind (fun u => PMF.pure (u who))) (f.udist_preserved σ)
  simpa [KernelGame.udistPlayer_eq_udist_bind] using h

/-- Utility-distribution preservation for an isomorphism implies per-player
utility-distribution preservation through its underlying morphism. -/
theorem GameIsomorphism.udistPlayer_preserved {G H : KernelGame ι}
    (e : GameIsomorphism G H) (σ : Profile G) (who : ι) :
    H.udistPlayer (fun i => e.stratEquiv i (σ i)) who = G.udistPlayer σ who :=
  e.toMorphism.udistPlayer_preserved σ who

/-- Expected utility is the expectation of the corresponding coordinate of
the utility-vector distribution under a bounded utility hypothesis. -/
theorem expect_udist_eq_eu_of_bounded (G : KernelGame ι)
    (σ : Profile G) (who : ι)
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    Math.Probability.expect (G.udist σ) (fun u => u who) =
      G.eu σ who := by
  rw [KernelGame.udist, KernelGame.eu]
  rw [Math.ProbabilityMassFunction.bind_pure_eq_pushforward]
  exact Math.ProbabilityMassFunction.expect_pushforward_of_bounded_on_source
    (G.outcomeKernel σ) G.utility (fun u => u who) hbd

/-- Expected utility is the expectation of the corresponding coordinate of
the utility-vector distribution. Unconditional: `udist` is a deterministic
pushforward of `outcomeKernel` through `utility`, and the pushforward
change-of-variables `Math.Probability.expect_map` carries no finiteness or
boundedness hypotheses. This strictly generalizes
`expect_udist_eq_eu_of_bounded`. -/
theorem expect_udist_eq_eu (G : KernelGame ι)
    (σ : Profile G) (who : ι) :
    Math.Probability.expect (G.udist σ) (fun u => u who) =
      G.eu σ who := by
  rw [KernelGame.udist, KernelGame.eu]
  rw [Math.ProbabilityMassFunction.bind_pure_eq_pushforward]
  exact Math.Probability.expect_map G.utility (G.outcomeKernel σ) (fun u => u who)

/-- A utility-distribution preserving morphism also preserves expected utility
under bounded utilities. The semantic content is already `udist_preserved`;
boundedness only justifies reading expectations of utility coordinates. -/
theorem Morphism.eu_preserved_of_bounded {G H : KernelGame ι}
    (f : Morphism G H)
    {C_G C_H : ι → ℝ}
    (hbdG : ∀ who ω, |G.utility ω who| ≤ C_G who)
    (hbdH : ∀ who ω, |H.utility ω who| ≤ C_H who)
    (σ : Profile G) (who : ι) :
    H.eu (fun i => f.stratMap i (σ i)) who = G.eu σ who := by
  calc
    H.eu (fun i => f.stratMap i (σ i)) who =
        Math.Probability.expect
          (H.udist (fun i => f.stratMap i (σ i))) (fun u => u who) := by
          exact (expect_udist_eq_eu_of_bounded H
            (fun i => f.stratMap i (σ i)) who (hbdH who)).symm
    _ =
        Math.Probability.expect (G.udist σ) (fun u => u who) := by
          rw [f.udist_preserved σ]
    _ = G.eu σ who := by
          exact expect_udist_eq_eu_of_bounded G σ who (hbdG who)

/-- A utility-distribution preserving morphism also preserves expected utility
when both outcome carriers are finite. -/
theorem Morphism.eu_preserved_of_fintype_outcome {G H : KernelGame ι}
    [Finite G.Outcome] [Finite H.Outcome] (f : Morphism G H)
    (σ : Profile G) (who : ι) :
    H.eu (fun i => f.stratMap i (σ i)) who = G.eu σ who := by
  let C_G : ι → ℝ := fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun ω => G.utility ω who)).choose
  have hbdG : ∀ who ω, |G.utility ω who| ≤ C_G who := fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun ω => G.utility ω who)).choose_spec
  let C_H : ι → ℝ := fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun ω => H.utility ω who)).choose
  have hbdH : ∀ who ω, |H.utility ω who| ≤ C_H who := fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun ω => H.utility ω who)).choose_spec
  exact f.eu_preserved_of_bounded hbdG hbdH σ who

/-- A utility-distribution preserving morphism preserves expected utility,
unconditionally. Special case of `eu_preserved_of_bounded`/
`eu_preserved_of_fintype_outcome` made possible by the unconditional
`expect_udist_eq_eu`: no boundedness or finiteness hypothesis on either
game's utility is needed. -/
theorem Morphism.eu_preserved {G H : KernelGame ι}
    (f : Morphism G H) (σ : Profile G) (who : ι) :
    H.eu (fun i => f.stratMap i (σ i)) who = G.eu σ who := by
  calc
    H.eu (fun i => f.stratMap i (σ i)) who =
        Math.Probability.expect
          (H.udist (fun i => f.stratMap i (σ i))) (fun u => u who) :=
          (expect_udist_eq_eu H (fun i => f.stratMap i (σ i)) who).symm
    _ = Math.Probability.expect (G.udist σ) (fun u => u who) := by
          rw [f.udist_preserved σ]
    _ = G.eu σ who := expect_udist_eq_eu G σ who

-- ============================================================================
-- EU-specialized morphisms
-- ============================================================================

/-- A morphism that additionally preserves expected utility values. -/
structure EUMorphism (G H : KernelGame ι) extends Morphism G H where
  /-- Expected-utility preservation under mapped profiles. -/
  eu_preserved : ∀ (σ : Profile G) (who : ι),
    H.eu (fun i => stratMap i (σ i)) who = G.eu σ who

/-- Upgrade a finite-outcome utility-distribution morphism to the EU-specialized
morphism expected by solution-concept transport theorems. -/
def Morphism.toEUMorphismOfFintypeOutcome {G H : KernelGame ι}
    [Finite G.Outcome] [Finite H.Outcome] (f : Morphism G H) :
    EUMorphism G H where
  toMorphism := f
  eu_preserved := f.eu_preserved_of_fintype_outcome

/-- Upgrade a bounded utility-distribution morphism to the EU-specialized
morphism expected by solution-concept transport theorems. -/
def Morphism.toEUMorphismOfBounded {G H : KernelGame ι}
    (f : Morphism G H)
    {C_G C_H : ι → ℝ}
    (hbdG : ∀ who ω, |G.utility ω who| ≤ C_G who)
    (hbdH : ∀ who ω, |H.utility ω who| ≤ C_H who) :
    EUMorphism G H where
  toMorphism := f
  eu_preserved := f.eu_preserved_of_bounded hbdG hbdH

/-- Upgrade any utility-distribution morphism to the EU-specialized morphism
expected by solution-concept transport theorems, unconditionally. Special
case of `toEUMorphismOfBounded`/`toEUMorphismOfFintypeOutcome` made possible
by the unconditional `Morphism.eu_preserved`. -/
def Morphism.toEUMorphism {G H : KernelGame ι} (f : Morphism G H) :
    EUMorphism G H where
  toMorphism := f
  eu_preserved := f.eu_preserved

namespace EUMorphism

/-- Identity EU morphism. -/
def id (G : KernelGame ι) : EUMorphism G G where
  toMorphism := Morphism.id G
  eu_preserved := by intro σ who; rfl

/-- Composition of EU morphisms. -/
def comp {G H K : KernelGame ι} (g : EUMorphism H K) (f : EUMorphism G H) : EUMorphism G K where
  toMorphism := Morphism.comp g.toMorphism f.toMorphism
  eu_preserved := by
    intro σ who
    let τ : Profile H := fun i => f.stratMap i (σ i)
    have hg : K.eu (fun i => g.stratMap i (τ i)) who = H.eu τ who := g.eu_preserved τ who
    have hf : H.eu τ who = G.eu σ who := by simpa [τ] using f.eu_preserved σ who
    exact hg.trans hf

@[simp] theorem id_comp {G H : KernelGame ι} (f : EUMorphism G H) :
    comp (id H) f = f := by
  cases f
  rfl

@[simp] theorem comp_id {G H : KernelGame ι} (f : EUMorphism G H) :
    comp f (id G) = f := by
  cases f
  rfl

theorem comp_assoc {G H K L : KernelGame ι}
    (h : EUMorphism K L) (g : EUMorphism H K) (f : EUMorphism G H) :
    comp h (comp g f) = comp (comp h g) f := by
  cases h; cases g; cases f
  rfl

end EUMorphism

-- ============================================================================
-- EU-specialized game isomorphisms
-- ============================================================================

/-- A game isomorphism with additional EU preservation. -/
structure EUGameIsomorphism (G H : KernelGame ι) extends GameIsomorphism G H where
  /-- Expected-utility preservation under the isomorphism. -/
  eu_preserved : ∀ (σ : Profile G) (who : ι),
    H.eu (fun i => stratEquiv i (σ i)) who = G.eu σ who

/-- Every utility-distribution-preserving game isomorphism preserves expected
utility.  This is unconditional because expected utility is the expectation of
the corresponding coordinate of `udist`. -/
def GameIsomorphism.toEUGameIsomorphism {G H : KernelGame ι}
    (e : GameIsomorphism G H) : EUGameIsomorphism G H where
  toGameIsomorphism := e
  eu_preserved := e.toMorphism.eu_preserved

@[simp]
theorem GameIsomorphism.toEUGameIsomorphism_toGameIsomorphism
    {G H : KernelGame ι} (e : GameIsomorphism G H) :
    e.toEUGameIsomorphism.toGameIsomorphism = e :=
  rfl

namespace EUGameIsomorphism

variable {G H : KernelGame ι}

/-- Two EU game isomorphisms are equal when their strategy equivalences agree
pointwise. Expected-utility preservation is proof data. -/
@[ext]
theorem ext {e f : EUGameIsomorphism G H}
    (h : ∀ who strategy,
      e.stratEquiv who strategy = f.stratEquiv who strategy) :
    e = f := by
  cases e with
  | mk eGame _ =>
      cases f with
      | mk fGame _ =>
          have hGame : eGame = fGame := GameIsomorphism.ext h
          cases hGame
          rfl

/-- Identity EU-preserving game isomorphism. -/
def id (G : KernelGame ι) : EUGameIsomorphism G G :=
  (GameIsomorphism.id G).toEUGameIsomorphism

/-- An EU-preserving game isomorphism induces an EU-preserving morphism. -/
def toEUMorphism (e : EUGameIsomorphism G H) : EUMorphism G H where
  toMorphism := e.toGameIsomorphism.toMorphism
  eu_preserved := e.eu_preserved

/-- Inverse EU-preserving game isomorphism. -/
def symm (e : EUGameIsomorphism G H) : EUGameIsomorphism H G where
  toGameIsomorphism := e.toGameIsomorphism.symm
  eu_preserved := by
    intro σ who
    have h := e.eu_preserved (fun i => (e.stratEquiv i).symm (σ i)) who
    change G.eu (fun i => (e.stratEquiv i).symm (σ i)) who =
      H.eu (fun i => σ i) who
    simpa using h.symm

/-- Composition of EU-preserving game isomorphisms. -/
def comp {G H K : KernelGame ι}
    (g : EUGameIsomorphism H K) (f : EUGameIsomorphism G H) :
    EUGameIsomorphism G K :=
  (GameIsomorphism.comp g.toGameIsomorphism f.toGameIsomorphism).toEUGameIsomorphism

@[simp] theorem id_comp (e : EUGameIsomorphism G H) :
    comp (id H) e = e := by
  apply ext
  intro who strategy
  rfl

@[simp] theorem comp_id (e : EUGameIsomorphism G H) :
    comp e (id G) = e := by
  apply ext
  intro who strategy
  rfl

theorem comp_assoc {G H K L : KernelGame ι}
    (h : EUGameIsomorphism K L) (g : EUGameIsomorphism H K)
    (f : EUGameIsomorphism G H) :
    comp h (comp g f) = comp (comp h g) f := by
  apply ext
  intro who strategy
  rfl

@[simp] theorem symm_symm (e : EUGameIsomorphism G H) :
    e.symm.symm = e := by
  apply ext
  intro who strategy
  change (e.stratEquiv who).symm.symm strategy = e.stratEquiv who strategy
  simp

@[simp] theorem id_symm (G : KernelGame ι) :
    (id G).symm = id G := by
  apply ext
  intro who strategy
  rfl

end EUGameIsomorphism

end KernelGame

end GameTheory
