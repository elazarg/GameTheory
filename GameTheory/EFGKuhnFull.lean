import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions

import GameTheory.EFGKuhn

/-!
# Kuhn's Theorem: Mixed-to-Behavioral Strategy Equivalence

For any extensive-form game with **perfect recall**, every mixed strategy profile
induces the same outcome distribution as some behavioral strategy profile.
This is Kuhn's (1953) foundational result in game theory.

## Theorem statement

`kuhn_mixed_to_behavioral`: Given a game tree `t` with perfect recall and a
mixed strategy profile `muP`, there exists a behavioral profile `σ` such that
`t.evalDist σ = (mixedProfileJoint muP).bind
  (fun π => t.evalDist (pureToBehavioral π))`.

## Proof architecture

The proof works on **flat profiles**
(`FlatProfile S = (idx : FlatIdx S) → S.Act idx.2`),
which are equivalent to pure strategy profiles but index by `(player, infoset)`
pairs rather than nested dependent functions. A mixed strategy profile `muP`
induces a product PMF on flat profiles via
`pmfPureToFlat (mixedProfileJoint muP)`.

### Key idea: sequential conditioning preserves product structure

The behavioral strategy at infoset `I` of player `p` is defined as the
conditional distribution of action at `I`, given the history of decisions
leading to `I`. Because `muP` is a product over players, conditioning on one
player's past decisions does not affect other players' marginals
(`muMarginal_muCond_other`). This **player-independence** property
(`PlayerIndep`) is preserved through arbitrary conditioning sequences
(`PlayerIndep_muCondPath`).

### The three pillars

1. **Product conditioning algebra** (§ 1): `muCond` on the flat product
   decomposes via `pureCond` on the pure-strategy product. Conditioning
   commutes across players (`muCond_comm_of_PlayerIndep`) and preserves
   cross-player marginals.

2. **Path filtering and perfect recall** (§ 2): A decision path `pi` to
   infoset `I` can be filtered to player `q`'s decisions
   (`FilterPlayer q pi`). Perfect recall guarantees this filtered history is
   the same regardless of which path reaches `I`
   (`FilterPlayer_path_eq_history`). The marginal after conditioning on the
   full path equals the marginal after conditioning on just `q`'s filtered
   path (`muMarginal_condPath_invariant_filter`).

3. **Inductive evaluation** (§ 3): By structural induction on the game tree,
   `evalDist σ u = (muCondPath mu pi).bind (evalFlat · u)` for every subtree
   `u` reached by path `pi`. At decision nodes, the behavioral strategy
   matches the conditional marginal by construction. At chance nodes, Fubini
   swaps the bind order.

### Notable proof techniques

- **ENNReal arithmetic**: Division `a / b` is definitionally `a * b⁻¹`, so
  `mul_right_comm` replaces `ring` (ENNReal is not a ring) and
  `div_right_comm` (no `DivisionCommMonoid` instance).

- **Dependent type transport for `GoodPath`**: When two PMFs are
  propositionally equal (`mu1 = mu2`), `GoodPath mu1 path` and
  `GoodPath mu2 path` are not definitionally equal (they're `PSigma` chains).
  We use `cast` + a helper `muCondPath_eq_of_eq` rather than `subst` (which
  requires variables) or `cases` (which can't decompose non-variable
  equalities).

- **`muCond_app` local unfolding**: To prove `muCond` commutativity, we
  unfold `muCond` only at top-level application
  (`(muCond ..) s = if .. then .. else ..`) via a local lemma, preserving
  `muMarginal J (muCond ..)` as an opaque subterm so that cross-player
  marginal invariance (`hJsame`, `hIsame`) can rewrite it.

## References

- Kuhn, H.W. (1953). "Extensive Games and the Problem of Information."
  Contributions to the Theory of Games, Vol. II. Annals of Mathematics
  Studies 28.

## Dependencies

- `GameTheory.EFG`: `InfoStructure`, `GameTree`, `PerfectRecall`, `ReachBy`,
  `playerHistory`, `MixedProfile`, `BehavioralProfile`
- `GameTheory.PMFProduct`: `pmfPi`, `pmfMass`, `pmfMask`, `pmfCond`,
  `pmfPi_cond_coord`, `pmfPi_cond_coord_push_other`
-/

namespace EFG

open scoped BigOperators

variable {S : InfoStructure} {Outcome : Type}


instance (p : S.Player) : DecidableEq (PureStrategy S p) :=
  show DecidableEq ((I : S.Infoset p) → S.Act I) from inferInstance
instance : DecidableEq (PureProfile S) :=
  show DecidableEq ((p : S.Player) → PureStrategy S p) from
    Fintype.decidablePiFintype

noncomputable def mixedProfileJoint (muP : MixedProfile S) : PMF (PureProfile S) :=
  pmfPi (A := fun p => PureStrategy S p) muP

def flatProfileEquivPureProfile : Equiv (FlatProfile S) (PureProfile S) where
  toFun := fun s p I => s ⟨p, I⟩
  invFun := fun pi idx => pi idx.1 idx.2
  left_inv := by intro s; funext idx; cases idx; rfl
  right_inv := by intro pi; funext p I; rfl

noncomputable def pmfPureToFlat (mu : PMF (PureProfile S)) : PMF (FlatProfile S) :=
  mu.bind (fun pi => PMF.pure (flatProfileEquivPureProfile.symm pi))

noncomputable def muMarginal {p : S.Player} (I : S.Infoset p)
    (mu : PMF (FlatProfile S)) : PMF (S.Act I) :=
  mu.bind (fun s => PMF.pure (s ⟨p, I⟩))

noncomputable def muCond {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S)) (hpa : muMarginal (S := S) I mu a ≠ 0) : PMF (FlatProfile S) :=
  PMF.ofFintype
    (fun s => if s ⟨p, I⟩ = a then mu s / (muMarginal (S := S) I mu a) else 0)
    (by
      rw [show (∑ s, if s ⟨p, I⟩ = a then mu s / muMarginal (S := S) I mu a
            else (0 : ENNReal)) =
          (∑ s, (if s ⟨p, I⟩ = a
          then (mu s : ENNReal) else 0) * (muMarginal (S := S) I mu a)⁻¹) from
        Finset.sum_congr rfl (fun s _ => by split_ifs <;> simp [div_eq_mul_inv]),
        ← Finset.sum_mul]
      have hsum : (∑ s : FlatProfile S, if s ⟨p, I⟩ = a then (mu s : ENNReal) else 0)
          = muMarginal (S := S) I mu a := by
        change _ = (mu.bind (fun s => PMF.pure (s ⟨p, I⟩)) ) a
        simp_all [PMF.bind_apply, PMF.pure_apply, tsum_fintype, mul_ite, mul_one, mul_zero]
        grind
      rw [hsum]
      exact ENNReal.mul_inv_cancel hpa
        (ENNReal.ne_top_of_tsum_ne_top
          (PMF.tsum_coe (muMarginal (S := S) I mu) ▸ ENNReal.one_ne_top) a))

/-- A flat PMF is **player-independent** if it arises as the pushforward of a product
of per-player mixed strategies. This is the key structural property preserved
through conditioning. -/
abbrev PlayerIndep (mu : PMF (FlatProfile S)) : Prop :=
  ∃ muP : MixedProfile S, mu = pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)

---
-- Product Conditioning Algebra
---

lemma pmfPureToFlat_apply (mu : PMF (PureProfile S)) (s : FlatProfile S) :
    pmfPureToFlat (S := S) mu s = ∑ pi : PureProfile S,
      mu pi * (if flatProfileEquivPureProfile.symm pi = s then 1 else 0) := by
  simp [pmfPureToFlat, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
    mul_ite, mul_one, mul_zero, eq_comm]

/-- `pmfPureToFlat mu` at flat profile `s` equals `mu` at the corresponding pure profile. -/
lemma pmfPureToFlat_eq (mu : PMF (PureProfile S)) (s : FlatProfile S) :
    pmfPureToFlat (S := S) mu s =
    mu (flatProfileEquivPureProfile (S := S) s) := by
  rw [pmfPureToFlat_apply]
  have : ∀ pi : PureProfile S,
      mu pi * (if flatProfileEquivPureProfile.symm pi = s then 1 else 0) =
      if pi = flatProfileEquivPureProfile (S := S) s then mu pi else 0 := by
    intro pi
    simp only [Equiv.symm_apply_eq]
    split_ifs with h <;> simp [h]
  simp_rw [this]
  simp [Finset.sum_ite_eq']

/-- Predicate on player `p`’s pure strategy at infoset `I`. -/
def Ep {p : S.Player} (I : S.Infoset p) (a : S.Act I) : PureStrategy S p → Prop :=
  fun sp => sp I = a

instance {p : S.Player} {I : S.Infoset p} {a : S.Act I} :
    DecidablePred (Ep (S := S) I a) :=
  fun sp => show Decidable (sp I = a) from inferInstance

instance {p : S.Player} {I : S.Infoset p} {a : S.Act I} :
    DecidablePred (fun (π : PureProfile S) => Ep (S := S) I a (π p)) :=
  fun π => show Decidable (π p I = a) from inferInstance

/-- The flat marginal at infoset I equals the pure-side pushforward. -/
lemma muMarginal_pmfPureToFlat_eq (mu : PMF (PureProfile S))
    {p : S.Player} (I : S.Infoset p) (a : S.Act I) :
    muMarginal (S := S) I (pmfPureToFlat (S := S) mu) a =
    pmfMass (μ := mu) (fun π => Ep (S := S) I a (π p)) := by
  simp only [muMarginal, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
    pmfPureToFlat_eq, mul_ite, mul_one, mul_zero]
  simp only [pmfMass, pmfMask, Ep]
  -- Reindex: FlatProfile → PureProfile via the equivalence
  exact Fintype.sum_equiv (flatProfileEquivPureProfile (S := S)) _ _
    (fun s => by simp [flatProfileEquivPureProfile, eq_comm])

/-- Condition the product PMF on the coordinate event `π p I = a`
 (depends only on coordinate `p`). -/
noncomputable def pureCond (muP : MixedProfile S) {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0) : PMF (PureProfile S) :=
  pmfCond (μ := mixedProfileJoint (S := S) muP)
    (fun π => Ep (S := S) I a (π p))
    (by
      change pmfMass (μ := pmfPi (A := fun q => PureStrategy S q) muP)
        (fun π => Ep (S := S) I a (π p)) ≠ 0
      rwa [pmfMass_pmfPi_coord (A := fun q => PureStrategy S q)
        (σ := muP) (j := p) (E := Ep (S := S) I a)])

/-- The key bridge: flat-side conditioning (`muCond`) on a product measure equals the
pushforward of pure-side conditioning (`pureCond`). This reduces all flat conditioning
questions to the product PMF machinery in `PMFProduct`. -/
theorem muCond_eq_pmfPureToFlat_pureCond
    (muP : MixedProfile S)
    {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (hpa_flat :
      muMarginal (S := S) I
        (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) a ≠ 0)
    (hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0) :
    muCond (S := S) I a
      (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa_flat
      =
    pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
  let e := flatProfileEquivPureProfile (S := S)
  let mu := mixedProfileJoint (S := S) muP
  -- The two denominators are equal
  have hd_eq : muMarginal (S := S) I (pmfPureToFlat (S := S) mu) a =
      pmfMass (μ := mu) (fun π => Ep (S := S) I a (π p)) :=
    muMarginal_pmfPureToFlat_eq mu I a
  ext s
  -- Key facts
  have hep : Ep (S := S) I a ((e s) p) ↔ s ⟨p, I⟩ = a := by
    simp [Ep, e, flatProfileEquivPureProfile]
  -- Expand everything at once
  simp only [muCond, PMF.ofFintype_apply, pmfPureToFlat_eq,
    pureCond, pmfCond_apply, pmfMask]
  -- After simp: LHS has if s⟨p,I⟩=a then mu(es)/muMarginal else 0
  --             RHS has (if Ep .. then mu(es) else 0) / pmfMass
  -- Both conditionals equivalent, both denominators equal
  rw [hd_eq]
  by_cases hs : s ⟨p, I⟩ = a
  · rw [if_pos hs, if_pos (hep.mpr hs)]
  · rw [if_neg hs, if_neg (show ¬ Ep (S := S) I a ((e s) p)
      from (not_congr hep).mpr hs)]
    simp

/-- Conditioning preserves player-independence, and cross-player marginals
are invariant. These two facts are the engine of the entire proof. -/
theorem PlayerIndep_pmfPureToFlat (muP : MixedProfile S) :
    PlayerIndep (S := S) (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) := by
  exact ⟨muP, rfl⟩

theorem PlayerIndep_muCond
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {p : S.Player} {I : S.Infoset p} {a : S.Act I}
    (hpa : muMarginal (S := S) I mu a ≠ 0) :
    PlayerIndep (S := S) (muCond (S := S) I a mu hpa) := by
  rcases hind with ⟨muP, rfl⟩
  -- derive the pure-side nonzero mass (you can prove this from `hpa` if you want;
  -- for now, just define it using classical choice + the fact it must be nonzero
  -- because pushforward to flat has nonzero mass).
  have hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0 := by
    rwa [← pmfMass_pmfPi_coord (A := fun q => PureStrategy S q)
      (σ := muP) (j := p) (E := Ep (S := S) I a),
      ← muMarginal_pmfPureToFlat_eq]
  refine ⟨Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE), ?_⟩
  -- Use the bridge lemma + the PMFProduct “conditioning a product updates only that coordinate”
  -- on the pure side:
  have hpure :
      pureCond (S := S) muP I a hE
        =
      mixedProfileJoint (S := S)
        (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE)) := by
    -- This is exactly `pmfPi_cond_coord` specialized to index = players, event on coordinate p.
    -- (your PMFProduct lemma)
    exact pmfPi_cond_coord
      (A := fun q => PureStrategy S q) muP p
      (Ep (S := S) I a) hE
  -- finish
  calc
    muCond (S := S) I a (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa
        =
      pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
          simpa using (muCond_eq_pmfPureToFlat_pureCond (S := S) muP I a hpa hE)
    _ = pmfPureToFlat (S := S)
          (mixedProfileJoint (S := S)
            (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE))) := by
          simp [hpure]
    _ = pmfPureToFlat (S := S) (mixedProfileJoint (S := S)
            (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE))) := rfl

theorem muMarginal_muCond_other
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {p q : S.Player}
    (hpq : q ≠ p)
    {I : S.Infoset p}
    {J : S.Infoset q}
    {a : S.Act I}
    (hpa : muMarginal (S := S) I mu a ≠ 0) :
    muMarginal (S := S) J (muCond (S := S) I a mu hpa) =
    muMarginal (S := S) J mu := by
  rcases hind with ⟨muP, rfl⟩
  -- same pure-side nonzero mass as above
  have hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0 := by
    rwa [← pmfMass_pmfPi_coord (A := fun q => PureStrategy S q)
      (σ := muP) (j := p) (E := Ep (S := S) I a),
      ← muMarginal_pmfPureToFlat_eq]
  -- rewrite `muCond` as pushforward of pure-side conditioning
  have hrew :
      muCond (S := S) I a (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa
        =
      pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
    simpa using (muCond_eq_pmfPureToFlat_pureCond (S := S) muP I a hpa hE)
  -- now apply the PMFProduct lemma: conditioning the product on coordinate p
  -- doesn’t change other coordinate marginals (q ≠ p), and pushforward commutes.
  --
  -- Concretely, marginal at infoset J of player q is pushforward along `π ↦ π q J`.
  -- On the pure side, that’s still coordinate q (as a PureStrategy) then apply at J.
  -- This is one more “pushforward-compose” lemma + `pmfPi_cond_coord_push_other`.
  -- Unfold muMarginal and rewrite muCond via hrew
  simp only [muMarginal, hrew]
  -- Goal: pmfPureToFlat(pureCond).bind(s↦pure(s⟨q,J⟩)) =
  --       pmfPureToFlat(joint).bind(s↦pure(s⟨q,J⟩))
  -- Unfold pmfPureToFlat and simplify to get pure-side binds
  simp only [pmfPureToFlat, PMF.bind_bind, PMF.pure_bind]
  -- Goal: (pureCond muP I a hE).bind (· q J |> PMF.pure) =
  --       (mixedProfileJoint muP).bind (· q J |> PMF.pure)
  -- Factor through pushforward at coordinate q
  calc (pureCond (S := S) muP I a hE).bind
        (fun pi => PMF.pure (pi q J))
      = ((pureCond (S := S) muP I a hE).bind
          (fun pi => PMF.pure (pi q))).bind
          (fun sq => PMF.pure (sq J)) := by
        simp only [PMF.bind_bind, PMF.pure_bind]
    _ = ((mixedProfileJoint (S := S) muP).bind
          (fun pi => PMF.pure (pi q))).bind
          (fun sq => PMF.pure (sq J)) := by
        congr 1
        exact (pmfPi_cond_coord_push_other
          (A := fun q => PureStrategy S q) muP hpq
          (Ep (S := S) I a) hE).trans
          (pmfPi_push_coord
            (A := fun q => PureStrategy S q) muP q).symm
    _ = (mixedProfileJoint (S := S) muP).bind
          (fun pi => PMF.pure (pi q J)) := by
        simp only [PMF.bind_bind, PMF.pure_bind]

theorem muCond_comm_of_PlayerIndep
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {p q : S.Player} (hpq : p ≠ q)
    {I : S.Infoset p} {a : S.Act I}
    {J : S.Infoset q} {b : S.Act J}
    (hpa : muMarginal (S := S) I mu a ≠ 0)
    (hpb : muMarginal (S := S) J mu b ≠ 0) :
    muCond (S := S) J b (muCond (S := S) I a mu hpa)
      (by
        have : muMarginal (S := S) J (muCond (S := S) I a mu hpa) b =
            muMarginal (S := S) J mu b :=
          congrArg (fun ν => ν b)
            (muMarginal_muCond_other (S := S) mu hind
              (Ne.symm hpq) hpa)
        simpa [this] using hpb)
      =
    muCond (S := S) I a (muCond (S := S) J b mu hpb)
      (by
        have : muMarginal (S := S) I (muCond (S := S) J b mu hpb) a =
            muMarginal (S := S) I mu a :=
          congrArg (fun ν => ν a)
            (muMarginal_muCond_other (S := S) mu hind hpq hpb)
        simpa [this] using hpa) := by
  have muCond_app : ∀ {p'} {I' : S.Infoset p'} {a' : S.Act I'}
      {mu' : PMF (FlatProfile S)} {h' : muMarginal (S := S) I' mu' a' ≠ 0}
      (s : FlatProfile S),
      (muCond (S := S) I' a' mu' h') s =
        if s ⟨p', I'⟩ = a' then mu' s / muMarginal (S := S) I' mu' a' else 0 := by
    intros; simp [muCond, PMF.ofFintype_apply]
  ext s
  simp only [muCond_app]
  have hJsame :
      muMarginal (S := S) J (muCond (S := S) I a mu hpa) b =
      muMarginal (S := S) J mu b :=
    congrArg (fun ν => ν b)
      (muMarginal_muCond_other (S := S) mu hind (Ne.symm hpq) hpa)
  have hIsame :
      muMarginal (S := S) I (muCond (S := S) J b mu hpb) a =
      muMarginal (S := S) I mu a :=
    congrArg (fun ν => ν a)
      (muMarginal_muCond_other (S := S) mu hind hpq hpb)
  by_cases hsi : s ⟨p, I⟩ = a
  · by_cases hsj : s ⟨q, J⟩ = b
    · simp only [hsj, ite_true, hsi]
      rw [hJsame, hIsame]
      exact mul_right_comm _ _ _
    · simp [hsi, hsj]
  · by_cases hsj : s ⟨q, J⟩ = b
    · simp [hsi, hsj]
    · simp [hsi, hsj]

---
-- Path Conditioning, Filtering, and Perfect Recall
--
-- A `DecPath` records the sequence of player decisions along a path from the root.
-- `GoodPath mu path` witnesses that each step has nonzero marginal mass,
-- allowing sequential conditioning. `FilterPlayer q path` extracts only player
-- `q`'s decisions. The main result of this section is
-- `muMarginal_condPath_invariant_filter`: the marginal at `q`'s infoset after
-- conditioning on the full path equals the marginal after conditioning on just
-- `q`'s filtered path. Combined with perfect recall (`FilterPlayer_path_eq_history`),
-- this means the behavioral strategy at each infoset depends only on the
-- canonical history, not on the particular path to the infoset.
---

structure DecConstraint (S : InfoStructure) where
  p : S.Player
  I : S.Infoset p
  a : S.Act I
deriving DecidableEq

abbrev DecPath (S : InfoStructure) := List (DecConstraint S)

def Satisfies (s : FlatProfile S) (c : DecConstraint S) : Prop :=
  s ⟨c.p, c.I⟩ = c.a

def SatisfiesPath (s : FlatProfile S) (path : DecPath S) : Prop :=
  ∀ c, c ∈ path -> Satisfies (S := S) s c

/-- Evidence that we can condition along `path` step-by-step (each step has nonzero mass). -/
def GoodPath {S} (mu : PMF (FlatProfile S)) : DecPath S → Type
  | [] => PUnit
  | c :: cs =>
      Σ' h : muMarginal (S := S) c.I mu c.a ≠ 0,
        GoodPath (S := S) (muCond (S := S) c.I c.a mu h) cs

noncomputable def muCondPath {S} :
    (mu : PMF (FlatProfile S)) → (path : DecPath S)
     → GoodPath (S := S) mu path → PMF (FlatProfile S)
  | mu, [], _ => mu
  | mu, c :: cs, ⟨h, hgood⟩ =>
      muCondPath (S := S) (mu := muCond (S := S) c.I c.a mu h) (path := cs) hgood

@[simp] lemma muCondPath_nil (mu : PMF (FlatProfile S)) (h : GoodPath (S := S) mu []) :
    muCondPath (S := S) (mu := mu) (path := []) h = mu := rfl

@[simp] lemma muCondPath_cons (mu : PMF (FlatProfile S)) (c : DecConstraint S) (cs : DecPath S)
    (h : GoodPath (S := S) mu (c :: cs)) :
    muCondPath (S := S) (mu := mu) (path := c :: cs) h =
      muCondPath (S := S)
        (mu := muCond (S := S) c.I c.a mu h.1)
        (path := cs) h.2 := rfl

/-- `muCond` doesn't depend on which proof of nonzero mass is used. -/
theorem muCond_irrel {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S))
    (h1 h2 : muMarginal (S := S) I mu a ≠ 0) :
    muCond (S := S) I a mu h1 = muCond (S := S) I a mu h2 := rfl

/-- `muCondPath` doesn't depend on which `GoodPath` witness is used. -/
theorem muCondPath_irrel (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hg₁ hg₂ : GoodPath (S := S) mu path) :
    muCondPath (S := S) mu path hg₁ = muCondPath (S := S) mu path hg₂ := by
  induction path generalizing mu with
  | nil => rfl
  | cons c cs ih => exact ih (muCond (S := S) c.I c.a mu hg₁.1) hg₁.2 hg₂.2

/-- `muCondPath` is invariant under equal distributions. -/
theorem muCondPath_eq_of_eq
    {mu1 mu2 : PMF (FlatProfile S)} (h : mu1 = mu2)
    {path : DecPath S}
    (hg1 : GoodPath (S := S) mu1 path)
    (hg2 : GoodPath (S := S) mu2 path) :
    muCondPath (S := S) mu1 path hg1 =
    muCondPath (S := S) mu2 path hg2 := by
  subst h; exact muCondPath_irrel (S := S) mu1 path hg1 hg2

def RelevantTo (p : S.Player) (c : DecConstraint S) : Prop := c.p = p

noncomputable def FilterPlayer (p : S.Player) (path : DecPath S) : DecPath S :=
  path.filter (fun c => decide (c.p = p))

lemma mem_FilterPlayer_iff (p : S.Player) (c : DecConstraint S) (path : DecPath S) :
    c ∈ FilterPlayer (S := S) p path ↔ c ∈ path ∧ c.p = p := by
  classical
  simp [FilterPlayer, List.mem_filter]

def decPathToHistory : DecPath S → List (HistoryStep S)
  | [] => []
  | c :: cs => HistoryStep.action c.p c.I c.a :: decPathToHistory cs

def playerViewOfConstraint (q : S.Player) (c : DecConstraint S) (h : c.p = q) :
    Σ I : S.Infoset q, S.Act I := by
  subst h
  exact ⟨c.I, c.a⟩

def viewToConstraint (q : S.Player) (v : Σ I : S.Infoset q, S.Act I) : DecConstraint S :=
  { p := q, I := v.1, a := v.2 }

lemma viewToConstraint_playerView
    (q : S.Player) (c : DecConstraint S) (h : c.p = q) :
    viewToConstraint (S := S) q (playerViewOfConstraint (S := S) q c h) = c := by
  cases c with
  | mk p I a =>
      dsimp [playerViewOfConstraint, viewToConstraint] at *
      cases h
      rfl

def decPathPlayerView (q : S.Player) : DecPath S → List (Σ I : S.Infoset q, S.Act I)
  | [] => []
  | c :: cs =>
      if h : c.p = q then
        playerViewOfConstraint (S := S) q c h :: decPathPlayerView q cs
      else
        decPathPlayerView q cs

lemma decPathPlayerView_eq_playerHistory (q : S.Player) (path : DecPath S) :
    decPathPlayerView (S := S) q path =
      playerHistory S q (decPathToHistory (S := S) path) := by
  induction path with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [decPathToHistory, decPathPlayerView, playerHistory, ih]
      by_cases h : c.p = q
      · simp [h, playerViewOfConstraint]
      · simp [h]

lemma map_viewToConstraint_decPathPlayerView
    (q : S.Player) (path : DecPath S) :
    List.map (viewToConstraint (S := S) q) (decPathPlayerView (S := S) q path)
      =
    FilterPlayer (S := S) q path := by
  induction path with
  | nil =>
      rfl
  | cons c cs ih =>
      by_cases h : c.p = q
      · simp [decPathPlayerView, FilterPlayer, h, ih]
        simp [viewToConstraint_playerView (S := S) q c h]
      · simp [decPathPlayerView, FilterPlayer, h, ih]

inductive SubtreeAt : GameTree S Outcome -> DecPath S -> GameTree S Outcome -> Prop where
  | refl (t : GameTree S Outcome) : SubtreeAt t [] t
  | chance {k : Nat} {muC : PMF (Fin k)} {hk : 0 < k} {next : Fin k -> GameTree S Outcome}
      {path : DecPath S} {u : GameTree S Outcome} {b : Fin k} :
      SubtreeAt (next b) path u -> SubtreeAt (.chance k muC hk next) path u
  | decision {pOwner : S.Player} {I0 : S.Infoset pOwner}
      {next : S.Act I0 -> GameTree S Outcome}
      {path : DecPath S} {u : GameTree S Outcome} {a : S.Act I0} :
      SubtreeAt (next a) path u ->
      SubtreeAt (.decision I0 next)
        ({ p := pOwner, I := I0, a := a } :: path) u

/-- Transitivity of SubtreeAt. -/
theorem SubtreeAt.trans {t₁ t₂ t₃ : GameTree S Outcome}
    {p₁ p₂ : DecPath S}
    (h₁ : SubtreeAt (S := S) (Outcome := Outcome) t₁ p₁ t₂)
    (h₂ : SubtreeAt (S := S) (Outcome := Outcome) t₂ p₂ t₃) :
    SubtreeAt (S := S) (Outcome := Outcome) t₁ (p₁ ++ p₂) t₃ := by
  induction h₁ with
  | refl => simpa
  | chance _ ih => exact .chance (ih h₂)
  | decision _ ih => exact .decision (ih h₂)

/-- Go from a decision node to one of its children via transitivity.
    The child's path extends the parent's by appending the decision. -/
theorem SubtreeAt.decision_child
    {t : GameTree S Outcome}
    {pi : DecPath S}
    {pOwner : S.Player} {I0 : S.Infoset pOwner}
    {next : S.Act I0 → GameTree S Outcome}
    (hsub : SubtreeAt (S := S) (Outcome := Outcome) t pi
      (.decision I0 next))
    (a : S.Act I0) :
    SubtreeAt (S := S) (Outcome := Outcome) t
      (pi ++ [{ p := pOwner, I := I0, a := a }]) (next a) :=
  hsub.trans (.decision (.refl _))

/-- Bridge from SubtreeAt to ReachBy, preserving player history. -/
theorem SubtreeAt_to_ReachBy_with_playerHistory
    {tRoot u : GameTree S Outcome} {pi : DecPath S}
    (hsub : SubtreeAt (S := S) (Outcome := Outcome) tRoot pi u) :
    ∃ h, ReachBy (S := S) (Outcome := Outcome) h tRoot u ∧
      ∀ q, playerHistory S q h = decPathPlayerView (S := S) q pi := by
  induction hsub with
  | refl t => exact ⟨[], ReachBy.here t, fun _ => rfl⟩
  | @chance k muC hk next path u b _ ih =>
    rcases ih with ⟨h, hreach, hview⟩
    exact ⟨HistoryStep.chance k b :: h, ReachBy.chance b hreach, fun q => by
      simp [playerHistory, hview q]⟩
  | @decision pOwner I0 next path u a _ ih =>
    rcases ih with ⟨h, hreach, hview⟩
    refine ⟨HistoryStep.action pOwner I0 a :: h, ReachBy.action a hreach, fun q => ?_⟩
    simp only [playerHistory, decPathPlayerView]
    by_cases hp : pOwner = q
    · subst hp
      simp [playerViewOfConstraint, hview _]
    · simp [hp, hview q]

def PathReachesInfoset
    (tRoot : GameTree S Outcome)
    (pi : DecPath S)
    {q : S.Player}
    (J : S.Infoset q) : Prop :=
  ∃ next, SubtreeAt (S := S) (Outcome := Outcome) tRoot pi (.decision J next)

open Classical in
noncomputable def qHistoryList (tRoot : GameTree S Outcome) (q : S.Player)
    (J : S.Infoset q) : DecPath S :=
  if h : ∃ pi, PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi J then
    FilterPlayer (S := S) q (Classical.choose h)
  else
    []

noncomputable def qHistory (tRoot : GameTree S Outcome) (q : S.Player)
    (J : S.Infoset q) : Finset (DecConstraint S) :=
  (qHistoryList (S := S) (Outcome := Outcome) tRoot q J).toFinset

/-- Extend a good path by one more constraint, using a nonzero-mass proof at the end. -/
noncomputable def GoodPath.snoc
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hpath : GoodPath (S := S) mu path)
    (c : DecConstraint S)
    (hc : muMarginal (S := S) c.I (muCondPath (S := S) (mu := mu) (path := path) hpath) c.a ≠ 0) :
    GoodPath (S := S) mu (path ++ [c]) := by
  induction path generalizing mu with
  | nil =>
      -- path = []
      exact ⟨hc, ⟨⟩⟩
  | cons c0 cs ih =>
      rcases hpath with ⟨h0, hcs⟩
      refine ⟨h0, ?_⟩
      -- now we are under the conditioned measure
      exact ih
        (mu := muCond (S := S) c0.I c0.a mu h0)
        (hpath := hcs)
        (hc := hc)

theorem muCondPath_step_eq_append
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hpath : GoodPath (S := S) mu path)
    (c : DecConstraint S)
    (hc : muMarginal (S := S) c.I (muCondPath (S := S) (mu := mu) (path := path) hpath) c.a ≠ 0) :
    muCond (S := S) c.I c.a (muCondPath (S := S) (mu := mu) (path := path) hpath) hc =
      muCondPath (S := S) (mu := mu) (path := path ++ [c])
        (GoodPath.snoc (S := S) mu path hpath c hc) := by
  -- unfold muCondPath on (path ++ [c]); it peels off the final `c` exactly once
  induction path generalizing mu with
  | nil =>
      -- path = []
      rfl
  | cons c0 cs ih =>
      -- reduce both sides under the first step `c0`
      rcases hpath with ⟨h0, hcs⟩
      -- both sides start with the same conditioning on c0, so recurse
      simp [muCondPath, GoodPath.snoc, List.cons_append, ih]

theorem PlayerIndep_muCondPath
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hind : PlayerIndep (S := S) mu)
    (hgood : GoodPath (S := S) mu path) :
    PlayerIndep (S := S) (muCondPath (S := S) mu path hgood) := by
  induction path generalizing mu with
  | nil => exact hind
  | cons c cs ih =>
    exact ih (muCond (S := S) c.I c.a mu hgood.1)
      (PlayerIndep_muCond (S := S) mu hind hgood.1)
      hgood.2

/-- Canonical witness that filtered constraints remain conditionable when we drop
    a non-q conditioning step. -/
noncomputable def goodPath_transport_other
    (mu : PMF (FlatProfile S))
    (c : DecConstraint S)
    (cs : DecPath S)
    (q : S.Player)
    (hc : muMarginal (S := S) c.I mu c.a ≠ 0)
    (hneq : c.p ≠ q)
    (hind : PlayerIndep (S := S) mu)
    (hcs :
      GoodPath (S := S)
        (muCond (S := S) c.I c.a mu hc)
        (FilterPlayer (S := S) q cs)) :
    GoodPath (S := S) mu (FilterPlayer (S := S) q cs) := by
  induction cs generalizing mu with
  | nil =>
      simpa [FilterPlayer] using (PUnit.unit : GoodPath (S := S) mu [])
  | cons d ds ih =>
      by_cases hdq : d.p = q
      · have hshape :
            GoodPath (S := S) (muCond (S := S) c.I c.a mu hc)
              (d :: FilterPlayer (S := S) q ds) := by
          simpa [FilterPlayer, hdq] using hcs
        rcases hshape with ⟨hd_cond, htail_cond⟩
        have hdp_ne_cp : d.p ≠ c.p := by
          intro hdc; exact hneq (hdc ▸ hdq)
        have hd_nonzero : muMarginal (S := S) d.I mu d.a ≠ 0 := by
          have hmarg :
              muMarginal (S := S) d.I (muCond (S := S) c.I c.a mu hc) d.a
                = muMarginal (S := S) d.I mu d.a :=
            congrArg (fun ν => ν d.a)
              (muMarginal_muCond_other (S := S) (mu := mu) hind
                hdp_ne_cp (I := c.I) (J := d.I) (a := c.a) hc)
          simpa [hmarg] using hd_cond
        have hc_after : muMarginal (S := S) c.I
            (muCond (S := S) d.I d.a mu hd_nonzero) c.a ≠ 0 := by
          have hmarg :
              muMarginal (S := S) c.I (muCond (S := S) d.I d.a mu hd_nonzero) c.a
                = muMarginal (S := S) c.I mu c.a :=
            congrArg (fun ν => ν c.a)
              (muMarginal_muCond_other (S := S) (mu := mu) hind
                (by simpa using hdp_ne_cp.symm)
                (I := d.I) (J := c.I) (a := d.a) hd_nonzero)
          simpa [hmarg] using hc
        have hind_d :
            PlayerIndep (S := S) (muCond (S := S) d.I d.a mu hd_nonzero) :=
          PlayerIndep_muCond (S := S) (mu := mu) hind hd_nonzero
        have hcomm :
            muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc) hd_cond
              =
            muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_nonzero) hc_after := by
          simpa using
            muCond_comm_of_PlayerIndep (S := S) (mu := mu) hind
              (Ne.symm hdp_ne_cp) (I := c.I) (a := c.a)
              (J := d.I) (b := d.a) hc hd_nonzero
        have htail' :
            GoodPath (S := S)
              (muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_nonzero) hc_after)
              (FilterPlayer (S := S) q ds) :=
          cast (by rw [hcomm]) htail_cond
        have htail :
            GoodPath (S := S) (muCond (S := S) d.I d.a mu hd_nonzero)
              (FilterPlayer (S := S) q ds) :=
          ih (mu := muCond (S := S) d.I d.a mu hd_nonzero)
            (hc := hc_after) (hind := hind_d) (hcs := htail')
        simpa [FilterPlayer, hdq] using (⟨hd_nonzero, htail⟩ :
          GoodPath (S := S) mu (d :: FilterPlayer (S := S) q ds))
      · have hshape :
            GoodPath (S := S) (muCond (S := S) c.I c.a mu hc)
              (FilterPlayer (S := S) q ds) := by
          simpa [FilterPlayer, hdq] using hcs
        have htail :
            GoodPath (S := S) mu (FilterPlayer (S := S) q ds) :=
          ih (mu := mu) (hc := hc) (hind := hind) (hcs := hshape)
        simpa [FilterPlayer, hdq] using htail

noncomputable def goodPathFilter
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hgood : GoodPath (S := S) mu path) (q : S.Player)
    (hind : PlayerIndep (S := S) mu) :
    GoodPath (S := S) mu (FilterPlayer (S := S) q path) := by
  induction path generalizing mu with
  | nil =>
      simpa [FilterPlayer] using (PUnit.unit : GoodPath (S := S) mu [])
  | cons c cs ih =>
      rcases hgood with ⟨hc, hcs⟩
      by_cases hq : c.p = q
      · simp only [FilterPlayer, hq, decide_true, List.filter_cons_of_pos]
        refine ⟨?_, ?_⟩
        · simpa [hq] using hc
        · exact ih (muCond (S := S) c.I c.a mu hc) hcs
            (PlayerIndep_muCond (S := S) mu hind hc)
      · simp only [FilterPlayer, hq, decide_false, Bool.false_eq_true, not_false_eq_true,
          List.filter_cons_of_neg]
        exact goodPath_transport_other (S := S) mu c cs q hc hq hind
          (ih (muCond (S := S) c.I c.a mu hc) hcs
            (PlayerIndep_muCond (S := S) mu hind hc))

/-- Conditioning on a constraint for a different player, then conditioning along a path,
    gives the same marginal at player q's infoset as just conditioning along the path.
    This follows from the product structure: non-q conditioning only modifies non-q coordinates. -/
theorem muMarginal_skip_nonq_cond
    (mu : PMF (FlatProfile S)) (hind : PlayerIndep (S := S) mu)
    (c : DecConstraint S) (q : S.Player) (hcq : c.p ≠ q)
    (J : S.Infoset q)
    (hc : muMarginal (S := S) c.I mu c.a ≠ 0)
    (path : DecPath S)
    (hall : ∀ d, d ∈ path → d.p = q)
    (hgood1 : GoodPath (S := S) (muCond (S := S) c.I c.a mu hc) path)
    (hgood2 : GoodPath (S := S) mu path) :
    muMarginal (S := S) J
      (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc) path hgood1) =
    muMarginal (S := S) J (muCondPath (S := S) mu path hgood2) := by
  induction path generalizing mu with
  | nil =>
      simp only [muCondPath]
      exact muMarginal_muCond_other (S := S) mu hind (Ne.symm hcq) hc
  | cons d ds ih =>
      have hdq : d.p = q := hall d (List.mem_cons.mpr (Or.inl rfl))
      have hdp_ne_cp : d.p ≠ c.p := by
        intro hdc; exact hcq (hdc ▸ hdq)
      rcases hgood1 with ⟨hd_cond, htail_cond⟩
      rcases hgood2 with ⟨hd_base, htail_base⟩
      have hc_after :
          muMarginal (S := S) c.I
            (muCond (S := S) d.I d.a mu hd_base) c.a ≠ 0 := by
        have hmarg :
            muMarginal (S := S) c.I (muCond (S := S) d.I d.a mu hd_base) c.a
              = muMarginal (S := S) c.I mu c.a :=
          congrArg (fun ν => ν c.a)
            (muMarginal_muCond_other (S := S) (mu := mu) hind
              (Ne.symm hdp_ne_cp) hd_base)
        simpa [hmarg] using hc
      have hcomm :
          muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc) hd_cond
            =
          muCond (S := S) c.I c.a
            (muCond (S := S) d.I d.a mu hd_base) hc_after := by
        simpa using
          muCond_comm_of_PlayerIndep (S := S) (mu := mu) hind
            (Ne.symm hdp_ne_cp) (I := c.I) (a := c.a)
            (J := d.I) (b := d.a) hc hd_base
      have htail_cond' :
          GoodPath (S := S)
            (muCond (S := S) c.I c.a
              (muCond (S := S) d.I d.a mu hd_base) hc_after)
            ds :=
        cast (by rw [hcomm]) htail_cond
      have hind_d :
          PlayerIndep (S := S) (muCond (S := S) d.I d.a mu hd_base) :=
        PlayerIndep_muCond (S := S) mu hind hd_base
      have hall_tail : ∀ d', d' ∈ ds → d'.p = q :=
        fun d' hd'mem => hall d' (List.mem_cons.mpr (Or.inr hd'mem))
      calc
        muMarginal (S := S) J
            (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc)
              (d :: ds) ⟨hd_cond, htail_cond⟩)
          = muMarginal (S := S) J
            (muCondPath (S := S)
              (muCond (S := S) c.I c.a
                (muCond (S := S) d.I d.a mu hd_base) hc_after)
              ds htail_cond') := by
                simp only [muCondPath]
                congr 1
                exact muCondPath_eq_of_eq (S := S)
                  hcomm htail_cond htail_cond'
        _ = muMarginal (S := S) J
            (muCondPath (S := S) (muCond (S := S) d.I d.a mu hd_base) ds htail_base) :=
          ih (muCond (S := S) d.I d.a mu hd_base)
            hind_d hc_after hall_tail htail_cond' htail_base
        _ = muMarginal (S := S) J
            (muCondPath (S := S) mu (d :: ds) ⟨hd_base, htail_base⟩) := by
              simp [muCondPath]

theorem muMarginal_condPath_invariant_filter
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hind : PlayerIndep (S := S) mu)
    (hgood : GoodPath (S := S) mu path)
    (q : S.Player) (J : S.Infoset q)
    (hgoodF : GoodPath (S := S) mu (FilterPlayer (S := S) q path)) :
    muMarginal (S := S) J (muCondPath (S := S) mu path hgood) =
    muMarginal (S := S) J
      (muCondPath (S := S) mu (FilterPlayer (S := S) q path) hgoodF) := by
  induction path generalizing mu with
  | nil => rfl
  | cons c cs ih =>
    -- muCondPath (c :: cs) = muCondPath cs ∘ muCond c
    -- FilterPlayer q (c :: cs) = if c.p = q then c :: FilterPlayer q cs
    --                                       else FilterPlayer q cs
    by_cases hcq : c.p = q
    · -- c.p = q: FilterPlayer keeps c, both sides peel off c
      subst hcq
      -- FilterPlayer c.p (c :: cs) = c :: FilterPlayer c.p cs propositionally
      have hfilt : FilterPlayer (S := S) c.p (c :: cs) =
          c :: FilterPlayer (S := S) c.p cs := by
        simp [FilterPlayer]
      -- Transport hgoodF to the simplified type
      revert hgoodF; rw [hfilt]; intro hgoodF
      -- Now hgoodF : GoodPath mu (c :: FilterPlayer c.p cs)
      exact ih (muCond (S := S) c.I c.a mu hgood.1)
        (PlayerIndep_muCond (S := S) mu hind hgood.1)
        hgood.2 hgoodF.2
    · -- c.p ≠ q: FilterPlayer drops c, so FilterPlayer q (c::cs) = FilterPlayer q cs
      have hfilt : FilterPlayer (S := S) q (c :: cs) =
          FilterPlayer (S := S) q cs := by
        simp [FilterPlayer, hcq]
      -- Transport hgoodF
      revert hgoodF; rw [hfilt]; intro hgoodF
      -- LHS: muMarginal J (muCondPath (muCond c mu) cs)
      -- By IH on cs with mu' = muCond c mu:
      --   = muMarginal J (muCondPath (muCond c mu) (FilterPlayer q cs))
      -- Then by skip lemma: = muMarginal J (muCondPath mu (FilterPlayer q cs))
      let mu' := muCond (S := S) c.I c.a mu hgood.1
      -- We need a GoodPath for FilterPlayer q cs under mu'
      have hind' := PlayerIndep_muCond (S := S) mu hind hgood.1
      -- Use muMarginal_condPath_invariant_filter (IH) to reduce to filtered path under mu'
      have hgoodF' : GoodPath (S := S) mu' (FilterPlayer (S := S) q cs) :=
        goodPathFilter (S := S) mu' cs hgood.2 q hind'
      have hallF : ∀ d, d ∈ FilterPlayer (S := S) q cs → d.p = q :=
        fun d hd => ((mem_FilterPlayer_iff (S := S) q d cs).mp hd).2
      calc muMarginal (S := S) J (muCondPath (S := S) mu (c :: cs) hgood)
          = muMarginal (S := S) J (muCondPath (S := S) mu' cs hgood.2) := rfl
        _ = muMarginal (S := S) J
              (muCondPath (S := S) mu' (FilterPlayer (S := S) q cs) hgoodF') :=
            ih mu' hind' hgood.2 hgoodF'
        _ = muMarginal (S := S) J
              (muCondPath (S := S) mu (FilterPlayer (S := S) q cs) hgoodF) :=
            muMarginal_skip_nonq_cond (S := S) mu hind c q hcq J hgood.1
              (FilterPlayer (S := S) q cs) hallF hgoodF' hgoodF

theorem FilterPlayer_path_eq_history
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    {q : S.Player}
    {J : S.Infoset q}
    {pi : DecPath S}
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi J) :
    FilterPlayer (S := S) q pi = qHistoryList (S := S) (Outcome := Outcome) tRoot q J := by
  classical
  unfold qHistoryList
  have hEx : ∃ pi', PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi' J :=
    ⟨pi, hreach⟩
  simp only [hEx, ↓reduceDIte]
  -- Let pi0 be the canonical chosen path
  let pi0 : DecPath S := Classical.choose hEx
  have hpi0 : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi0 J :=
    Classical.choose_spec hEx
  -- Extract SubtreeAt witnesses
  rcases hreach with ⟨next, hsub⟩
  rcases hpi0 with ⟨next0, hsub0⟩
  -- Convert to ReachBy with playerHistory
  rcases SubtreeAt_to_ReachBy_with_playerHistory (S := S) (Outcome := Outcome) hsub with
    ⟨h, hreach_h, hview⟩
  rcases SubtreeAt_to_ReachBy_with_playerHistory (S := S) (Outcome := Outcome) hsub0 with
    ⟨h0, hreach_h0, hview0⟩
  -- Apply PerfectRecall
  have hPR : playerHistory S q h = playerHistory S q h0 :=
    hpr h h0 J next next0 hreach_h hreach_h0
  -- Convert playerHistory to decPathPlayerView
  have hpv : decPathPlayerView (S := S) q pi = decPathPlayerView (S := S) q pi0 := by
    rw [← hview q, ← hview0 q, hPR]
  -- Convert decPathPlayerView to FilterPlayer via map_viewToConstraint_decPathPlayerView
  have := map_viewToConstraint_decPathPlayerView (S := S) q pi
  have := map_viewToConstraint_decPathPlayerView (S := S) q pi0
  -- FilterPlayer = map viewToConstraint (decPathPlayerView q ·)
  calc FilterPlayer (S := S) q pi
      = List.map (viewToConstraint (S := S) q) (decPathPlayerView (S := S) q pi) := by
        rw [map_viewToConstraint_decPathPlayerView]
    _ = List.map (viewToConstraint (S := S) q) (decPathPlayerView (S := S) q pi0) := by
        rw [hpv]
    _ = FilterPlayer (S := S) q pi0 := by
        rw [map_viewToConstraint_decPathPlayerView]

---
-- Behavioral Strategy Construction and Inductive Evaluation
--
-- `mixedToBehavioralRoot` defines the behavioral strategy: at each infoset,
-- condition the flat product measure on the canonical history, then take the
-- marginal. The main induction (`eval_subtree_correct`) shows that evaluating
-- any subtree under this behavioral strategy equals the conditional expectation
-- under the product measure.
---

/-- The behavioral strategy induced by a flat product measure. At infoset `I`,
condition on the canonical history of decisions leading to `I`, then take the
marginal at `I`. Falls back to the unconditional marginal when the history has
zero mass (unreachable infoset). -/
noncomputable def mixedToBehavioralRoot
    (mu : PMF (FlatProfile S)) (tRoot : GameTree S Outcome) :
    BehavioralProfile S :=
  fun q J => by
    classical
    let hlist := qHistoryList (S := S) (Outcome := Outcome) tRoot q J
    by_cases hgood : Nonempty (GoodPath (S := S) mu hlist)
    · exact muMarginal (S := S) J
        (muCondPath (S := S) mu hlist (Classical.choice hgood))
    · exact muMarginal (S := S) J mu

/-- Disintegration / law of total probability for muCond:
    Splitting a bind by the value at an infoset. -/
theorem muCond_disintegration
    {p : S.Player} (I : S.Infoset p)
    (mu : PMF (FlatProfile S))
    (f : FlatProfile S → PMF Outcome) (x : Outcome) :
    (mu.bind f) x =
    ∑ a : S.Act I,
      ∑ s : FlatProfile S,
        (if s ⟨p, I⟩ = a then mu s else 0) * (f s x) := by
  simp only [PMF.bind_apply, tsum_fintype]
  rw [show ∑ s, mu s * f s x =
    ∑ s, ∑ a : S.Act I, if s ⟨p, I⟩ = a then mu s * f s x else 0 from by
    congr 1; funext s
    exact Eq.symm (Fintype.sum_ite_eq (s ⟨p, I⟩) fun j ↦ mu s * (f s) x)]
  rw [Finset.sum_comm]
  congr 1; funext a; congr 1; funext s
  split_ifs <;> ring

theorem mixedToBehavioral_context_eq
    (mu : PMF (FlatProfile S)) (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot) (hind : PlayerIndep (S := S) mu)
    (pi : DecPath S) (hgood : GoodPath (S := S) mu pi)
    {pOwner : S.Player} {I0 : S.Infoset pOwner}
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome)
      tRoot pi I0) :
    mixedToBehavioralRoot (S := S) (Outcome := Outcome)
      mu tRoot pOwner I0 =
      muMarginal (S := S) I0
        (muCondPath (S := S) mu pi hgood) := by
  classical
  have h_hist :
      FilterPlayer (S := S) pOwner pi =
      qHistoryList (S := S) (Outcome := Outcome)
        tRoot pOwner I0 := by
    simpa using
      (FilterPlayer_path_eq_history (S := S) (Outcome := Outcome)
        (tRoot := tRoot) hpr (q := pOwner)
        (J := I0) (pi := pi) hreach)
  -- Derive GoodPath for the history list
  have hgoodF : GoodPath (S := S) mu (FilterPlayer (S := S) pOwner pi) :=
    goodPathFilter (S := S) mu pi hgood pOwner hind
  have hgoodHist : GoodPath (S := S) mu
      (qHistoryList (S := S) (Outcome := Outcome) tRoot pOwner I0) :=
    h_hist ▸ hgoodF
  -- Show mixedToBehavioralRoot takes the good branch
  have hne : Nonempty (GoodPath (S := S) mu
      (qHistoryList (S := S) (Outcome := Outcome) tRoot pOwner I0)) :=
    ⟨hgoodHist⟩
  -- Unfold and simplify
  unfold mixedToBehavioralRoot
  simp only [hne, ↓reduceDIte]
  -- The chosen GoodPath may differ from ours, but muCondPath is proof-irrelevant
  have hrw :
      muCondPath (S := S) mu
        (qHistoryList (S := S) (Outcome := Outcome) tRoot pOwner I0)
        (Classical.choice hne) =
      muCondPath (S := S) mu
        (FilterPlayer (S := S) pOwner pi) hgoodF := by
    revert hgoodF; rw [h_hist]; intro hgoodF
    exact muCondPath_irrel (S := S) mu _ _ _
  rw [hrw]
  exact (muMarginal_condPath_invariant_filter (S := S)
    mu pi hind hgood pOwner I0 hgoodF).symm

/-- If muMarginal I mu a = 0 then mu s = 0 for any s with s⟨p,I⟩=a. -/
theorem muMarginal_zero_of_coord
    {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S))
    (ha : muMarginal (S := S) I mu a = 0)
    (s : FlatProfile S) (hs : s ⟨p, I⟩ = a) :
    mu s = 0 := by
  simp only [muMarginal, PMF.bind_apply,
    tsum_fintype] at ha
  have h0 := Finset.sum_eq_zero_iff.mp ha s
    (Finset.mem_univ s)
  simp only [hs, PMF.pure_apply, ↓reduceIte, mul_one] at h0
  exact h0

/-- Mass times conditional = indicator times original. -/
theorem muMarginal_mul_muCond_apply
    {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S))
    (ha : muMarginal (S := S) I mu a ≠ 0)
    (s : FlatProfile S) :
    muMarginal (S := S) I mu a *
      muCond (S := S) I a mu ha s =
    if s ⟨p, I⟩ = a then mu s else 0 := by
  have hne_top : (muMarginal (S := S) I mu) a ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top
      (PMF.tsum_coe (muMarginal (S := S) I mu) ▸
        ENNReal.one_ne_top) a
  simp only [muCond, PMF.ofFintype_apply]
  split_ifs with hs
  · rw [mul_comm,
      ENNReal.div_mul_cancel ha hne_top]
  · simp

/-- The inductive step for decision nodes. -/
theorem eval_subtree_decision_step
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {pOwner : S.Player} {I0 : S.Infoset pOwner}
    {next : S.Act I0 → GameTree S Outcome}
    {pi : DecPath S} (hgood : GoodPath (S := S) mu pi)
    (h_sub : SubtreeAt (S := S) (Outcome := Outcome)
      tRoot pi (.decision I0 next))
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome)
      tRoot pi I0)
    (ih : ∀ (a : S.Act I0)
        (hga : GoodPath (S := S) mu
          (pi ++ [{ p := pOwner, I := I0, a := a }])),
        SubtreeAt (S := S) (Outcome := Outcome)
          tRoot
          (pi ++ [{ p := pOwner, I := I0, a := a }])
          (next a) →
        (next a).evalDist
          (mixedToBehavioralRoot (S := S)
            (Outcome := Outcome) mu tRoot) =
        (muCondPath (S := S) mu
          (pi ++ [{ p := pOwner, I := I0, a := a }])
          hga).bind
          (fun s => (next a).evalFlat (S := S)
            (Outcome := Outcome) s)) :
    (GameTree.decision (S := S) (Outcome := Outcome)
      I0 next).evalDist
        (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
          mu tRoot)
      =
    (muCondPath (S := S) mu pi hgood).bind
      (fun s =>
        (GameTree.decision (S := S) (Outcome := Outcome)
          I0 next).evalFlat (S := S)
            (Outcome := Outcome) s) := by
  simp only [evalDist_decision]
  have hctx :
      mixedToBehavioralRoot (S := S) (Outcome := Outcome)
        mu tRoot pOwner I0 =
      muMarginal (S := S) I0
        (muCondPath (S := S) mu pi hgood) :=
    mixedToBehavioral_context_eq (S := S) (Outcome := Outcome)
      mu tRoot hpr hind pi hgood hreach
  rw [hctx]
  conv_rhs =>
    rw [show
      (fun s =>
        (GameTree.decision (S := S) (Outcome := Outcome)
          I0 next).evalFlat (S := S)
            (Outcome := Outcome) s) =
      (fun s =>
        (next (s ⟨pOwner, I0⟩)).evalFlat (S := S)
          (Outcome := Outcome) s) from by
        funext s; simp [GameTree.evalFlat,
          evalDist_decision, flatToBehavioral,
          PMF.pure_bind]]
  -- Goal: (muMarginal I0 μ_pi).bind (fun a => evalDist σ (next a))
  --     = μ_pi.bind (fun s => (next (s⟨p,I0⟩)).evalFlat s)
  -- Prove pointwise
  set μ_pi := muCondPath (S := S) mu pi hgood with hμ_def
  ext x
  simp only [PMF.bind_apply, tsum_fintype]
  -- Split RHS sum by action at I0
  rw [show (∑ s : FlatProfile S, μ_pi s *
      ((next (s ⟨pOwner, I0⟩)).evalFlat (S := S)
        (Outcome := Outcome) s) x) =
    ∑ a : S.Act I0, ∑ s : FlatProfile S,
      if s ⟨pOwner, I0⟩ = a
      then μ_pi s *
        ((next a).evalFlat (S := S)
          (Outcome := Outcome) s) x
      else 0 from by
    rw [Finset.sum_comm]; congr 1; funext s; symm
    rw [Finset.sum_ite_eq]; simp [Finset.mem_univ]]
  -- Now both sides: ∑ a, f(a)
  congr 1; funext a
  -- Per-action identity
  by_cases ha :
      muMarginal (S := S) I0 μ_pi a = 0
  · -- Zero mass: both sides = 0
    simp only [ha, zero_mul]
    symm; apply Finset.sum_eq_zero
    intro s _
    split_ifs with hs
    · have : μ_pi s = 0 :=
        muMarginal_zero_of_coord (S := S) I0 a
          μ_pi ha s hs
      simp [this]
    · rfl
  · -- Nonzero mass: use IH
    have hga : GoodPath (S := S) mu
        (pi ++ [{ p := pOwner, I := I0, a := a }]) :=
      GoodPath.snoc (S := S) mu pi hgood
        { p := pOwner, I := I0, a := a } ha
    have hsub_a : SubtreeAt (S := S) (Outcome := Outcome)
        tRoot
        (pi ++ [{ p := pOwner, I := I0, a := a }])
        (next a) := h_sub.decision_child a
    have hih := ih a hga hsub_a
    -- Replace evalDist with bind of evalFlat via IH
    rw [show (GameTree.evalDist
        (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
          mu tRoot) (next a)) x =
      ((muCondPath (S := S) mu
        (pi ++ [{ p := pOwner, I := I0, a := a }])
        hga).bind
        (fun s => (next a).evalFlat (S := S)
          (Outcome := Outcome) s)) x from by
      rw [← hih]]
    -- Rewrite muCondPath(pi++[c]) to muCond I0 a μ_pi
    rw [show muCondPath (S := S) mu
        (pi ++ [{ p := pOwner, I := I0, a := a }])
        hga =
      muCond (S := S) I0 a μ_pi ha from
      (muCondPath_irrel (S := S) mu _ hga
        (GoodPath.snoc (S := S) mu pi hgood
          { p := pOwner, I := I0, a := a } ha)).trans
      (muCondPath_step_eq_append (S := S) mu pi
        hgood
        { p := pOwner, I := I0, a := a } ha).symm]
    simp only [PMF.bind_apply, tsum_fintype]
    -- LHS: marginal(a) * ∑ s, muCond(s) * evalFlat(s)
    -- RHS: ∑ s, [s⟨p,I0⟩=a] * μ_pi(s) * evalFlat(s)
    rw [Finset.mul_sum]
    congr 1; funext s
    rw [← mul_assoc,
      muMarginal_mul_muCond_apply (S := S)
        I0 a μ_pi ha s]
    split_ifs <;> simp

theorem eval_subtree_correct
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu) :
    ∀ (u : GameTree S Outcome) (pi : DecPath S)
      (hgood : GoodPath (S := S) mu pi),
      SubtreeAt (S := S) (Outcome := Outcome) tRoot pi u ->
      u.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
        mu tRoot) =
      (muCondPath (S := S) mu pi hgood).bind
        (fun s => u.evalFlat s) := by
  intro u
  induction u with
  | terminal z =>
    -- terminal: both sides = PMF.pure z
    intro pi hgood _
    simp only [evalDist_terminal]
    -- RHS: mu_pi.bind (fun _ => PMF.pure z) = PMF.pure z
    symm
    ext x
    simp only [GameTree.evalFlat, evalDist_terminal,
      PMF.bind_apply, PMF.pure_apply, tsum_fintype]
    have hsum : ∑ s : FlatProfile S,
        (muCondPath (S := S) mu pi hgood) s = 1 := by
      have := PMF.tsum_coe (muCondPath (S := S) mu pi hgood)
      rwa [tsum_fintype] at this
    split_ifs <;> simp [hsum]
  | chance k muC hk next ih_chance =>
    -- chance: swap bind order using Fubini, then apply IH per branch
    intro pi hgood hsub
    simp only [evalDist_chance]
    -- Unfold evalFlat on RHS to expose the inner structure
    change _ = (muCondPath (S := S) mu pi hgood).bind
      (fun s => muC.bind (fun b =>
        (next b).evalDist (flatToBehavioral (S := S) s)))
    -- Swap the bind order (Fubini)
    rw [PMF.bind_comm]
    -- Now both sides: muC.bind (fun b => ...)
    congr 1; funext b
    -- Get SubtreeAt tRoot pi (next b) via transitivity
    have hsub_b : SubtreeAt (S := S) (Outcome := Outcome)
        tRoot pi (next b) := by
      have := hsub.trans (SubtreeAt.chance (b := b)
        (SubtreeAt.refl (next b)))
      simpa using this
    exact ih_chance b pi hgood hsub_b
  | decision I0 next ih_dec =>
    -- decision: the core case, delegated to eval_subtree_decision_step
    intro pi hgood hsub
    have hreach : PathReachesInfoset (S := S) (Outcome := Outcome)
        tRoot pi I0 :=
      ⟨next, hsub⟩
    exact eval_subtree_decision_step (S := S) (Outcome := Outcome)
      tRoot hpr mu hind hgood hsub hreach
      (fun a hga hsub_a => ih_dec a _ hga hsub_a)

theorem rhs_eq_flat_bind (t : GameTree S Outcome) (muP : MixedProfile S) :
    (mixedProfileJoint (S := S) muP).bind
      (fun pi => t.evalDist (pureToBehavioral (S := S) pi)) =
    (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)).bind
      (fun s => t.evalDist (flatToBehavioral s)) := by
  ext x
  simp only [PMF.bind_apply, tsum_fintype, pmfPureToFlat, PMF.bind_bind, PMF.pure_bind]
  refine Finset.sum_congr rfl ?_
  intro pi _
  have hflat :
      (flatProfileEquivPureProfile (S := S)).symm pi =
      (fun idx : FlatIdx S => pi idx.1 idx.2) := rfl
  have hprof :
      pureToBehavioral (S := S) pi =
      flatToBehavioral (S := S) (fun idx => pi idx.1 idx.2) := by
    funext p I
    rfl
  simp [hflat, hprof]

---
-- Main Theorem
---

/-- The behavioral strategy induced by a player-independent flat measure reproduces
the expected outcome: evaluating the whole tree under the behavioral strategy
equals the expectation under the flat product measure. -/
theorem mixed_to_behavioral_nplayer
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu) :
    t.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
      mu t) =
    mu.bind (fun s => t.evalFlat s) := by
  simpa using eval_subtree_correct (S := S) (Outcome := Outcome)
    t hpr mu hind t [] ⟨⟩ (SubtreeAt.refl t)

/-- **Kuhn's theorem.** For any game tree with perfect recall and any mixed strategy
profile, there exists a behavioral strategy profile that induces the same outcome
distribution. -/
theorem kuhn_mixed_to_behavioral
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ sigma : BehavioralProfile S,
      t.evalDist sigma =
      (mixedProfileJoint (S := S) muP).bind
        (fun pi => t.evalDist
          (pureToBehavioral (S := S) pi)) := by
  let mu0 : PMF (FlatProfile S) :=
    pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)
  refine ⟨mixedToBehavioralRoot (S := S) (Outcome := Outcome)
    mu0 t, ?_⟩
  calc
    t.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
      mu0 t)
      = mu0.bind (fun s => t.evalFlat s) := by
          exact mixed_to_behavioral_nplayer (S := S)
            (Outcome := Outcome) t hpr mu0
            (PlayerIndep_pmfPureToFlat (S := S) muP)
    _ = (mixedProfileJoint (S := S) muP).bind
          (fun pi => t.evalDist
            (pureToBehavioral (S := S) pi)) := by
        exact (rhs_eq_flat_bind (S := S)
          (Outcome := Outcome) t muP).symm

open GameTheory in
/-- Kuhn's theorem lifted to utility distributions (mixed → behavioral):
    For any EFG game with perfect recall, every mixed strategy profile has an
    equivalent behavioral profile that induces the same joint utility distribution. -/
theorem kuhn_mixed_to_behavioral_udist (G : EFGGame)
    (hpr : PerfectRecall G.tree) (muP : MixedProfile G.inf) :
    ∃ σ : BehavioralProfile G.inf,
      G.toKernelGame.udist σ =
      (mixedProfileJoint (S := G.inf) muP).bind
        (fun pi => G.toKernelGame.udist (pureToBehavioral pi)) := by
  obtain ⟨σ, hσ⟩ := kuhn_mixed_to_behavioral G.tree hpr muP
  exact ⟨σ, by
    simp only [KernelGame.udist, EFGGame.toKernelGame]
    rw [hσ, PMF.bind_bind]⟩

end EFG
