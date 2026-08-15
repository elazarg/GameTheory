/-
# Existence of a mixed equilibrium

Every finite game has an equilibrium in mixed strategies. Unlike the potential
argument, which finds one by maximizing a single function, this needs a genuine
fixed point: nothing is being maximized globally, and the object that has to
exist is a profile at which every player is simultaneously already best
replying.

The argument is the classical one. Mixed profiles form a compact convex
polytope; each player's best replies to a profile form a nonempty convex set,
nonempty because a continuous function attains its maximum on a compact set and
convex because the payoff is affine in the deviator's own weights; the whole
best-reply correspondence has a closed graph; and a fixed point of it is exactly
a profile no player wants to move away from.

This is the module the fixed-point dependency exists for, and it is the only
place a set-valued fixed-point theorem is used.
-/

import GameTheory.Analysis.Payoff
import GameTheory.Core.Response
import FixedPointTheorems.kakutani

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι] {F : GameForm ι}
variable [∀ i, Fintype (F.sig.Strategy i)]
variable (utility : F.sig.Outcome → ι → ℝ)

/-! ## Continuity of replacing one player's weights

Both the best-reply set and its graph are cut out by inequalities between
payoffs at updated profiles, so every closedness argument below rests on this
one map being continuous — jointly, because the graph varies the profile and the
reply together. -/

omit [Fintype ι] [∀ i, Fintype (F.sig.Strategy i)] in
/-- Replacing one player's weight vector is jointly continuous. -/
theorem continuous_profileUpdate (who : ι) :
    Continuous fun p : Profile F.sig.weights × (F.sig.Strategy who → ℝ) =>
      Profile.update p.1 who p.2 := by
  refine continuous_pi fun j => ?_
  by_cases h : j = who
  · subst h
    simpa only [Profile.update_same] using continuous_snd
  · simp only [Profile.update_of_ne _ _ h]
    exact (continuous_apply j).comp continuous_fst

omit [Fintype ι] [∀ i, Fintype (F.sig.Strategy i)] in
theorem continuous_update_reply (who : ι) (x : Profile F.sig.weights) :
    Continuous fun v : F.sig.Strategy who → ℝ => Profile.update x who v :=
  (continuous_profileUpdate who).comp (continuous_const.prodMk continuous_id)

omit [Fintype ι] [∀ i, Fintype (F.sig.Strategy i)] in
theorem continuous_update_profile (who : ι) (v : F.sig.Strategy who → ℝ) :
    Continuous fun x : Profile F.sig.weights => Profile.update x who v :=
  (continuous_profileUpdate who).comp (continuous_id.prodMk continuous_const)

/-! ## Best replies -/

variable (F) in
/-- The weight vectors player `who` cannot improve on against `x`. Membership is
stated against every point of the simplex rather than against every law, so that
the set lives in the vector space the fixed-point theorem works in. -/
def bestReply (who : ι) (x : Profile F.sig.weights) : Set (F.sig.Strategy who → ℝ) :=
  {v | v ∈ stdSimplex ℝ (F.sig.Strategy who) ∧
    ∀ w ∈ stdSimplex ℝ (F.sig.Strategy who),
      payoff F utility who (Profile.update x who w) ≤
        payoff F utility who (Profile.update x who v)}

theorem bestReply_subset (who : ι) (x : Profile F.sig.weights) :
    bestReply F utility who x ⊆ stdSimplex ℝ (F.sig.Strategy who) := fun _ hv => hv.1

/-- **A best reply set is convex**, because the payoff is affine in the
deviator's own weights: a mixture of two best replies is worth their mixed
value, which is still at least anything else. -/
theorem convex_bestReply (who : ι) (x : Profile F.sig.weights) :
    Convex ℝ (bestReply F utility who x) := by
  rintro v ⟨hv, hvmax⟩ w ⟨hw, hwmax⟩ a b ha hb hab
  refine ⟨convex_stdSimplex ℝ _ hv hw ha hb hab, fun u hu => ?_⟩
  rw [payoff_update_mix]
  calc payoff F utility who (Profile.update x who u)
      = a * payoff F utility who (Profile.update x who u) +
          b * payoff F utility who (Profile.update x who u) := by
        rw [← add_mul, hab, one_mul]
    _ ≤ a * payoff F utility who (Profile.update x who v) +
          b * payoff F utility who (Profile.update x who w) :=
        add_le_add (by gcongr; exact hvmax u hu) (by gcongr; exact hwmax u hu)

/-- **A best reply exists**, because a continuous payoff attains its maximum on
the compact simplex. -/
theorem bestReply_nonempty [∀ i, Nonempty (F.sig.Strategy i)] (who : ι)
    (x : Profile F.sig.weights) : (bestReply F utility who x).Nonempty := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_stdSimplex ℝ (F.sig.Strategy who)).exists_isMaxOn
    FinDist.stdSimplex_nonempty
    ((continuous_payoff who).comp (continuous_update_reply who x)).continuousOn
  exact ⟨v, hv, fun w hw => hmax hw⟩

omit [Fintype ι] [∀ i, Fintype (F.sig.Strategy i)] in
/-- Taking probability vectors commutes with replacing one player's law. -/
theorem probs_update (mu : Profile F.sig.mixed) (who : ι)
    (replacement : FinDist (F.sig.Strategy who)) :
    probs F.sig (Profile.update mu who replacement) =
      Profile.update (probs F.sig mu) who replacement.prob := by
  funext j
  by_cases h : j = who
  · subst h
    show (Profile.update mu j replacement j).prob = _
    rw [Profile.update_same, Profile.update_same]
  · show (Profile.update mu who replacement j).prob = _
    rw [Profile.update_of_ne _ _ h, Profile.update_of_ne _ _ h]
    rfl

/-- The analytic best-reply set is exactly the canonical semantic
`IsBestResponse` predicate after transporting finite laws to their probability
vectors.  This is the bridge between the fixed-point proof and the concepts in
`Core.Response`. -/
theorem prob_mem_bestReply_iff_isBestResponse (opponents : Profile F.sig.mixed)
    (who : ι) (candidate : FinDist (F.sig.Strategy who)) :
    candidate.prob ∈ bestReply F utility who (probs F.sig opponents) ↔
      IsBestResponse F.mixed (euPreference utility) who opponents candidate := by
  constructor
  · rintro ⟨_, hmax⟩ alternative
    have hle := hmax alternative.prob alternative.prob_mem_stdSimplex
    show expectedUtility utility who
        (F.mixed.play (Profile.update opponents who alternative)) ≤
      expectedUtility utility who
        (F.mixed.play (Profile.update opponents who candidate))
    rw [← payoff_probs, ← payoff_probs, probs_update, probs_update]
    exact hle
  · intro hbest
    refine ⟨candidate.prob_mem_stdSimplex, fun weights hweights => ?_⟩
    let alternative : FinDist (F.sig.Strategy who) := FinDist.ofSimplex hweights
    have hle := hbest alternative
    rw [euPreference_apply, ← payoff_probs, ← payoff_probs,
      probs_update, probs_update, FinDist.prob_ofSimplex] at hle
    exact hle

variable (F) in
/-- Every player best replying at once. A fixed point of this correspondence is
an equilibrium. -/
def bestReplies (x : Profile F.sig.weights) : Set (Profile F.sig.weights) :=
  Set.pi Set.univ fun i => bestReply F utility i x

theorem bestReplies_subset (x : Profile F.sig.weights) :
    bestReplies F utility x ⊆ mixedPolytope F.sig := fun _ hy i _ =>
  bestReply_subset utility i x (hy i (Set.mem_univ i))

theorem convex_bestReplies (x : Profile F.sig.weights) :
    Convex ℝ (bestReplies F utility x) :=
  convex_pi fun i _ => convex_bestReply utility i x

theorem bestReplies_nonempty [∀ i, Nonempty (F.sig.Strategy i)] (x : Profile F.sig.weights) :
    (bestReplies F utility x).Nonempty := by
  choose v hv using fun i => bestReply_nonempty utility i x
  exact ⟨v, fun i _ => hv i⟩

/-- Membership in the product correspondence is simultaneous semantic best
response. -/
theorem probs_mem_bestReplies_iff (opponents candidates : Profile F.sig.mixed) :
    probs F.sig candidates ∈ bestReplies F utility (probs F.sig opponents) ↔
      ∀ who, IsBestResponse F.mixed (euPreference utility) who opponents
        (candidates who) := by
  simp only [bestReplies, Set.mem_pi, Set.mem_univ, forall_const]
  exact forall_congr' fun who =>
    prob_mem_bestReply_iff_isBestResponse utility opponents who (candidates who)

/-- A fixed point of the analytic correspondence is exactly a mixed Nash
equilibrium under the canonical core predicate. -/
theorem probs_mem_bestReplies_self_iff_isNash (profile : Profile F.sig.mixed) :
    probs F.sig profile ∈ bestReplies F utility (probs F.sig profile) ↔
      IsNash F.mixed (euPreference utility) profile := by
  rw [probs_mem_bestReplies_iff]
  exact (isNash_iff_isBestResponse (F := F.mixed)
    (weaklyPrefers := euPreference utility) profile).symm

/-- **The correspondence has a closed graph.** Each condition defining it is a
non-strict inequality between two continuous functions of the profile and the
reply jointly, and an intersection of closed sets is closed however large the
family is. -/
theorem closedGraph_bestReplies :
    closedGraph fun x : mixedPolytope F.sig => bestReplies F utility x.1 := by
  show IsClosed _
  have hset : {z : mixedPolytope F.sig × Profile F.sig.weights |
        z.2 ∈ bestReplies F utility z.1.1} =
      (⋂ i : ι, {z : mixedPolytope F.sig × Profile F.sig.weights |
          z.2 i ∈ stdSimplex ℝ (F.sig.Strategy i)}) ∩
        ⋂ i : ι, ⋂ w ∈ stdSimplex ℝ (F.sig.Strategy i),
          {z : mixedPolytope F.sig × Profile F.sig.weights |
            payoff F utility i (Profile.update z.1.1 i w) ≤
              payoff F utility i (Profile.update z.1.1 i (z.2 i))} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, bestReplies, bestReply,
      Set.mem_pi, Set.mem_univ, forall_const]
    exact forall_and
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun i => ?_)
    (isClosed_iInter fun i => isClosed_iInter fun w => isClosed_iInter fun _ => ?_)
  · exact (isClosed_stdSimplex ℝ _).preimage ((continuous_apply i).comp continuous_snd)
  · refine isClosed_le ?_ ?_
    · exact ((continuous_payoff i).comp (continuous_update_profile i w)).comp
        (continuous_subtype_val.comp continuous_fst)
    · exact (continuous_payoff i).comp ((continuous_profileUpdate i).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          ((continuous_apply i).comp continuous_snd)))

/-! ## From a fixed point to an equilibrium -/

/-- **Every finite game has an equilibrium in mixed strategies.** -/
theorem exists_isNash_mixed [∀ i, Nonempty (F.sig.Strategy i)] :
    ∃ μ : Profile F.sig.mixed, IsNash F.mixed (euPreference utility) μ := by
  obtain ⟨x, hx⟩ := kakutani_fixed_point (mixedPolytope F.sig) (convex_mixedPolytope F.sig)
    (isCompact_mixedPolytope F.sig) (mixedPolytope_nonempty F.sig)
    (fun x => bestReplies F utility x.1) (closedGraph_bestReplies utility)
    fun x => ⟨bestReplies_subset utility x.1, convex_bestReplies utility x.1,
      bestReplies_nonempty utility x.1⟩
  refine ⟨ofPolytope F.sig x.2, (probs_mem_bestReplies_self_iff_isNash utility _).mp ?_⟩
  rw [probs_ofPolytope]
  exact hx

end GameTheory
