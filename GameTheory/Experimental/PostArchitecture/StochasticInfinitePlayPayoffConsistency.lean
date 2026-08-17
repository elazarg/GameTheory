/-
# EXP-113: pathwise finite-average consistency

The canonical path and its fixed-horizon projection read the same finite
stage records.  This is a finite, pathwise bridge; it makes no limiting or
expectation-limit bridge claim.
-/

import GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffBridge

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffConsistency

open MeasureTheory
open GameTheory.Math.Probability
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Stochastic
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure.Game
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffBridge
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffBridge.Game

universe uι us ua

namespace Game

variable {ι : Type uι} (G : Stochastic.Game.{uι, us, ua} ι)
variable [Fintype ι]
variable (initial : G.State) [∀ i, Nonempty (G.Action i)]
variable (profile : G.BehaviorProfile initial)
variable [Countable (CanonicalHistory G initial)]

omit [Fintype ι] [Countable (CanonicalHistory G initial)] in
private theorem publicHistory_zero (history : PathHistory G initial 0) :
    G.publicHistoryOfTrace initial history.1.trace = [] := by
  rcases history with ⟨⟨state, trace⟩, hlength⟩
  cases trace with
  | start => rfl
  | extend prior joint isLegal realized =>
      simp [Trace.length] at hlength

omit [Fintype ι] [Countable (CanonicalHistory G initial)] in
private theorem reverse_publicHistory_prefix
    (play : ∀ k, PathHistory G initial k) (horizon k : ℕ) (hk : k ≤ horizon)
    (hcoh : ∀ n : ℕ, ∃ (joint : ∀ i, Option (G.Action i))
      (isLegal : (G.toExecution initial).Legal (play n).1.state joint)
      (realized : (play (n + 1)).1.state ∈
        ((G.toExecution initial).step (play n).1.state ⟨joint, isLegal⟩).support),
      (play (n + 1)).1 = (play n).1.extend isLegal realized) :
    ∃ suffix : List G.StageRecord,
      (G.publicHistoryOfTrace initial (play horizon).1.trace).reverse =
        (G.publicHistoryOfTrace initial (play k).1.trace).reverse ++ suffix := by
  revert k
  induction horizon with
  | zero =>
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      have hpub0 := publicHistory_zero G initial (play 0)
      exact ⟨[], by simp [hpub0]⟩
  | succ horizon ih =>
      intro k hk
      by_cases hlast : k = horizon + 1
      · subst k
        exact ⟨[], by simp⟩
      · have hkle : k ≤ horizon := by
          exact Nat.le_of_lt_succ (lt_of_le_of_ne hk hlast)
        obtain ⟨suffix, hsuffix⟩ := ih k hkle
        obtain ⟨joint, isLegal, realized, hnext⟩ := hcoh horizon
        let event := G.stageRecordOfEvent initial
          ⟨(play horizon).1.state, joint, isLegal, _, realized⟩
        have hrev :
            (G.publicHistoryOfTrace initial (play (horizon + 1)).1.trace).reverse =
              (G.publicHistoryOfTrace initial (play horizon).1.trace).reverse ++
                [event] := by
          have hpub := congrArg
            (fun history : (G.toExecution initial).History =>
              G.publicHistoryOfTrace initial history.trace) hnext
          have hextend := G.publicHistoryOfTrace_extend initial
            (play horizon).1.trace joint isLegal realized
          have hpublic :
              G.publicHistoryOfTrace initial (play (horizon + 1)).1.trace =
                event :: G.publicHistoryOfTrace initial (play horizon).1.trace := by
            exact hpub.trans hextend
          rw [hpublic]
          simp [event]
        refine ⟨suffix ++ [event], ?_⟩
        rw [hrev, hsuffix, List.append_assoc]

omit [Fintype ι] [∀ i, Nonempty (G.Action i)]
    [Countable (CanonicalHistory G initial)] in
private theorem chronological_index_of_reverse_append
    {p q : G.PublicHistory} {suffix : List G.StageRecord}
    {n horizon : ℕ} (hp : p.length = n + 1)
    (hq : q.length = horizon) (hsuffix : q.reverse = p.reverse ++ suffix)
    (hn : n < horizon) :
    G.chronologicalOfPublicHistory q hq ⟨n, hn⟩ =
      G.chronologicalOfPublicHistory p hp ⟨n, Nat.lt_succ_self n⟩ := by
  unfold GameTheory.Stochastic.Game.chronologicalOfPublicHistory
  dsimp [Equiv.vectorEquivFin, List.Vector.get, List.Vector.toList]
  have hindex : n < p.reverse.length := by
    rw [List.length_reverse, hp]
    exact Nat.lt_succ_self n
  have happend : n < (p.reverse ++ suffix).length := by
    simp only [List.length_append]
    omega
  have hget : (p.reverse ++ suffix)[n]'happend = p.reverse[n]'hindex :=
    List.getElem_append_left hindex
  simpa only [hsuffix] using hget

omit [Fintype ι] [∀ i, Nonempty (G.Action i)]
    [Countable (CanonicalHistory G initial)] in
private theorem chronological_last_of_reverse_append
    {prior history : G.PublicHistory} {record : G.StageRecord} {n : ℕ}
    (hprior : prior.length = n) (hhistory : history.length = n + 1)
    (happend : history.reverse = prior.reverse ++ [record]) :
    G.chronologicalOfPublicHistory history hhistory ⟨n, Nat.lt_succ_self n⟩ =
      record := by
  unfold GameTheory.Stochastic.Game.chronologicalOfPublicHistory
  dsimp [Equiv.vectorEquivFin, List.Vector.get, List.Vector.toList]
  have hright : prior.reverse.length ≤ n := by
    rw [List.length_reverse, hprior]
  have hfull : n < (prior.reverse ++ [record]).length := by
    simp [hprior]
  have hget := List.getElem_append_right
    (as := prior.reverse) (bs := [record]) (i := n) hright (h₂ := hfull)
  have hlast : (prior.reverse ++ [record])[n]'hfull = record := by
    simpa only [List.length_reverse, hprior, Nat.sub_self,
      List.getElem_singleton] using hget
  simpa only [happend] using hlast

omit [Fintype ι] [Countable (CanonicalHistory G initial)] in
/-- A coherent path reads the same stage record from every longer projection. -/
theorem canonicalStageUtility_eq_projected_of_coherent
    (who : ι) (play : ∀ k, PathHistory G initial k) (horizon n : ℕ)
    (hn : n < horizon)
    (hcoh : ∀ k : ℕ, ∃ (joint : ∀ i, Option (G.Action i))
      (isLegal : (G.toExecution initial).Legal (play k).1.state joint)
      (realized : (play (k + 1)).1.state ∈
        ((G.toExecution initial).step (play k).1.state ⟨joint, isLegal⟩).support),
      (play (k + 1)).1 = (play k).1.extend isLegal realized) :
    canonicalStageUtility G initial who play n =
      G.stageRecordUtility
        ((chronologicalProjection G initial horizon play) ⟨n, hn⟩) who := by
  obtain ⟨suffix, hsuffix⟩ := reverse_publicHistory_prefix G initial play horizon
    (n + 1) (Nat.succ_le_of_lt hn) hcoh
  have hindex := chronological_index_of_reverse_append G (suffix := suffix)
    (by rw [G.publicHistoryOfTrace_length]; exact (play (n + 1)).2)
    (by rw [G.publicHistoryOfTrace_length]; exact (play horizon).2)
    hsuffix hn
  unfold canonicalStageUtility chronologicalProjection chronologicalAt
  exact congrArg (G.stageRecordUtility · who) hindex.symm

omit [Fintype ι] [Countable (CanonicalHistory G initial)] in
/-- A coherent path's `n`th utility is the utility of its `n`th extension. -/
theorem canonicalStageUtility_eq_extension_of_coherent
    (who : ι) (play : ∀ k, PathHistory G initial k) (n : ℕ)
    (joint : ∀ i, Option (G.Action i))
    (isLegal : (G.toExecution initial).Legal (play n).1.state joint)
    (realized : (play (n + 1)).1.state ∈
      ((G.toExecution initial).step (play n).1.state ⟨joint, isLegal⟩).support)
    (hnext : (play (n + 1)).1 = (play n).1.extend isLegal realized) :
    canonicalStageUtility G initial who play n =
      G.stageRecordUtility
        (G.stageRecordOfEvent initial
          ⟨(play n).1.state, joint, isLegal, (play (n + 1)).1.state, realized⟩) who := by
  let record := G.stageRecordOfEvent initial
    ⟨(play n).1.state, joint, isLegal, (play (n + 1)).1.state, realized⟩
  have hpublic :
      G.publicHistoryOfTrace initial (play (n + 1)).1.trace =
        record :: G.publicHistoryOfTrace initial (play n).1.trace := by
    have hprojection := congrArg
      (fun history : (G.toExecution initial).History =>
        G.publicHistoryOfTrace initial history.trace) hnext
    exact hprojection.trans (G.publicHistoryOfTrace_extend initial
      (play n).1.trace joint isLegal realized)
  have hprefix :
      (G.publicHistoryOfTrace initial (play n).1.trace).length = n := by
    rw [G.publicHistoryOfTrace_length]
    exact (play n).2
  have hhistory :
      (G.publicHistoryOfTrace initial (play (n + 1)).1.trace).length = n + 1 := by
    rw [G.publicHistoryOfTrace_length]
    exact (play (n + 1)).2
  have happend :
      (G.publicHistoryOfTrace initial (play (n + 1)).1.trace).reverse =
        (G.publicHistoryOfTrace initial (play n).1.trace).reverse ++ [record] := by
    rw [hpublic]
    simp
  have hrecord := chronological_last_of_reverse_append G hprefix hhistory happend
  unfold canonicalStageUtility chronologicalProjection chronologicalAt
  simpa [record] using congrArg (G.stageRecordUtility · who) hrecord

omit [Fintype ι] [∀ i, Nonempty (G.Action i)]
    [Countable (CanonicalHistory G initial)] in
private theorem publicHistoryOfChronological_sum
    (who : ι) (horizon : ℕ) (history : G.ChronologicalHistory horizon) :
    ((G.publicHistoryOfChronological history).map
        (fun record => G.stageRecordUtility record who)).sum =
      ∑ n : Fin horizon, G.stageRecordUtility (history n) who := by
  unfold GameTheory.Stochastic.Game.publicHistoryOfChronological
  rw [List.map_reverse, List.sum_reverse]
  let vector := (Equiv.vectorEquivFin G.StageRecord horizon).symm history
  have hvector : vector.toList = List.ofFn vector.get := by
    calc
      vector.toList = (List.Vector.ofFn vector.get).toList :=
        congrArg List.Vector.toList (List.Vector.ofFn_get vector).symm
      _ = List.ofFn vector.get := List.Vector.toList_ofFn _
  rw [hvector, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro n hn
  have hv : (Equiv.vectorEquivFin G.StageRecord horizon) vector = history := by
    exact Equiv.apply_symm_apply _ _
  exact congrArg (fun record => G.stageRecordUtility record who)
    (congrFun hv n)

private theorem sum_range_eq_sum_fin {α : Type*} [AddCommMonoid α]
    (n : ℕ) (f : ℕ → α) :
    (∑ k ∈ Finset.range n, f k) = ∑ i : Fin n, f i := by
  rw [Finset.sum_subtype (p := fun x : ℕ => x ∈ Finset.range n)
    (Finset.range n) (fun x => Iff.rfl) f]
  let e : Fin n ≃ {k // k ∈ Finset.range n} :=
    { toFun := fun i => ⟨i, Finset.mem_range.2 i.isLt⟩
      invFun := fun i => ⟨i, Finset.mem_range.1 i.2⟩
      left_inv := fun i => rfl
      right_inv := fun i => by apply Subtype.ext; rfl }
  calc
    (∑ a : {k // k ∈ Finset.range n}, f a) = ∑ i : Fin n, f (e i) :=
      (e.sum_comp (fun a => f a)).symm
    _ = ∑ i : Fin n, f i := by
      apply Finset.sum_congr rfl
      intro i hi
      apply congrArg f
      simp [e]

theorem ae_stagewiseConsistency (who : ι) (horizon : ℕ) :
    ∀ᵐ play ∂infinitePlayMeasure G initial profile,
      canonicalPathAverage G initial who play horizon =
        canonicalProjectedAverage G initial who play horizon := by
  by_cases hhorizon : horizon = 0
  · filter_upwards [] with play
    simp [hhorizon]
  · filter_upwards [ae_all_path_coherent G initial profile] with play hcoh
    let history := chronologicalProjection G initial horizon play
    have hsumStage :
        (∑ n ∈ Finset.range horizon,
          canonicalStageUtility G initial who play n) =
          ∑ n : Fin horizon, G.stageRecordUtility (history n) who := by
      rw [sum_range_eq_sum_fin]
      apply Finset.sum_congr rfl
      intro n hn
      exact canonicalStageUtility_eq_projected_of_coherent G initial who play
        horizon n n.isLt (fun k => hcoh k)
    unfold canonicalPathAverage canonicalProjectedAverage
    rw [if_neg hhorizon, hsumStage]
    unfold GameTheory.Stochastic.Game.publicHistoryAverageUtility
    rw [publicHistoryOfChronological_sum]

theorem integral_canonicalPathAverage_eq_finiteAveragePayoff
    (who : ι) (horizon : ℕ) {C : ℝ}
    [Countable (G.ChronologicalHistory horizon)]
    (hstage_measurable :
      Measurable (fun history : G.ChronologicalHistory horizon =>
        G.publicHistoryAverageUtility horizon
          (G.publicHistoryOfChronological history) who))
    (hstage_bound :
      ∀ history : G.ChronologicalHistory horizon,
        ‖G.publicHistoryAverageUtility horizon
          (G.publicHistoryOfChronological history) who‖ ≤ C) :
    (∫ play, canonicalPathAverage G initial who play horizon ∂
      infinitePlayMeasure G initial profile) =
      G.finiteAveragePayoff initial horizon profile who := by
  exact integral_canonicalPathAverage_eq_finiteAveragePayoff_of_ae_stagewiseConsistency
    G initial profile who horizon hstage_measurable hstage_bound
      (ae_stagewiseConsistency G initial profile who horizon)

end Game

end GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffConsistency
