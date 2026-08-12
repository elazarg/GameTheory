/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashChronology
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMacroscopicAtomNashProvenance
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauNashMoat
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefix
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# Unique all-Continue caps cannot causally realize a retained terminal law

Suppose the unilateral-cap game at one literal continuation has the
all-Continue root as its unique exact Nash root.  Backward cap--Nash
iteration cannot escape this point.  Every root in every finite exact
cap--Nash stack over that continuation is all-Continue, the complete
terminal semantic pair is unchanged, and the stack has zero absorption.

This is the sharp negative consumer for an off-minimum unique-all-Continue
reset plateau.  A positive terminal cylinder retained at the endpoint stays
strictly in the continuation law: finite cap--Nash prefixing alone can never
promote it to a current-stage cylinder.  Any successful use of the plateau
must therefore change the cap/state, spend a law-retention premium, or add a
separate chronology-return argument.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The all-Continue action fixes every complete terminal-outcome law.  This
is the law-coordinate counterpart of the semantic fixed-point identity. -/
theorem quittingTerminalOutcomeLawPrefix_allContinue_eq_self
    (mass : QuittingTerminalOutcome ι → ℝ) :
    quittingTerminalOutcomeLawPrefix
        (quittingAllContinueRoot : ι → PMF Bool) mass = mass := by
  funext outcome
  cases outcome with
  | none =>
      simp [quittingTerminalOutcomeLawPrefix,
        quittingStationaryContinueMass, quittingAllContinueRoot,
        quittingAllContinueAction, Math.PMFProduct.pmfPi_apply]
  | some terminal =>
      simp [quittingTerminalOutcomeLawPrefix,
        quittingStationaryContinueMass, quittingRootCoalitionMass,
        quittingRootQuitRates, quittingAllContinueRoot,
        quittingAllContinueAction, Math.PMFProduct.pmfPi_apply,
        Math.PMFProduct.coalitionMass, terminal.property.ne_empty]

/-- **One-step architectural invariant.**  If the exact cap--Nash
correspondence is the singleton all-Continue root, every legal exact cap
prefix fixes the semantic pair and the complete terminal law and has zero
absorption.  In particular, the retained law cannot influence the root:
the root equations see only the cap coordinate. -/
theorem exactCapPrefix_joint_eq_self_of_unique_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward point.1.2 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward point.1.2 0 root) :
    quittingTerminalSemanticPrefix reward root point.1 = point.1 ∧
      quittingTerminalOutcomeLawPrefix root point.2 = point.2 ∧
      quittingRootAbsorptionMass root = 0 := by
  have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) :=
    hunique root hnash
  have hallContinueNash : IsεQuittingRootNash reward point.1.2 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    simpa only [hroot] using hnash
  have hcap : ∀ player,
      reward (quittingSingletonTerminal player) player ≤ point.1.2 player :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward point.1.2).1 hallContinueNash
  subst root
  exact ⟨
    quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
      (reward := reward) point.1 hcap,
    quittingTerminalOutcomeLawPrefix_allContinue_eq_self point.2,
    quittingRootAbsorptionMass_allContinueRoot⟩

/-- **Approximate version of the trap.**  Uniqueness of the exact
all-Continue root gives a positive Nash-defect moat around every fixed
positive absorption scale.  Hence even approximate roots at the unchanged
cap cannot carry macroscopic fresh absorption as their Nash error vanishes.

This is the compactness statement needed to rule out escaping the plateau by
replacing exact roots with increasingly accurate approximate ones. -/
theorem exists_absorptionNashDefect_moat_of_unique_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ ε root,
        IsεQuittingRootNash reward cap ε
            (quittingRootOfSimplex root) →
        Fintype.card ι * ε < moat →
        quittingSimplexAbsorptionMass root < eta := by
  let highAbsorption : Set (QuittingRootSimplex ι) :=
    {root | eta ≤ quittingSimplexAbsorptionMass root}
  have hhighClosed : IsClosed highAbsorption :=
    isClosed_Ici.preimage continuous_quittingSimplexAbsorptionMass
  have hhighCompact : IsCompact highAbsorption := hhighClosed.isCompact
  by_cases hhighNonempty : highAbsorption.Nonempty
  · have hdefectContinuous : Continuous (fun root : QuittingRootSimplex ι =>
        quittingRootTotalNashDefect reward cap
          (quittingRootOfSimplex root)) := by
      change Continuous
        ((fun point : Payoff ι × QuittingRootSimplex ι =>
            quittingRootTotalNashDefect reward point.1
              (quittingRootOfSimplex point.2)) ∘
          fun root : QuittingRootSimplex ι => (cap, root))
      exact (continuous_quittingRootTotalNashDefect_simplex reward).comp
        (continuous_const.prodMk continuous_id)
    obtain ⟨selected, hselectedHigh, hselectedMin⟩ :=
      hhighCompact.exists_isMinOn hhighNonempty
        hdefectContinuous.continuousOn
    have hselectedNonneg : 0 ≤ quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex selected) :=
      quittingRootTotalNashDefect_nonneg reward cap
        (quittingRootOfSimplex selected)
    have hselectedPositive : 0 < quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex selected) := by
      apply lt_of_le_of_ne hselectedNonneg
      intro hzero
      have hnash : IsεQuittingRootNash reward cap 0
          (quittingRootOfSimplex selected) :=
        (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
          (reward := reward) cap (quittingRootOfSimplex selected)).2 hzero.symm
      have hroot := hunique (quittingRootOfSimplex selected) hnash
      have habsorptionZero : quittingSimplexAbsorptionMass selected = 0 := by
        rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass, hroot]
        exact quittingRootAbsorptionMass_allContinueRoot
      have hselectedEta : eta ≤ quittingSimplexAbsorptionMass selected :=
        hselectedHigh
      rw [habsorptionZero] at hselectedEta
      linarith
    refine ⟨quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex selected), hselectedPositive, ?_⟩
    intro ε root hnash hsmall
    have hdefectUpper :=
      quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
        reward cap (quittingRootOfSimplex root) ε hnash
    by_contra hnot
    have hrootHigh : root ∈ highAbsorption := by
      exact le_of_not_gt hnot
    have hdefectLower :
        quittingRootTotalNashDefect reward cap
            (quittingRootOfSimplex selected) ≤
          quittingRootTotalNashDefect reward cap
            (quittingRootOfSimplex root) :=
      hselectedMin hrootHigh
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro ε root _hnash _hsmall
    exact lt_of_not_ge fun hrootHigh => hhighNonempty ⟨root, hrootHigh⟩

/-- **Positive-minimum plateau no-go.**  The strongest reset-face selector
does not merely exhibit one zero-charge root.  It produces a positive-law
point at which *every* exact cap/state operation is the identity on the full
joint semantic/law state and has zero absorption.

Thus neither repeated exact prefixing nor a different exact-root selection
can consume the retained incidence.  Escape requires an operation not
generated by exact cap prefixing at this state: a cap-changing reset with a
proved return, a nonexact root paid for by a quantitative Nash budget, or an
independently source-matched strategic edge. -/
theorem exists_resetFace_positiveIncidence_exactCapOperations_are_identity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (htarget : (target, mass) ∈
      quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target owner = 0)
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner mass) :
    ∃ returned : QuittingTerminalSemanticLawPoint ι,
      returned ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned.1 owner = 0 ∧
      0 < quittingTerminalTotalOpponentIncidenceMass owner returned.2 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned.1 ∧
      ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward returned.1.2 0 root →
          quittingTerminalSemanticPrefix reward root returned.1 = returned.1 ∧
          quittingTerminalOutcomeLawPrefix root returned.2 = returned.2 ∧
          quittingRootAbsorptionMass root = 0 := by
  obtain ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
      hsourceLe, _hallContinueNash, _hfixed, hallRoots⟩ :=
    exists_resetFace_positiveTotalIncidence_allContinueCapPlateau
      source target mass owner hM hreward hminimum hsourcePositive
        htarget hreset hincidence
  refine ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
    hsourceLe, ?_⟩
  intro root hnash
  exact exactCapPrefix_joint_eq_self_of_unique_allContinue
    reward returned hallRoots root hnash

/-- **Named-compiler no-go.**  An arbitrary exact punishment-floor prefix
anchored at a unique-all-Continue cap is the constant all-Continue prefix.
Every displayed value equals the anchor, every used root is all-Continue, and
the prefix charge is zero.  Repackaging the plateau in the canonical finite
prefix interface therefore cannot activate its unbounded-charge compiler. -/
theorem QuittingPunishmentFloorFinitePrefix.constant_of_unique_allContinue_anchor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward (cert.value 0) 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    (∀ time, time ≤ cert.horizon → cert.value time = cert.value 0) ∧
      (∀ time, time < cert.horizon →
        cert.roots time = (quittingAllContinueRoot : ι → PMF Bool)) ∧
      cert.charge = 0 := by
  have hvalue : ∀ time, time ≤ cert.horizon →
      cert.value time = cert.value 0 := by
    intro time htime
    induction time with
    | zero => rfl
    | succ time ih =>
        have htimeLt : time < cert.horizon := by omega
        have htimeLe : time ≤ cert.horizon := htimeLt.le
        have hnash := cert.exactNash time htimeLt
        have hcurrent := ih htimeLe
        rw [hcurrent] at hnash
        have hroot : cert.roots time =
            (quittingAllContinueRoot : ι → PMF Bool) :=
          hunique (cert.roots time) hnash
        rw [cert.policy time htimeLt, hroot]
        funext who
        rw [quittingRootSuccessorPayoff_eq_endpointMix]
        have hquit :
            ((quittingAllContinueRoot who) true).toReal = 0 := by
          simp [quittingAllContinueRoot]
        have hcontinue :
            ((quittingAllContinueRoot who) false).toReal = 1 := by
          simp [quittingAllContinueRoot]
        rw [hquit, hcontinue, zero_mul, zero_add, one_mul]
        rw [quittingRootContinuePayoff_allContinueRoot]
        exact congrFun hcurrent who
  have hroots : ∀ time, time < cert.horizon →
      cert.roots time = (quittingAllContinueRoot : ι → PMF Bool) := by
    intro time htime
    have hnash := cert.exactNash time htime
    rw [hvalue time htime.le] at hnash
    exact hunique (cert.roots time) hnash
  refine ⟨hvalue, hroots, ?_⟩
  unfold QuittingPunishmentFloorFinitePrefix.charge
  apply Finset.sum_eq_zero
  intro time htime
  rw [hroots time (Finset.mem_range.mp htime)]
  exact quittingRootAbsorptionMass_allContinueRoot

/-- Uniqueness at the terminal cap propagates through an arbitrary finite
cap--Nash stack.  The semantic-pair conclusion is included in the induction
because it is exactly what makes the uniqueness hypothesis reusable at the
preceding row. -/
theorem capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : List (ι → PMF Bool)) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward terminal).2 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    roots = List.replicate roots.length
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots terminal) =
        quittingTerminalSemanticPair reward terminal := by
  have hallContinueNash : IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward terminal).2 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash
      (reward := reward) (quittingTerminalSemanticPair reward terminal).2
    simpa only [hunique root hnash] using hnash
  have hcap : ∀ player,
      reward (quittingSingletonTerminal player) player ≤
        (quittingTerminalSemanticPair reward terminal).2 player :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward (quittingTerminalSemanticPair reward terminal).2).1
        hallContinueNash
  have hfixed : quittingTerminalSemanticPrefix reward
      quittingAllContinueRoot
        (quittingTerminalSemanticPair reward terminal) =
      quittingTerminalSemanticPair reward terminal := by
    apply Prod.ext
    · funext player
      change quittingRootSuccessorPayoff reward
          (quittingTerminalSemanticPair reward terminal).1
            quittingAllContinueRoot player =
        (quittingTerminalSemanticPair reward terminal).1 player
      rw [quittingRootSuccessorPayoff_eq_endpointMix]
      simp [quittingAllContinueRoot]
    · funext player
      simp only [quittingTerminalSemanticPrefix,
        quittingRootQuitPayoff_allContinueRoot,
        quittingRootContinuePayoff_allContinueRoot,
        Function.update_self]
      exact max_eq_right (hcap player)
  induction roots with
  | nil => exact ⟨rfl, rfl⟩
  | cons root roots ih =>
      rw [isQuittingCapNashRootStack_cons_iff] at hstack
      obtain ⟨hroots, hsemantic⟩ := ih hstack.2
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      have hrootNash : IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward suffix).2 0 root := by
        simpa only [suffix, quittingTerminalSemanticPair] using hstack.1
      have hrootNashTerminal : IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward terminal).2 0 root := by
        rw [show quittingTerminalSemanticPair reward suffix =
            quittingTerminalSemanticPair reward terminal by
          simpa only [suffix] using hsemantic] at hrootNash
        exact hrootNash
      have hroot : root =
          (quittingAllContinueRoot : ι → PMF Bool) :=
        hunique root hrootNashTerminal
      constructor
      · simp only [List.length_cons, List.replicate_succ]
        simpa only [hroot] using congrArg
          (List.cons (quittingAllContinueRoot : ι → PMF Bool)) hroots
      · rw [quittingLiteralRootStackProfile_cons,
          quittingTerminalSemanticPair_rootThenContinuation
            reward root suffix hM hreward]
        rw [show quittingTerminalSemanticPair reward suffix =
            quittingTerminalSemanticPair reward terminal by
          simpa only [suffix] using hsemantic,
          hroot]
        exact hfixed

/-- In particular, a finite exact cap--Nash chronology above a unique
all-Continue terminal cap has no current-stage absorption budget at all. -/
theorem capNashStackAbsorptionSum_eq_zero_of_unique_terminalCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : List (ι → PMF Bool)) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward terminal).2 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingCapNashStackAbsorptionSum roots = 0 := by
  have hroots :=
    (capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
      reward terminal roots hM hreward hunique hstack).1
  rw [hroots]
  simp [quittingCapNashStackAbsorptionSum,
    quittingRootAbsorptionMass_allContinueRoot]

/-- The same finite-stack invariant holds on the complete terminal law, not
only on the semantic projection.  Thus a retained atom is merely shifted
behind zero-charge Continue rows; it is never promoted to fresh absorption. -/
theorem capNashRootStack_terminalOutcomeMass_eq_of_unique_terminalCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : List (ι → PMF Bool)) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward terminal).2 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingTerminalOutcomeMass reward
        (quittingLiteralRootStackProfile reward roots terminal) =
      quittingTerminalOutcomeMass reward terminal := by
  have hroots :=
    (capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
      reward terminal roots hM hreward hunique hstack).1
  rw [hroots]
  let allContinue : ι → PMF Bool := quittingAllContinueRoot
  change quittingTerminalOutcomeMass reward
      (quittingLiteralRootStackProfile reward
        (List.replicate roots.length allContinue) terminal) =
    quittingTerminalOutcomeMass reward terminal
  induction roots.length with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, quittingLiteralRootStackProfile_cons]
      calc
        quittingTerminalOutcomeMass reward
            (quittingRootThenContinuationProfile reward allContinue
              (quittingLiteralRootStackProfile reward
                (List.replicate n allContinue) terminal)) =
            quittingTerminalOutcomeLawPrefix allContinue
              (quittingTerminalOutcomeMass reward
                (quittingLiteralRootStackProfile reward
                  (List.replicate n allContinue) terminal)) :=
          (quittingTerminalOutcomeLawPrefix_outcomeMass reward allContinue
            (quittingLiteralRootStackProfile reward
              (List.replicate n allContinue) terminal)).symm
        _ = quittingTerminalOutcomeMass reward
              (quittingLiteralRootStackProfile reward
                (List.replicate n allContinue) terminal) :=
          quittingTerminalOutcomeLawPrefix_allContinue_eq_self _
        _ = quittingTerminalOutcomeMass reward terminal := ih

end GameTheory
