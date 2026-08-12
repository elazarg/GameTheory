/-
Experimental: a concentrated collision has a three-role transfer unless its
tail pays a uniform minimum-fibre escape.  The fourth role is the terminal
coalition/background host; no cardinal reduction is claimed here.
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCausalCollisionRecipientAtom
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionConcentratedConsumer

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota] [Nonempty iota]

namespace ConcentratedCollisionFourRole

def tail
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    QuittingTerminalSemanticPair iota :=
  quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))

def root
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    iota → PMF Bool :=
  quittingProfileLiveRoot reward profile stage

def action
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (mover : iota) : Bool :=
  quittingRootBestEndpointAction reward
    (tail reward profile stage).1 (root reward profile stage) mover

def targetProfile
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (mover : iota) : (quittingGame reward).BehaviorProfile :=
  Function.update profile mover
    (quittingStagePureEndpointBehaviorDeviation reward profile mover stage
      (action reward profile stage mover))

def source
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) :
    QuittingTerminalSemanticPair iota :=
  quittingTerminalSemanticPair reward profile

def target
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (mover : iota) : QuittingTerminalSemanticPair iota :=
  quittingTerminalSemanticPair reward
    (targetProfile reward profile stage mover)

def gain
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (mover : iota) : ℝ :=
  quittingTerminalPayoff reward (targetProfile reward profile stage mover) mover -
    quittingTerminalPayoff reward profile mover

def routed
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (terminal : Finset iota) (mover : iota) : Finset iota :=
  quittingPureEndpointRoutedCoalition terminal mover
    (action reward profile stage mover)

/-- The local object exposed by a recurrent collision.  There are three
strategic labels: the reset owner, a different profitable mover, and a debt
recipient different from the mover.  The routed terminal coalition is kept
literally, rather than replaced by a rank bound. -/
structure ThreeRoleTransfer
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (owner : iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset iota // S.Nonempty})
    (lower epsilon : ℝ)
    (minimum : QuittingTerminalSemanticPair iota) where
  mover : iota
  recipient : iota
  mover_ne_owner : mover ≠ owner
  recipient_ne_mover : recipient ≠ mover
  gain_pos : 0 < gain reward profile stage mover
  gain_quantitative :
    lower ^ 2 * quittingTerminalSemanticDebtSum minimum / 2 ≤
      (Fintype.card iota : ℝ) * gain reward profile stage mover
  target_mem : target reward profile stage mover ∈
    quittingTerminalSemanticCarrier reward
  mover_debt_exact :
    quittingTerminalSemanticDebt (target reward profile stage mover) mover =
      quittingTerminalSemanticDebt (source reward profile) mover -
        gain reward profile stage mover
  transfer_sum :
    gain reward profile stage mover - epsilon ≤
      ∑ other ∈ Finset.univ.erase mover,
        quittingTerminalSemanticDebtChange (source reward profile)
          (target reward profile stage mover) other
  recipient_mem : recipient ∈ Finset.univ.erase mover
  recipient_pos : 0 <
    quittingTerminalSemanticDebtChange (source reward profile)
      (target reward profile stage mover) recipient
  recipient_quantitative :
    (gain reward profile stage mover - epsilon) /
        ((Finset.univ.erase mover).card : ℝ) ≤
      quittingTerminalSemanticDebtChange (source reward profile)
        (target reward profile stage mover) recipient
  recipient_atom : HasQuittingEndpointDebtRecipientAtom reward profile mover
    recipient (quittingStagePureEndpointBehaviorDeviation reward profile mover
      stage (action reward profile stage mover))
  routed_mass : lower ≤ quittingRootCoalitionMass
    (Function.update (root reward profile stage) mover
      (PMF.pure (action reward profile stage mover)))
    (routed reward profile stage terminal.val mover)
  orientation :
    ((mover ∈ terminal.val ∧ action reward profile stage mover = true ∧
        routed reward profile stage terminal.val mover = terminal.val) ∨
      (mover ∈ terminal.val ∧ action reward profile stage mover = false ∧
        routed reward profile stage terminal.val mover = terminal.val.erase mover) ∨
      (mover ∉ terminal.val ∧ action reward profile stage mover = true ∧
        routed reward profile stage terminal.val mover = insert mover terminal.val) ∨
      (mover ∉ terminal.val ∧ action reward profile stage mover = false ∧
        routed reward profile stage terminal.val mover = terminal.val))

/-- A quantitative recipient chosen by maximization survives with a
cardinality-only floor once the source excess is below half the collision
gain threshold. -/
theorem ThreeRoleTransfer.recipient_globalFloor
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {owner : iota}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {terminal : {S : Finset iota // S.Nonempty}}
    {lower epsilon : ℝ} {minimum : QuittingTerminalSemanticPair iota}
    (transfer : ThreeRoleTransfer reward owner profile stage terminal
      lower epsilon minimum)
    (hlower : 0 < lower)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hepsilonHalf : epsilon ≤
      lower ^ 2 * quittingTerminalSemanticDebtSum minimum /
        (4 * (Fintype.card iota : ℝ))) :
    lower ^ 2 * quittingTerminalSemanticDebtSum minimum /
          (4 * (Fintype.card iota : ℝ) ^ 2) ≤
      quittingTerminalSemanticDebtChange (source reward profile)
        (target reward profile stage transfer.mover) transfer.recipient := by
  let A := lower ^ 2 * quittingTerminalSemanticDebtSum minimum
  let c : ℝ := Fintype.card iota
  let r : ℝ := (Finset.univ.erase transfer.mover).card
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (sq_pos_of_pos hlower) hminimumDebt
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast (Finset.nonempty_iff_ne_empty.mpr
      (by intro hempty; simpa [hempty] using transfer.recipient_mem)).card_pos
  have hrc : r ≤ c := by
    dsimp only [r, c]
    exact_mod_cast Finset.card_le_univ (Finset.univ.erase transfer.mover)
  have hgainLower : A / (2 * c) ≤ gain reward profile stage transfer.mover := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hc)).2
    have hquant := transfer.gain_quantitative
    dsimp only [A, c] at hquant ⊢
    nlinarith [hquant]
  have hepsilonHalf' : epsilon ≤ A / (4 * c) := by
    simpa only [A, c] using hepsilonHalf
  have hnet : A / (4 * c) ≤
      gain reward profile stage transfer.mover - epsilon := by
    have hdouble : A / (2 * c) = 2 * (A / (4 * c)) := by
      field_simp [hc.ne']
      all_goals ring
    rw [hdouble] at hgainLower
    linarith
  have hdenominator : A / (4 * c ^ 2) ≤ (A / (4 * c)) / r := by
    have hnumNonneg : 0 ≤ A / (4 * c) :=
      div_nonneg hA.le (mul_nonneg (by norm_num) hc.le)
    have hdivide : (A / (4 * c)) / c ≤ (A / (4 * c)) / r :=
      div_le_div_of_nonneg_left hnumNonneg hr hrc
    calc
      A / (4 * c ^ 2) = (A / (4 * c)) / c := by ring
      _ ≤ (A / (4 * c)) / r := hdivide
  have hnetDivide : (A / (4 * c)) / r ≤
      (gain reward profile stage transfer.mover - epsilon) / r :=
    div_le_div_of_nonneg_right hnet hr.le
  exact (by
    simpa only [A, c, r] using
      hdenominator.trans (hnetDivide.trans transfer.recipient_quantitative))

/-- **Local three-role theorem.**  If the reset owner's row defect is below
the collision-gain threshold, the causal collision mover cannot be that
owner.  Near-minimality then supplies a genuinely different positive-debt
recipient, unless the marked tail has already escaped the minimum fibre by a
uniform amount. -/
theorem tailEscape_or_threeRoleTransfer
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (owner : iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset iota // S.Nonempty})
    (lower epsilon : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hlower : 0 < lower)
    (hnear : quittingTerminalSemanticDebtSum (source reward profile) ≤
      quittingTerminalSemanticDebtSum minimum + epsilon)
    (hmass : lower ≤
      quittingStageCoalitionMass reward profile stage terminal)
    (hepsilon : epsilon <
      lower ^ 2 * quittingTerminalSemanticDebtSum minimum /
        (2 * (Fintype.card iota : ℝ)))
    (hownerSmall : (Fintype.card iota : ℝ) *
        quittingRootCoordinateNashDefect reward
          (tail reward profile stage).1 (root reward profile stage) owner <
      lower ^ 2 * quittingTerminalSemanticDebtSum minimum / 2) :
    (lower * quittingTerminalSemanticDebtSum minimum / 2 ≤
        quittingTerminalSemanticDebtSum (tail reward profile stage) -
          quittingTerminalSemanticDebtSum minimum) ∨
      Nonempty (ThreeRoleTransfer reward owner profile stage terminal
        lower epsilon minimum) := by
  have hdispatch :=
    causalCollision_tailEscape_or_quantitativeNearMinimumTransfer
      reward minimum profile stage terminal lower epsilon hM hreward
        hminimumCarrier hminimum hminimumDebt hcollision hlower hnear hmass
  dsimp only at hdispatch
  rcases hdispatch with hescape | hgain
  · exact Or.inl hescape.1
  · right
    rcases hgain with ⟨mover, hgainPos, hquant, htargetMem, hmoverDebt,
      htransfer, hrecipient, hrouted, horientation⟩
    have hmoverNe : mover ≠ owner := by
      intro heq
      subst mover
      have hformula :=
        quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
          reward profile owner stage
      have hdefectNonneg := quittingRootCoordinateNashDefect_nonneg reward
        (tail reward profile stage).1 (root reward profile stage) owner
      have hliveLe := quittingLiveMass_le_one reward profile stage
      have hgainLe : gain reward profile stage owner ≤
          quittingRootCoordinateNashDefect reward
            (tail reward profile stage).1 (root reward profile stage) owner := by
        rw [show gain reward profile stage owner =
            quittingLiveMass reward profile stage *
              quittingRootCoordinateNashDefect reward
                (tail reward profile stage).1
                (root reward profile stage) owner by
          simpa only [gain, targetProfile, action, tail, root] using hformula]
        exact mul_le_of_le_one_left hdefectNonneg hliveLe
      have hcardNonneg : 0 ≤ (Fintype.card iota : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hgainLe hcardNonneg
      have hquant' :
          lower ^ 2 * quittingTerminalSemanticDebtSum minimum / 2 ≤
            (Fintype.card iota : ℝ) * gain reward profile stage owner := by
        simpa only [gain, targetProfile, action, tail, root] using hquant
      exact (not_lt_of_ge hquant') (this.trans_lt hownerSmall)
    have hcardPos : 0 < (Fintype.card iota : ℝ) := by positivity
    have hgainThreshold :
        lower ^ 2 * quittingTerminalSemanticDebtSum minimum /
              (2 * (Fintype.card iota : ℝ)) ≤
            gain reward profile stage mover := by
      dsimp only [gain, targetProfile, action, tail, root] at hquant ⊢
      apply (div_le_iff₀ (mul_pos (by norm_num) hcardPos)).2
      nlinarith
    have hepsGain : epsilon < gain reward profile stage mover :=
      hepsilon.trans_le hgainThreshold
    obtain ⟨someRecipient, hsomeMem, _hsomePos⟩ := hrecipient hepsGain
    let change : iota → ℝ := fun recipient ↦
      quittingTerminalSemanticDebtChange (source reward profile)
        (target reward profile stage mover) recipient
    have hrecipientsNonempty : (Finset.univ.erase mover).Nonempty :=
      ⟨someRecipient, hsomeMem⟩
    obtain ⟨recipient, hrecipientMem, hrecipientMax⟩ :=
      Finset.exists_max_image (Finset.univ.erase mover) change
        hrecipientsNonempty
    have hsumLe :
        (∑ other ∈ Finset.univ.erase mover, change other) ≤
          ((Finset.univ.erase mover).card : ℝ) * change recipient := by
      have hsum := (Finset.univ.erase mover).sum_le_card_nsmul
        change (change recipient) (fun other hother ↦ hrecipientMax other hother)
      simpa only [nsmul_eq_mul] using hsum
    have hrecipientCardPos : 0 <
        ((Finset.univ.erase mover).card : ℝ) := by
      exact_mod_cast hrecipientsNonempty.card_pos
    have hrecipientQuantitative :
        (gain reward profile stage mover - epsilon) /
              ((Finset.univ.erase mover).card : ℝ) ≤
            change recipient := by
      apply (div_le_iff₀ hrecipientCardPos).2
      have htransfer' : gain reward profile stage mover - epsilon ≤
          ∑ other ∈ Finset.univ.erase mover, change other := by
        simpa only [change, target, source, gain, targetProfile, action, tail,
          root] using htransfer
      exact htransfer'.trans (by simpa [mul_comm] using hsumLe)
    have hrecipientPos : 0 < change recipient := by
      have hnumerator : 0 < gain reward profile stage mover - epsilon :=
        sub_pos.mpr hepsGain
      exact (div_pos hnumerator hrecipientCardPos).trans_le
        hrecipientQuantitative
    refine ⟨⟨mover, recipient, hmoverNe, ?_, ?_, ?_, ?_, ?_, ?_,
      hrecipientMem, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact (Finset.mem_erase.mp hrecipientMem).1
    · simpa only [gain, targetProfile, action, tail, root] using hgainPos
    · simpa only [gain, targetProfile, action, tail, root] using hquant
    · simpa only [target, targetProfile, action, tail, root] using htargetMem
    · simpa only [target, source, gain, targetProfile, action, tail, root]
        using hmoverDebt
    · simpa only [target, source, gain, targetProfile, action, tail, root]
        using htransfer
    · simpa only [change, target, source, targetProfile, action, tail, root]
        using hrecipientPos
    · simpa only [change, target, source, gain, targetProfile, action, tail,
        root] using hrecipientQuantitative
    · apply hasQuittingEndpointDebtRecipientAtom_of_pos reward profile mover
        recipient (quittingStagePureEndpointBehaviorDeviation reward profile
          mover stage (action reward profile stage mover)) hM hreward
      simpa only [source, target, targetProfile, action, tail, root] using
        (show 0 < quittingTerminalSemanticDebtChange (source reward profile)
            (target reward profile stage mover) recipient by
          simpa only [change] using hrecipientPos)
    · simpa only [routed, action, tail, root] using hrouted
    · simpa only [routed, action, tail, root] using horientation

def packetProfile
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  profiles (packet.subseq rank)

def packetEpsilon
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (rank : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum
      (source reward (packetProfile packet rank)) -
    quittingTerminalSemanticDebtSum minimum

def packetEscape
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (rank : ℕ) : Prop :=
  packet.resolution * quittingTerminalSemanticDebtSum minimum / 2 ≤
    quittingTerminalSemanticDebtSum
        (tail reward (packetProfile packet rank) (packet.mark rank)) -
      quittingTerminalSemanticDebtSum minimum

def packetTransfer
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (rank : ℕ) : Type :=
  ThreeRoleTransfer reward owner (packetProfile packet rank)
    (packet.mark rank) terminal packet.resolution
      (packetEpsilon minimum packet rank) minimum

/-- The local compiler applies eventually on every recurrent marked row of a
concentrated packet whose source total debts return to the minimum.  Thus the
packet is eventually exhausted by only two alternatives: uniform tail escape
or an executable three-role transfer. -/
theorem packet_eventually_tailEscape_or_threeRoleTransfer
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (minimum : QuittingTerminalSemanticPair iota)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0))
    (hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (source reward (packetProfile packet rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum))) :
    ∀ᶠ rank in atTop,
      packetEscape minimum packet rank ∨
        Nonempty (packetTransfer minimum packet rank) := by
  let eps : ℕ → ℝ := fun rank ↦ packetEpsilon minimum packet rank
  let ownerDefect : ℕ → ℝ := fun rank ↦
    quittingRootCoordinateNashDefect reward
      (tail reward (packetProfile packet rank) (packet.mark rank)).1
      (root reward (packetProfile packet rank) (packet.mark rank)) owner
  have hepsZero : Tendsto eps atTop (nhds 0) := by
    have hsub := hsourceDebt.sub_const
      (quittingTerminalSemanticDebtSum minimum)
    simpa only [eps, packetEpsilon, sub_self] using hsub
  have hownerZero : Tendsto ownerDefect atTop (nhds 0) := by
    simpa only [ownerDefect, packetProfile, tail, root] using
      packet.ownerDefect_tendsto_zero hscale hscaleTendsto
  have hresolutionSq : 0 < packet.resolution ^ 2 := sq_pos_of_pos packet.resolution_pos
  have hnumerator : 0 <
      packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum :=
    mul_pos hresolutionSq hminimumDebt
  have hcardPos : 0 < (Fintype.card iota : ℝ) := by positivity
  have hthreshold : 0 <
      packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum /
        (2 * (Fintype.card iota : ℝ)) :=
    div_pos hnumerator (mul_pos (by norm_num) hcardPos)
  have hownerThreshold : 0 <
      packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum / 2 := by
    exact div_pos hnumerator (by norm_num)
  have hepsSmall : ∀ᶠ rank in atTop, eps rank <
      packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum /
        (2 * (Fintype.card iota : ℝ)) :=
    hepsZero.eventually_lt_const hthreshold
  have hownerScaled : Tendsto (fun rank ↦
      (Fintype.card iota : ℝ) * ownerDefect rank) atTop (nhds 0) := by
    simpa using hownerZero.const_mul (Fintype.card iota : ℝ)
  have hownerSmall : ∀ᶠ rank in atTop,
      (Fintype.card iota : ℝ) * ownerDefect rank <
        packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum / 2 :=
    hownerScaled.eventually_lt_const hownerThreshold
  filter_upwards [hepsSmall, hownerSmall] with rank heps howner
  have hnear : quittingTerminalSemanticDebtSum
        (source reward (packetProfile packet rank)) ≤
      quittingTerminalSemanticDebtSum minimum + eps rank := by
    dsimp only [eps, packetEpsilon]
    linarith
  have hrow := tailEscape_or_threeRoleTransfer reward minimum owner
    (packetProfile packet rank) (packet.mark rank) terminal
      packet.resolution (eps rank) hM hreward hminimumCarrier hminimum
      hminimumDebt hcollision packet.resolution_pos hnear
      (packet.stageMass rank) heps howner
  simpa only [packetEscape, packetTransfer, eps] using hrow

def packetTransferRoles
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (rank : ℕ) (mover recipient : iota) : Prop :=
  ∃ transfer : packetTransfer minimum packet rank,
    transfer.mover = mover ∧ transfer.recipient = recipient

inductive RecipientAtomMode where
  | prescribed
  | rectangle
deriving DecidableEq, Fintype

def packetTransferAtomLabel
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {marked : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (rank : ℕ) (mover recipient : iota)
    (mode : RecipientAtomMode)
    (terminal : {S : Finset iota // S.Nonempty}) : Prop :=
  ∃ transfer : packetTransfer minimum packet rank,
    transfer.mover = mover ∧ transfer.recipient = recipient ∧
      let profile := packetProfile packet rank
      let endpoint := targetProfile reward profile (packet.mark rank)
        transfer.mover
      let charge := quittingTerminalSemanticDebtChange
        (source reward profile)
        (target reward profile (packet.mark rank) transfer.mover)
        transfer.recipient
      match mode with
      | .prescribed =>
          charge / 2 ≤
            (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
              quittingTerminalPayoffDifferenceAtom reward profile endpoint
                transfer.recipient (some terminal)
      | .rectangle =>
          ∃ deviation : (quittingGame reward).BehaviorStrategy
              transfer.recipient,
            charge / 4 ≤
              (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
                quittingTerminalPayoffDifferenceAtom reward
                  (Function.update endpoint transfer.recipient deviation)
                  (Function.update profile transfer.recipient deviation)
                  transfer.recipient (some terminal)

def packetRecipientCharge
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {marked : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (rank : ℕ) (mover recipient : iota) : ℝ :=
  quittingTerminalSemanticDebtChange
    (source reward (packetProfile packet rank))
    (target reward (packetProfile packet rank) (packet.mark rank) mover)
    recipient

def packetRecipientFloor
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {marked : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale) : ℝ :=
  packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum /
    (4 * (Fintype.card iota : ℝ) ^ 2)

omit [Nonempty iota] in
/-- Every role-labelled transfer exposes one finite decoder mode and one
literal absorbing outcome label. -/
theorem exists_packetTransferAtomLabel_of_roles
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {marked : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (rank : ℕ) (mover recipient : iota)
    (hroles : packetTransferRoles minimum packet rank mover recipient) :
    ∃ mode terminal,
      packetTransferAtomLabel minimum packet rank mover recipient
        mode terminal := by
  rcases hroles with ⟨transfer, hmover, hrecipient⟩
  have hatom := transfer.recipient_atom
  unfold HasQuittingEndpointDebtRecipientAtom at hatom
  dsimp only at hatom
  rcases hatom.2 with hprescribed | hrectangle
  · obtain ⟨terminal, hterminal⟩ := hprescribed
    refine ⟨.prescribed, terminal, transfer, hmover, hrecipient, ?_⟩
    simpa only [packetProfile, targetProfile, target, source, action, tail, root]
      using hterminal
  · obtain ⟨deviation, terminal, hterminal⟩ := hrectangle
    refine ⟨.rectangle, terminal, transfer, hmover, hrecipient,
      deviation, ?_⟩
    simpa only [packetProfile, targetProfile, target, source, action, tail, root]
      using hterminal

/-- Finiteness freezes the transport labels.  Either the uniform tail escape
recurs cofinally, or one fixed ordered mover--recipient pair recurs cofinally
on actual rows of the packet.  The reset owner is different from the mover,
and the recipient is different from the mover; the recipient may equal the
owner, which is the genuine two-cycle case. -/
theorem packet_tailEscapeFrequently_or_fixedThreeRoleTransfer
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (minimum : QuittingTerminalSemanticPair iota)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0))
    (hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (source reward (packetProfile packet rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum))) :
    (∃ᶠ rank in atTop, packetEscape minimum packet rank) ∨
      ∃ mover recipient,
        mover ≠ owner ∧ recipient ≠ mover ∧
          ∃ᶠ rank in atTop,
            packetTransferRoles minimum packet rank mover recipient := by
  have hrows := packet_eventually_tailEscape_or_threeRoleTransfer
    minimum packet hM hreward hminimumCarrier hminimum hminimumDebt
      hcollision hscale hscaleTendsto hsourceDebt
  by_cases hescape : ∃ᶠ rank in atTop, packetEscape minimum packet rank
  · exact Or.inl hescape
  · right
    have hnotEscape : ∀ᶠ rank in atTop,
        ¬ packetEscape minimum packet rank := not_frequently.mp hescape
    have htransfers : ∀ᶠ rank in atTop,
        Nonempty (packetTransfer minimum packet rank) := by
      filter_upwards [hrows, hnotEscape] with rank hrow hnot
      exact hrow.resolve_left hnot
    have hroleExists : ∀ᶠ rank in atTop,
        ∃ mover recipient,
          packetTransferRoles minimum packet rank mover recipient := by
      filter_upwards [htransfers] with rank htransfer
      rcases htransfer with ⟨transfer⟩
      exact ⟨transfer.mover, transfer.recipient, transfer, rfl, rfl⟩
    have hroleFrequently : ∃ᶠ rank in atTop,
        ∃ mover recipient,
          packetTransferRoles minimum packet rank mover recipient :=
      hroleExists.frequently
    rw [Filter.frequently_exists] at hroleFrequently
    obtain ⟨mover, hmover⟩ := hroleFrequently
    rw [Filter.frequently_exists] at hmover
    obtain ⟨recipient, hfixed⟩ := hmover
    obtain ⟨rank, transfer, hmoverEq, hrecipientEq⟩ := hfixed.exists
    exact ⟨mover, recipient,
      hmoverEq ▸ transfer.mover_ne_owner,
      hrecipientEq ▸ hmoverEq ▸ transfer.recipient_ne_mover,
      hfixed⟩

/-- The complete finite passport can be frozen with nonvanishing charge:
outside recurrent tail escape, one ordered transfer edge, one atom-decoder
mode, and one absorbing outcome label recur cofinally.  Their recipient debt
charge is bounded below by `resolution² * D / (4 * card²)`.  The profiles and
(in the rectangle case) the recipient deviations may still vary; that
remaining variation is exactly the stationarization seam. -/
theorem packet_tailEscapeFrequently_or_fixedThreeRoleAtomLabel
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (minimum : QuittingTerminalSemanticPair iota)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {marked : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < marked.val.card)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0))
    (hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (source reward (packetProfile packet rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum))) :
    (∃ᶠ rank in atTop, packetEscape minimum packet rank) ∨
      ∃ mover recipient mode terminal,
        mover ≠ owner ∧ recipient ≠ mover ∧
          ∃ᶠ rank in atTop,
            packetTransferAtomLabel minimum packet rank mover recipient
                mode terminal ∧
              packetRecipientFloor minimum packet ≤
                packetRecipientCharge packet rank mover recipient := by
  have hroles := packet_tailEscapeFrequently_or_fixedThreeRoleTransfer
    minimum packet hM hreward hminimumCarrier hminimum hminimumDebt
      hcollision hscale hscaleTendsto hsourceDebt
  rcases hroles with hescape | hfixed
  · exact Or.inl hescape
  · right
    obtain ⟨mover, recipient, hmover, hrecipient, hfrequent⟩ := hfixed
    let eps : ℕ → ℝ := fun rank ↦ packetEpsilon minimum packet rank
    have hepsZero : Tendsto eps atTop (nhds 0) := by
      have hsub := hsourceDebt.sub_const
        (quittingTerminalSemanticDebtSum minimum)
      simpa only [eps, packetEpsilon, sub_self] using hsub
    have hhalfPositive : 0 <
        packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum /
          (4 * (Fintype.card iota : ℝ)) := by
      have hcard : 0 < (Fintype.card iota : ℝ) := by positivity
      exact div_pos
        (mul_pos (sq_pos_of_pos packet.resolution_pos) hminimumDebt)
        (mul_pos (by norm_num) hcard)
    have hepsHalf : ∀ᶠ rank in atTop, eps rank ≤
        packet.resolution ^ 2 * quittingTerminalSemanticDebtSum minimum /
          (4 * (Fintype.card iota : ℝ)) :=
      (hepsZero.eventually_lt_const hhalfPositive).mono fun _ hlt ↦ hlt.le
    have hlabels : ∃ᶠ rank in atTop,
        ∃ mode terminal,
          packetTransferAtomLabel minimum packet rank mover recipient
              mode terminal ∧
            packetRecipientFloor minimum packet ≤
              packetRecipientCharge packet rank mover recipient := by
      apply hfrequent.mp
      filter_upwards [hepsHalf] with rank heps hrow
      rcases hrow with ⟨transfer, htransferMover, htransferRecipient⟩
      obtain ⟨mode, terminal, hlabel⟩ :=
        exists_packetTransferAtomLabel_of_roles minimum packet rank mover
          recipient ⟨transfer, htransferMover, htransferRecipient⟩
      refine ⟨mode, terminal, hlabel, ?_⟩
      have hfloor := transfer.recipient_globalFloor packet.resolution_pos
        hminimumDebt (by simpa only [eps] using heps)
      simpa only [packetRecipientFloor, packetRecipientCharge,
        packetTransfer, packetProfile, htransferMover, htransferRecipient]
        using hfloor
    rw [Filter.frequently_exists] at hlabels
    obtain ⟨mode, hmode⟩ := hlabels
    rw [Filter.frequently_exists] at hmode
    obtain ⟨terminal, hterminal⟩ := hmode
    exact ⟨mover, recipient, mode, terminal, hmover, hrecipient, hterminal⟩

end ConcentratedCollisionFourRole

end GameTheory
