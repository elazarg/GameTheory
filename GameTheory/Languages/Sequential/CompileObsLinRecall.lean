import GameTheory.Languages.Sequential.CompileObsLinAdequacy

/-!
# FullRecall → OLF, NNIR, and VRD descent for Linearized Compilation

Bridges `Protocol.FullRecall` to `ObsLocalFeasibility` and
`NoNontrivialInfoStateRepeat` on the linearized compiled model.
Also provides VRD (ViewDeterminesRound) agreement lemmas for M→B descent.

## Main results

- `obsLocalFeasibility_of_fullRecall` — FullRecall implies OLF on compiled model
- `noNontrivialInfoStateRepeat_compiledLin` — NNIR holds unconditionally
- `liftBehavioralProfile_descendVRD_agree` — lift ∘ descendVRD agrees at reachable states
- `liftPureProfile_descendVRD_agree` — pure profile version
-/

namespace GameTheory.Sequential

open GameTheory

variable {n : Nat} {S V A Sig : Type}

-- ============================================================================
-- ObsLocalFeasibility from FullRecall
-- ============================================================================

section OLFBridge

open Math.ParameterizedChain

variable [DecidableEq (Fin n)] [Fintype (Fin n)]
variable [Fintype A] [Nonempty A]
variable (G : Protocol n S V A Sig)

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- `linObserve G i cfg = some obs` implies cfg is a playerTurn for player i
at a valid round, and extracts the state, signals, and accumulated actions. -/
theorem linObserve_some_playerTurn (cfg : LinConfig G) (i : Fin n)
    (obs : RoundView G)
    (h : linObserve G i cfg = some obs) :
    ∃ (s : S) (sig : Fin n → Sig) (accActs : Fin n → Option A),
      cfg = .playerTurn obs.1.val s sig i accActs ∧
      (G.rounds[obs.1.val]'(obs.1.isLt)).view i s (sig i) = obs.2 := by
  cases cfg with
  | signal _ _ => simp [linObserve] at h
  | terminal _ => simp [linObserve] at h
  | applyTransition _ _ _ _ => simp [linObserve] at h
  | playerTurn k s sig p accActs =>
    simp only [linObserve] at h
    split at h
    · rename_i hip
      split at h
      · rename_i hk
        simp only [Option.some.injEq] at h
        subst hip
        have hk_eq : k = obs.1.val := by
          have := congrArg (fun x => x.1.val) h; simp at this; omega
        have hv_eq : G.rounds[k].view i s (sig i) = obs.2 := congrArg Prod.snd h
        subst hk_eq
        exact ⟨s, sig, accActs, rfl, hv_eq⟩
      · simp at h
    · simp at h

set_option linter.unusedFintypeInType false in
/-- `linObserve G i cfg = some obs` implies `cfg` is not done. -/
private theorem not_isDone_of_linObserve_some
    (cfg : LinConfig G) (i : Fin n) (obs : RoundView G)
    (h : linObserve G i cfg = some obs) : ¬ cfg.isDone G := by
  obtain ⟨s, sig, accActs, hcfg, _⟩ := linObserve_some_playerTurn G cfg i obs h
  subst hcfg
  change ¬ (G.rounds[obs.1.val]? = none)
  rw [show G.rounds[obs.1.val]? = some G.rounds[obs.1.val] from
    List.getElem?_eq_getElem obs.1.isLt]
  exact Option.some_ne_none _

set_option linter.unusedFintypeInType false in
/-- Phase of a config where `linObserve G i cfg = some (⟨r, hr⟩, v)`. -/
private theorem phase_of_linObserve_some
    (cfg : LinConfig G) (i : Fin n) (r : Fin G.rounds.length) (v : V)
    (h : linObserve G i cfg = some (r, v)) :
    cfg.phase G = r.val * (n + 2) + i.val + 1 := by
  obtain ⟨s, sig, accActs, hcfg, _⟩ := linObserve_some_playerTurn G cfg i ⟨r, v⟩ h
  rw [hcfg]; simp [LinConfig.phase]

set_option linter.unusedSectionVars false in
/-- On a nonzero trace, if `ss[b]` is not done, then `ss[a]` is not done for `a ≤ b`. -/
private theorem not_isDone_of_later_not_isDone
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (a b : Nat) (ha : a < ss.length) (hb : b < ss.length) (hab : a ≤ b)
    (hnd : ¬ (ss[b]'hb).isDone G) : ¬ (ss[a]'ha).isDone G := by
  intro hd; apply hnd
  suffices h : ∀ c, a ≤ c → (hc : c < ss.length) → (ss[c]'hc).isDone G from h b hab hb
  intro c hac
  induction c with
  | zero =>
    intro hc
    have ha0 : a = 0 := by omega
    subst ha0; exact hd
  | succ c ih =>
    intro hc
    by_cases hac' : a ≤ c
    · have hc' : c < ss.length := by omega
      have ihc := ih hac' hc'
      have hstep := pureRun_step_nonzero _ _ k pi ss hss c (show c + 1 < ss.length by omega)
      rw [pureStep_compiledLin_eq] at hstep
      have hcfg := lastState_take_eq_getElem ss c (show c + 1 < ss.length by omega)
      rw [hcfg] at hstep
      exact (isDone_step_of_isDone G _ _ ihc _ (PMF.mem_support_iff _ _ |>.mpr hstep)).1
    · have ha0 : a = c + 1 := by omega
      subst ha0; exact hd

/-- On a nonzero trace, if `ss[b]` is not done and `a < b`, then
`phase(ss[a]) < phase(ss[b])`. -/
private theorem phase_strict_mono_of_not_done
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (a b : Nat) (ha : a < ss.length) (hb : b < ss.length) (hab : a < b)
    (hnd : ¬ (ss[b]'hb).isDone G) :
    (ss[a]'ha).phase G < (ss[b]'hb).phase G := by
  induction b with
  | zero => omega
  | succ b' ih =>
    have hb'lt : b' < ss.length := by omega
    have hstep := pureRun_step_nonzero _ _ k pi ss hss b' (show b' + 1 < ss.length by omega)
    rw [pureStep_compiledLin_eq] at hstep
    have hcfg := lastState_take_eq_getElem ss b' (show b' + 1 < ss.length by omega)
    rw [hcfg] at hstep
    have hnd' : ¬ (ss[b']'hb'lt).isDone G :=
      not_isDone_of_later_not_isDone G pi k ss hss b' (b' + 1) hb'lt hb (by omega) hnd
    have hprog := phase_step_progress G _ _ hnd' _ (PMF.mem_support_iff _ _ |>.mpr hstep)
    by_cases hab' : a < b'
    · exact lt_of_lt_of_le (ih hb'lt hab' hnd') (by omega)
    · have hab'eq : a = b' := by omega
      subst hab'eq; omega

/-- The first element of a nonzero `pureRun` trace is the initial state. -/
private theorem pureRun_head_eq_init
    {T P : Type} (step : P → List T → PMF T) (s₀ : T)
    (m : Nat) (π : P) (ss : List T)
    (h : pureRun step s₀ m π ss ≠ 0)
    (h0 : 0 < ss.length) :
    ss[0] = s₀ := by
  induction m generalizing ss with
  | zero =>
    have hss : ss = [s₀] := by
      by_contra hne; exact h (by simp [pureRun, PMF.pure_apply, hne])
    subst hss; rfl
  | succ m ih =>
    have hne : ss ≠ [] := by intro he; subst he; simp at h0
    have hsplit := (List.dropLast_append_getLast hne).symm
    have h_pre : pureRun step s₀ m π ss.dropLast ≠ 0 := by
      rw [hsplit] at h; rw [pureRun_succ_append] at h; exact left_ne_zero_of_mul h
    have hlen_pre : 0 < ss.dropLast.length := by
      have := pureRun_length step s₀ m π ss.dropLast h_pre; omega
    have hih := ih ss.dropLast h_pre hlen_pre
    -- ss[0] = ss.dropLast[0] since dropLast is a prefix
    have h_eq : ss[0] = ss.dropLast[0]'hlen_pre := by
      rcases ss with _ | ⟨hd, tl⟩
      · exact absurd rfl hne
      · cases tl with
        | nil => simp at hlen_pre
        | cons h t => rfl
    rw [h_eq, hih]

set_option linter.unusedSectionVars false in
/-- On a nonzero trace where `ss[last]` is not done, `phase(ss[j]) = j` for all j. -/
private theorem phase_eq_index
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (hlast_nd : ¬ (ss[ss.length - 1]'(by
      have := pureRun_length _ _ k pi ss hss; omega)).isDone G)
    (j : Nat) (hj : j < ss.length) :
    (ss[j]'hj).phase G = j := by
  induction j with
  | zero =>
    have hlen : 0 < ss.length := by omega
    have h0 := pureRun_head_eq_init _ _ k pi ss hss hlen
    conv_lhs => rw [show ss[0]'hj = ss[0]'hlen from rfl, h0]
    -- linInitialConfig G phase
    simp only [compiledLinObs, compileObsCoreModelLin, linInitialConfig]
    split
    · -- rounds empty: terminal phase = G.rounds.length * (n+2) = 0
      rename_i hempty
      simp only [LinConfig.phase]
      have : G.rounds.length = 0 := by
        by_contra hne; push Not at hne
        have : G.rounds[0]? ≠ none := by
          rw [ne_eq, List.getElem?_eq_none_iff]; omega
        exact this hempty
      simp [this]
    · simp [LinConfig.phase]
  | succ j ih =>
    have hjlt : j < ss.length := by omega
    have hnd_j : ¬ (ss[j]'hjlt).isDone G :=
      not_isDone_of_later_not_isDone G pi k ss hss j (ss.length - 1) hjlt
        (by have := pureRun_length _ _ k pi ss hss; omega) (by omega) hlast_nd
    have hstep := pureRun_step_nonzero _ _ k pi ss hss j (show j + 1 < ss.length by omega)
    rw [pureStep_compiledLin_eq] at hstep
    have hcfg := lastState_take_eq_getElem ss j (show j + 1 < ss.length by omega)
    rw [hcfg] at hstep
    have hprog := phase_step_progress G _ _ hnd_j _ (PMF.mem_support_iff _ _ |>.mpr hstep)
    rw [hprog, ih hjlt]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- A config with phase `r*(n+2) + i.val + 1` (where `r < G.rounds.length` and `i < n`)
is a `playerTurn` for player `i` at round `r`, so `linObserve G i` returns `some`. -/
private theorem linObserve_of_phase_eq
    (cfg : LinConfig G) (p : Fin n)
    (r : Nat) (hr : r < G.rounds.length)
    (hphase : cfg.phase G = r * (n + 2) + p.val + 1) :
    ∃ (v : V), linObserve G p cfg = some (⟨r, hr⟩, v) := by
  cases cfg with
  | signal k s =>
    simp only [LinConfig.phase] at hphase
    -- k*(n+2) = r*(n+2) + p.val + 1, impossible since p.val+1 < n+2
    exfalso
    rcases le_or_gt r k with hrk | hrk
    · have heq : (k - r) * (n + 2) = p.val + 1 := by
        rw [Nat.sub_mul]; omega
      rcases Nat.eq_zero_or_pos (k - r) with h0 | h0
      · simp [h0] at heq
      · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
    · have : k * (n + 2) < r * (n + 2) :=
        (Nat.mul_lt_mul_right (by omega : 0 < n + 2)).mpr hrk
      omega
  | playerTurn k s sig q accActs =>
    simp only [LinConfig.phase] at hphase
    -- k*(n+2) + q.val + 1 = r*(n+2) + p.val + 1 → k = r, q = p
    have hk : k = r := by
      rcases le_or_gt r k with hrk | hrk
      · rcases le_or_gt k r with hkr | hkr
        · omega
        · have : (k - r) * (n + 2) = p.val - q.val := by rw [Nat.sub_mul]; omega
          rcases Nat.eq_zero_or_pos (k - r) with h0 | h0
          · omega
          · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
      · have : (r - k) * (n + 2) = q.val - p.val := by rw [Nat.sub_mul]; omega
        rcases Nat.eq_zero_or_pos (r - k) with h0 | h0
        · omega
        · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
    subst hk
    have hp : q = p := Fin.ext (by omega)
    subst hp
    simp only [linObserve]
    split
    · exact ⟨G.rounds[k].view q s (sig q), rfl⟩
    · rename_i habs
      exfalso
      have : G.rounds[k]? ≠ none := by rw [ne_eq, List.getElem?_eq_none_iff]; omega
      simp at habs
  | applyTransition k s sig accActs =>
    simp only [LinConfig.phase] at hphase
    -- k*(n+2) + n + 1 = r*(n+2) + p.val + 1, same sub_mul technique
    exfalso
    rcases le_or_gt k r with hkr | hkr
    · have heq : (r - k) * (n + 2) = n - p.val := by rw [Nat.sub_mul]; omega
      rcases Nat.eq_zero_or_pos (r - k) with h0 | h0
      · simp [h0] at heq; omega
      · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
    · have heq : (k - r) * (n + 2) = p.val - n := by rw [Nat.sub_mul]; omega
      rcases Nat.eq_zero_or_pos (k - r) with h0 | h0
      · omega
      · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
  | terminal s =>
    simp only [LinConfig.phase] at hphase
    -- G.rounds.length*(n+2) = r*(n+2) + p.val + 1, same technique as signal
    exfalso
    rcases le_or_gt r G.rounds.length with hrk | hrk
    · have heq : (G.rounds.length - r) * (n + 2) = p.val + 1 := by rw [Nat.sub_mul]; omega
      rcases Nat.eq_zero_or_pos (G.rounds.length - r) with h0 | h0
      · simp [h0] at heq
      · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
    · have : G.rounds.length * (n + 2) < r * (n + 2) :=
        (Nat.mul_lt_mul_right (by omega : 0 < n + 2)).mpr hrk
      omega

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- On a nonzero trace, if `linObserve G i ss[last] = some (kLast, vLast)`,
then for every r < kLast, there exists an internal position j (j+1 < ss.length)
with `linObserve G i ss[j] = some (r, v)` for some v. -/
private theorem earlier_i_step_exists
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (i : Fin n) (kLast : Fin G.rounds.length) (vLast : V)
    (hobsLast : linObserve G i (ss[ss.length - 1]'(by
      have := pureRun_length _ _ k pi ss hss; omega)) = some (kLast, vLast))
    (r : Nat) (hr : r < kLast.val) :
    ∃ (j : Nat) (hj : j + 1 < ss.length)
      (hr' : r < G.rounds.length) (v : V),
      linObserve G i (ss[j]'(by omega)) = some (⟨r, hr'⟩, v) := by
  have hlen := pureRun_length _ _ k pi ss hss
  have hlast_nd : ¬ (ss[ss.length - 1]'(by omega)).isDone G :=
    not_isDone_of_linObserve_some G _ i _ hobsLast
  have hr' : r < G.rounds.length := lt_trans hr kLast.isLt
  set target := r * (n + 2) + i.val + 1
  have hp_last := phase_of_linObserve_some G _ i kLast vLast hobsLast
  -- phase(ss[last]) = kLast.val * (n+2) + i.val + 1 = ss.length - 1
  have hlast_phase := phase_eq_index G pi k ss hss hlast_nd (ss.length - 1) (by omega)
  -- target < ss.length - 1
  have htarget_lt_last : target < ss.length - 1 := by
    rw [← hlast_phase, hp_last]
    change r * (n + 2) + i.val + 1 < kLast.val * (n + 2) + i.val + 1
    have : r * (n + 2) < kLast.val * (n + 2) :=
      (Nat.mul_lt_mul_right (by omega : 0 < n + 2)).mpr hr
    omega
  have htarget_lt : target < ss.length := by omega
  have hphase_target := phase_eq_index G pi k ss hss hlast_nd target htarget_lt
  obtain ⟨v, hobs⟩ := linObserve_of_phase_eq G (ss[target]'htarget_lt) i r hr' hphase_target
  exact ⟨target, by omega, hr', v, hobs⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- Two positions in a nonzero trace with the same `linObserve G i` returning
`some` at the same round must be at the same position and have the same view. -/
private theorem unique_i_step_position
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (i : Fin n) (kLast : Fin G.rounds.length) (vLast : V)
    (_hobsLast : linObserve G i (ss[ss.length - 1]'(by
      have := pureRun_length _ _ k pi ss hss; omega)) = some (kLast, vLast))
    (j1 j2 : Nat) (hj1 : j1 + 1 < ss.length) (hj2 : j2 + 1 < ss.length)
    (r : Fin G.rounds.length) (v1 v2 : V)
    (hobs1 : linObserve G i (ss[j1]'(by omega)) = some (r, v1))
    (hobs2 : linObserve G i (ss[j2]'(by omega)) = some (r, v2)) :
    j1 = j2 ∧ v1 = v2 := by
  have hp1 := phase_of_linObserve_some G _ i r v1 hobs1
  have hp2 := phase_of_linObserve_some G _ i r v2 hobs2
  have hj_eq : j1 = j2 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hnd2 : ¬ (ss[j2]'(by omega)).isDone G :=
        not_isDone_of_linObserve_some G _ i _ hobs2
      have := phase_strict_mono_of_not_done G pi k ss hss
        j1 j2 (by omega) (by omega) hlt hnd2
      omega
    · have hnd1 : ¬ (ss[j1]'(by omega)).isDone G :=
        not_isDone_of_linObserve_some G _ i _ hobs1
      have := phase_strict_mono_of_not_done G pi k ss hss
        j2 j1 (by omega) (by omega) hlt hnd1
      omega
  subst hj_eq
  have heq : (r, v1) = (r, v2) := Option.some_injective _ (hobs1.symm.trans hobs2)
  exact ⟨rfl, (Prod.mk.inj heq).2⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- Show r < kLast from phase arithmetic on a trace. -/
private theorem round_lt_of_earlier_step
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (i : Fin n) (kLast : Fin G.rounds.length) (vLast : V)
    (hobsLast : linObserve G i (ss[ss.length - 1]'(by
      have := pureRun_length _ _ k pi ss hss; omega)) = some (kLast, vLast))
    (j : Nat) (hj : j + 1 < ss.length) (r : Fin G.rounds.length) (v : V)
    (hobs : linObserve G i (ss[j]'(by omega)) = some (r, v)) :
    r.val < kLast.val := by
  have hlast : ss.length - 1 < ss.length := by
    have := pureRun_length _ _ k pi ss hss; omega
  have hndLast : ¬ (ss[ss.length - 1]'hlast).isDone G :=
    not_isDone_of_linObserve_some G _ i _ hobsLast
  have hlt : j < ss.length - 1 := by omega
  have hphase_lt := phase_strict_mono_of_not_done G pi k ss hss
    j (ss.length - 1) (by omega) hlast hlt hndLast
  have hp_j := phase_of_linObserve_some G _ i r v hobs
  have hp_last := phase_of_linObserve_some G _ i kLast vLast hobsLast
  rw [hp_j, hp_last] at hphase_lt
  by_contra h; push Not at h
  exact Nat.not_lt.mpr (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ h) _) _) hphase_lt

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **FullRecall bridge**: On nonzero traces with same last i-observation,
for each round r < kLast, the view at round r matches between the two traces
and the profile actions at that view agree. -/
private theorem fullRecall_view_action_match
    (hFR : G.FullRecall)
    (pi0 pi0' : (compiledLinObs G).PureProfile)
    (n1 n2 : Nat) (ss1 ss2 : List (LinConfig G))
    (h1 : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init n1 pi0 ss1 ≠ 0)
    (h2 : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init n2 pi0' ss2 ≠ 0)
    (i : Fin n) (kLast : Fin G.rounds.length) (vLast : V)
    (hobs1 : linObserve G i (ss1[ss1.length - 1]'(by
      have := pureRun_length _ _ n1 pi0 ss1 h1; omega)) = some (kLast, vLast))
    (hobs2 : linObserve G i (ss2[ss2.length - 1]'(by
      have := pureRun_length _ _ n2 pi0' ss2 h2; omega)) = some (kLast, vLast))
    (r : Nat) (hr : r < kLast.val) :
    ∃ (hr' : r < G.rounds.length)
      (j1 : Nat) (hj1 : j1 + 1 < ss1.length) (v : V),
      linObserve G i (ss1[j1]'(by omega)) = some (⟨r, hr'⟩, v) ∧
      ∃ (j2 : Nat) (hj2 : j2 + 1 < ss2.length),
        linObserve G i (ss2[j2]'(by omega)) = some (⟨r, hr'⟩, v) ∧
        ∀ (o : Option (RoundView G)),
          o = some (⟨r, hr'⟩, v) →
          (pi0 i) o = (pi0' i) o := by
  obtain ⟨j1, hj1, hr', v1, hobs_j1⟩ :=
    earlier_i_step_exists G pi0 n1 ss1 h1 i kLast vLast hobs1 r hr
  obtain ⟨j2, hj2, _, v2, hobs_j2⟩ :=
    earlier_i_step_exists G pi0' n2 ss2 h2 i kLast vLast hobs2 r hr
  obtain ⟨s1, sig1, acc1, hcfg1, hview1⟩ :=
    linObserve_some_playerTurn G _ i ⟨⟨r, hr'⟩, v1⟩ hobs_j1
  obtain ⟨s2, sig2, acc2, hcfg2, hview2⟩ :=
    linObserve_some_playerTurn G _ i ⟨⟨r, _⟩, v2⟩ hobs_j2
  obtain ⟨sL1, sigL1, accL1, hcfgL1, hviewL1⟩ :=
    linObserve_some_playerTurn G _ i ⟨kLast, vLast⟩ hobs1
  obtain ⟨sL2, sigL2, accL2, hcfgL2, hviewL2⟩ :=
    linObserve_some_playerTurn G _ i ⟨kLast, vLast⟩ hobs2
  -- Build ExecRecords with correct actions for player i
  let act1 : Option A := (pi0 i) (some (⟨r, hr'⟩, v1))
  let act2 : Option A := (pi0' i) (some (⟨r, hr'⟩, v2))
  let recs1 : Fin (kLast.val + 1) → ExecRecord n S A Sig := fun m =>
    if hm : m.val = kLast.val then
      ⟨⟨sL1, sigL1⟩, fun _ => none⟩
    else if hm : m.val = r then
      ⟨⟨s1, sig1⟩, Function.update (fun _ => none) i act1⟩
    else ⟨⟨s1, sig1⟩, fun _ => none⟩
  let recs2 : Fin (kLast.val + 1) → ExecRecord n S A Sig := fun m =>
    if hm : m.val = kLast.val then
      ⟨⟨sL2, sigL2⟩, fun _ => none⟩
    else if hm : m.val = r then
      ⟨⟨s2, sig2⟩, Function.update (fun _ => none) i act2⟩
    else ⟨⟨s2, sig2⟩, fun _ => none⟩
  -- Views at round kLast match
  have hview_kLast : G.rounds[kLast.val].playerView i
        (recs1 ⟨kLast.val, Nat.lt_succ_self _⟩).toRound =
      G.rounds[kLast.val].playerView i
        (recs2 ⟨kLast.val, Nat.lt_succ_self _⟩).toRound := by
    simp only [recs1, recs2, ↓reduceDIte]
    simp only [ExecRecord.toRound, Round.playerView]
    rw [hviewL1, hviewL2]
  -- Apply FullRecall
  have hfr := hFR i kLast.val kLast.isLt recs1 recs2 hview_kLast r hr
  obtain ⟨hview_match, haction_match⟩ := hfr
  have hr_ne : ¬(r = kLast.val) := by omega
  simp only [recs1, recs2, hr_ne, ↓reduceDIte] at hview_match haction_match
  simp only [ExecRecord.toRound, Round.playerView] at hview_match
  change G.rounds[r].view i s1 (sig1 i) = v1 at hview1
  change G.rounds[r].view i s2 (sig2 i) = v2 at hview2
  have hv_eq : v1 = v2 := by rw [← hview1, ← hview2]; exact hview_match
  subst hv_eq
  simp only [Function.update_self] at haction_match
  refine ⟨hr', j1, hj1, v1, hobs_j1, j2, hj2, ?_, ?_⟩
  · convert hobs_j2 using 2
  · intro o ho; subst ho; exact haction_match

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- projectStates for the compiled model equals the last observation. -/
theorem projectStates_eq_lastObs
    (i : Fin n) (ss : List (LinConfig G)) (hne : ss ≠ []) :
    (compiledLinObs G).projectStates i ss =
      linObserve G i (ss[ss.length - 1]'(by
        rcases ss with _ | ⟨_, _⟩ <;> simp_all)) := by
  have h := ObsModelCore.currentObs_projectStates (compiledLinObs G) i ss
  change id ((compiledLinObs G).projectStates i ss) =
    (compiledLinObs G).observe i ((compiledLinObs G).lastState ss) at h
  rw [id_eq] at h; rw [h]
  simp only [ObsModelCore.lastState]
  rcases ss with _ | ⟨hd, tl⟩
  · exact absurd rfl hne
  · have hne' : hd :: tl ≠ [] := by simp
    rw [List.getLast?_eq_getLast_of_ne_nil hne', Option.getD_some,
      List.getLast_eq_getElem]
    rfl

set_option linter.unusedSectionVars false in
/-- **ObsLocalFeasibility for the linearized model under FullRecall**:
if two traces have the same `projectStates` for player i, then updating
player i's strategy preserves reachability equivalently. -/
theorem obsLocalFeasibility_of_fullRecall
    (hFR : G.FullRecall) (i : Fin n) :
    ObsModelCore.ObsLocalFeasibility (compiledLinObs G) i := by
  intro n1 n2 pi0 pi0' ss1 ss2 hproj h1 h2 hns pii
  have hlen1 := pureRun_length _ _ n1 pi0 ss1 h1
  have hlen2 := pureRun_length _ _ n2 pi0' ss2 h2
  have hne1 : ss1 ≠ [] := by intro h; subst h; simp at hlen1
  have hne2 : ss2 ≠ [] := by intro h; subst h; simp at hlen2
  have hproj1 := projectStates_eq_lastObs G i ss1 hne1
  have hproj2 := projectStates_eq_lastObs G i ss2 hne2
  have hproj' : linObserve G i (ss1[ss1.length - 1]'(by omega)) =
      linObserve G i (ss2[ss2.length - 1]'(by omega)) := by
    rw [← hproj1, ← hproj2]; exact hproj
  match hobs_last1 : linObserve G i (ss1[ss1.length - 1]'(by omega)) with
  | none =>
    exfalso; apply hns
    have : (compiledLinObs G).currentObs i ((compiledLinObs G).projectStates i ss1) =
        (compiledLinObs G).projectStates i ss1 := rfl
    rw [this, hproj1, hobs_last1]
    exact inferInstanceAs (Subsingleton PUnit)
  | some ⟨kLast, vLast⟩ =>
    have hobs_last2 : linObserve G i (ss2[ss2.length - 1]'(by omega)) =
        some (kLast, vLast) := by rwa [← hproj']
    suffices key : ∀ (nA nB : Nat) (piA piB : (compiledLinObs G).PureProfile)
        (ssA ssB : List (LinConfig G))
        (hA : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init nA piA ssA ≠ 0)
        (hB : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init nB piB ssB ≠ 0)
        (hobsA : linObserve G i (ssA[ssA.length - 1]'(by
          have := pureRun_length _ _ nA piA ssA hA; omega)) = some (kLast, vLast))
        (hobsB : linObserve G i (ssB[ssB.length - 1]'(by
          have := pureRun_length _ _ nB piB ssB hB; omega)) = some (kLast, vLast))
        (hagree : ∀ j (hj : j + 1 < ssA.length),
          pii (linObserve G i (ssA[j]'(by omega))) =
            (piA i) (linObserve G i (ssA[j]'(by omega))))
        (j : Nat) (hj : j + 1 < ssB.length),
        pii (linObserve G i (ssB[j]'(by omega))) =
          (piB i) (linObserve G i (ssB[j]'(by omega))) by
      constructor
      · intro hup1
        have hagree1 : ∀ j (hj : j + 1 < ss1.length),
            pii (linObserve G i (ss1[j]'(by omega))) =
              (pi0 i) (linObserve G i (ss1[j]'(by omega))) :=
          fun j hj => pureRun_update_nonzero_agree G pi0 i pii n1 ss1 h1 hup1 j hj
        rw [pureRun_update_eq_of_obs_agree G pi0' i pii n2 ss2 h2
          (fun j hj => key n1 n2 pi0 pi0' ss1 ss2 h1 h2
            hobs_last1 hobs_last2 hagree1 j hj)]
        exact h2
      · intro hup2
        have hagree2 : ∀ j (hj : j + 1 < ss2.length),
            pii (linObserve G i (ss2[j]'(by omega))) =
              (pi0' i) (linObserve G i (ss2[j]'(by omega))) :=
          fun j hj => pureRun_update_nonzero_agree G pi0' i pii n2 ss2 h2 hup2 j hj
        rw [pureRun_update_eq_of_obs_agree G pi0 i pii n1 ss1 h1
          (fun j hj => key n2 n1 pi0' pi0 ss2 ss1 h2 h1
            hobs_last2 hobs_last1 hagree2 j hj)]
        exact h1
    -- Prove the key lemma
    intro nA nB piA piB ssA ssB hA hB hobsA hobsB hagree j hj
    match hobs : linObserve G i (ssB[j]'(by omega)) with
    | none => exact PUnit.ext _ _
    | some ⟨⟨r, hr⟩, v⟩ =>
      have hr_lt : r < kLast.val :=
        round_lt_of_earlier_step G piB nB ssB hB i kLast vLast hobsB j hj ⟨r, hr⟩ v hobs
      obtain ⟨hr', jA, hjA, v_match, hobsA_j, jB, hjB, hobsB_j, hact_eq⟩ :=
        fullRecall_view_action_match G hFR piA piB nA nB ssA ssB hA hB i kLast vLast
          hobsA hobsB r hr_lt
      have ⟨hjBeq, hveq⟩ := unique_i_step_position G piB nB ssB hB i kLast vLast hobsB
        jB j hjB hj ⟨r, hr'⟩ v_match v hobsB_j
        (by convert hobs using 2)
      subst hjBeq; subst hveq
      have hfin_eq : (⟨r, hr⟩ : Fin G.rounds.length) = ⟨r, hr'⟩ := Fin.ext rfl
      have h1' := hagree jA hjA
      rw [hobsA_j] at h1'
      have h2' := hact_eq (some (⟨r, hr'⟩, v_match)) rfl
      rw [show (some (⟨r, hr⟩, v_match) : Option (RoundView G)) =
        some (⟨r, hr'⟩, v_match) from by rw [hfin_eq]]
      rw [h1', h2']

/-- The linearized compiled model satisfies `NoNontrivialInfoStateRepeat`
unconditionally: along any reachable trace, no observation `some (k, v)`
appears at two distinct positions. This follows from the strict monotonicity
of the phase function along non-done traces. -/
theorem noNontrivialInfoStateRepeat_compiledLin :
    (compiledLinObs G).NoNontrivialInfoStateRepeat := by
  intro i π k ss hss j₁ j₂ hlt hj₂ hproj
  rw [ObsModelCore.runDistPure_eq_pureRun] at hss
  have hlen := pureRun_length _ _ k π ss hss
  -- For identity info state, projectStates (take) = linObserve at last element
  have hne₁ : ss.take (j₁ + 1) ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  have hne₂ : ss.take (j₂ + 1) ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  have hobs_eq₁ := projectStates_eq_lastObs G i (ss.take (j₁ + 1)) hne₁
  have hobs_eq₂ := projectStates_eq_lastObs G i (ss.take (j₂ + 1)) hne₂
  -- Simplify: last element of take (j+1) ss is ss[j]
  have htake_last₁ : (ss.take (j₁ + 1))[(ss.take (j₁ + 1)).length - 1]'(by
      simp; omega) = ss[j₁]'(by omega) := by
    have : (ss.take (j₁ + 1)).length - 1 = j₁ := by simp; omega
    simp only [this]; exact List.getElem_take
  have htake_last₂ : (ss.take (j₂ + 1))[(ss.take (j₂ + 1)).length - 1]'(by
      simp; omega) = ss[j₂]'(by omega) := by
    have : (ss.take (j₂ + 1)).length - 1 = j₂ := by simp; omega
    simp only [this]; exact List.getElem_take
  rw [htake_last₁] at hobs_eq₁
  rw [htake_last₂] at hobs_eq₂
  -- Now: projectStates i (take (j+1) ss) = linObserve G i ss[j]
  -- hproj gives equal projectStates → equal observations
  have hobseq : linObserve G i (ss[j₁]'(by omega)) =
      linObserve G i (ss[j₂]'(by omega)) := by
    rw [← hobs_eq₁, ← hobs_eq₂]; exact hproj
  -- The goal is about Act at currentObs (projectStates (take (j₂+1) ss))
  -- For identity: currentObs = id, so this is projectStates = linObserve at j₂
  -- For identity info state: currentObs = id, so goal reduces to
  -- Subsingleton (LinAct _ A (projectStates i (take (j₂+1) ss)))
  -- which equals linObserve G i ss[j₂] by hobs_eq₂
  change Subsingleton (LinAct (RoundView G) A
    ((compiledLinObs G).projectStates i (ss.take (j₂ + 1))))
  rw [hobs_eq₂]
  cases hobs₂ : linObserve G i (ss[j₂]'(by omega)) with
  | none => exact inferInstanceAs (Subsingleton PUnit)
  | some rv =>
    obtain ⟨r, v⟩ := rv
    rw [hobs₂] at hobseq
    have hp₁ := phase_of_linObserve_some G _ i r v hobseq
    have hp₂ := phase_of_linObserve_some G _ i r v hobs₂
    have hnd₂ := not_isDone_of_linObserve_some G _ i _ hobs₂
    have hphase_lt := phase_strict_mono_of_not_done G π k ss hss
      j₁ j₂ (by omega) (by omega) hlt hnd₂
    omega

end OLFBridge

-- ============================================================================
-- VRD agreement: lift ∘ descendVRD agrees with β at reachable observations
-- ============================================================================

section VRDAgreement

variable {G : Protocol n S V A Sig} [DecidableEq (Fin n)] [Fintype (Fin n)]
variable [Fintype A] [Nonempty A] [Nonempty (Fin G.rounds.length)]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- Under `ViewDeterminesRound`, the lifted VRD-descended profile agrees with `β` at all
info states visited during `runDist`. This provides the hypothesis for `runDist_congr`. -/
theorem liftBehavioralProfile_descendVRD_agree
    (hVRD : G.ViewDeterminesRound)
    (β : ObsModelCore.BehavioralProfile (compiledLinObs G))
    (m : Nat) (i : Fin n) (ss : List (LinConfig G))
    (_hss : ((compiledLinObs G).runDist m β) ss ≠ 0) :
    β i ((compiledLinObs G).projectStates i ss) =
      (liftBehavioralProfile (G := G) (descendBehavioralProfileVRD hVRD β)) i
        ((compiledLinObs G).projectStates i ss) := by
  -- For identity info states, projectStates i ss = observe i (lastState ss)
  set obs := (compiledLinObs G).projectStates i ss
  -- The key insight: projectStates is linObserve at the last state
  have hps : obs = linObserve G i ((compiledLinObs G).lastState ss) := by
    have h := ObsModelCore.currentObs_projectStates (compiledLinObs G) i ss
    simp only [ObsModelCore.currentObs, compileObsCoreModelLin] at h
    exact h
  cases hobs : obs with
  | none =>
    -- Both sides are PMF over PUnit (subsingleton action type at none)
    change β i none = liftBehavioralStrategy (descendBehavioralProfileVRD hVRD β i) none
    simp only [liftBehavioralStrategy]
    -- Goal: β i none = PMF.pure PUnit.unit
    ext ⟨⟩
    have h : ∑' (a : PUnit), (β i none) a = 1 := (β i none).tsum_coe
    rw [tsum_eq_single PUnit.unit
      (fun x hx => absurd (Subsingleton.elim x PUnit.unit) hx)] at h
    rw [h]
    exact (PMF.pure_apply_self _).symm
  | some rv =>
    obtain ⟨k, v⟩ := rv
    -- linObserve at lastState = some (k, v)
    rw [hobs] at hps
    obtain ⟨s, sig, _, _, hview⟩ := linObserve_some_playerTurn G _ i (k, v) hps.symm
    -- viewRound hVRD i v = k by ViewDeterminesRound
    have hvr : viewRound hVRD i v = k :=
      viewRound_eq hVRD k s (sig i) i hview
    -- Both sides now reduce to β i (some (k, v))
    change β i (some (k, v)) =
      liftBehavioralStrategy (descendBehavioralProfileVRD hVRD β i) (some (k, v))
    simp only [liftBehavioralStrategy, descendBehavioralProfileVRD]
    rw [hvr]

end VRDAgreement

-- ============================================================================
-- Pure profile VRD descent (for B→M)
-- ============================================================================

section PureVRDDescent

variable [DecidableEq (Fin n)] [Fintype (Fin n)]
variable [Fintype A] [Nonempty A]
variable {G : Protocol n S V A Sig}

/-- Descend a compiled local strategy using `ViewDeterminesRound`: picks the
canonical round for each view via `viewRound`. -/
noncomputable def descendLocalStrategyVRD [Nonempty (Fin G.rounds.length)]
    (hVRD : G.ViewDeterminesRound)
    (π : (compiledLinObs G).LocalStrategy (i := i)) :
    PureStrategy V A :=
  fun v => π (some (viewRound hVRD i v, v))

/-- Descend a compiled pure profile using `ViewDeterminesRound`. -/
noncomputable def descendPureProfileVRD [Nonempty (Fin G.rounds.length)]
    (hVRD : G.ViewDeterminesRound)
    (π : (compiledLinObs G).PureProfile) :
    PureProfile n V A :=
  fun i => descendLocalStrategyVRD hVRD (π i)

/-- `liftPureProfile (descendPureProfileVRD hVRD π)` agrees with `π` at all
reachable info states under `pureToBehavioral`. -/
theorem liftPureProfile_descendVRD_agree
    [Nonempty (Fin G.rounds.length)]
    (hVRD : G.ViewDeterminesRound)
    (π : (compiledLinObs G).PureProfile)
    (m : Nat) (i : Fin n) (ss : List (LinConfig G))
    (_hss : ((compiledLinObs G).runDist m
      ((compiledLinObs G).pureToBehavioral π)) ss ≠ 0) :
    ((compiledLinObs G).pureToBehavioral π) i
      ((compiledLinObs G).projectStates i ss) =
    ((compiledLinObs G).pureToBehavioral
      (liftPureProfile (G := G) (descendPureProfileVRD hVRD π))) i
      ((compiledLinObs G).projectStates i ss) := by
  set obs := (compiledLinObs G).projectStates i ss
  cases hobs : obs with
  | none =>
    simp [ObsModelCore.pureToBehavioral]
    rfl
  | some rv =>
    obtain ⟨k, v⟩ := rv
    have hps : obs = linObserve G i ((compiledLinObs G).lastState ss) := by
      have h := ObsModelCore.currentObs_projectStates (compiledLinObs G) i ss
      simp only [ObsModelCore.currentObs, compileObsCoreModelLin] at h
      exact h
    rw [hobs] at hps
    obtain ⟨s, sig, _, _, hview⟩ := linObserve_some_playerTurn G _ i (k, v) hps.symm
    have hvr : viewRound hVRD i v = k := viewRound_eq hVRD k s (sig i) i hview
    simp only [ObsModelCore.pureToBehavioral]
    congr 1
    change π i (some (k, v)) =
      liftLocalStrategy (descendLocalStrategyVRD hVRD (π i)) (some (k, v))
    simp only [liftLocalStrategy, descendLocalStrategyVRD]; rw [hvr]

end PureVRDDescent

end GameTheory.Sequential
