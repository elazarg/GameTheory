module

/-
# Envelope and payment identities for single-parameter mechanisms

Canonical dominant-strategy truthfulness determines each payment slice up to
its charge at one report. Allocation quantities may be signed and unbounded;
monotonicity supplies the local integrability needed on each finite interval.
-/

public import GameTheory.Mechanism.SingleParameter
public import GameTheory.Math.Envelope
public import GameTheory.Math.Probability.TailIntegral
public import GameTheory.Math.Probability.Measure

@[expose] public section

noncomputable section

namespace GameTheory.Mechanism.SingleParameterMechanism

open MeasureTheory

variable {Player : Type*} [DecidableEq Player]
variable (M : SingleParameterMechanism Player)

/-- Report optimality throughout an interval gives supporting slopes there.
This condition also constrains types of zero prior probability. -/
theorem supporting_slopes_on (who : Player) (reports : SingleParameterReportProfile Player)
    {a b : ℝ}
    (hIC : ∀ t ∈ Set.Icc a b,
      IsMaxOn (fun r => M.utility (Profile.update reports who r) who t) (Set.Icc a b) t) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      (x - y) * OwnAllocation M.allocation who reports y ≤
        M.utility (Profile.update reports who x) who x -
          M.utility (Profile.update reports who y) who y := by
  intro x hx y hy
  have hic : M.utility (Profile.update reports who y) who x ≤
      M.utility (Profile.update reports who x) who x := hIC x hx hy
  dsimp only [utility, OwnAllocation] at hic ⊢
  nlinarith

/-- Interval-wide report optimality determines the payment at every type in
the interval from the lowest-type utility. No prior-support premise is used. -/
theorem payment_identity_on (who : Player) (reports : SingleParameterReportProfile Player)
    {a b : ℝ}
    (hIC : ∀ t ∈ Set.Icc a b,
      IsMaxOn (fun r => M.utility (Profile.update reports who r) who t) (Set.Icc a b) t)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    M.payment (Profile.update reports who t) who =
      t * OwnAllocation M.allocation who reports t -
        M.utility (Profile.update reports who a) who a -
        ∫ s in a..t, OwnAllocation M.allocation who reports s := by
  have hs := M.supporting_slopes_on who reports hIC
  have hi := Math.integral_eq_sub_of_supporting_slopesOn ht.1
    (fun x hx y hy => hs x ⟨hx.1, hx.2.trans ht.2⟩ y ⟨hy.1, hy.2.trans ht.2⟩)
  dsimp only [utility, OwnAllocation] at hi ⊢
  linarith

/-- Equal allocation on the type interval and equal lowest-type utility
determine all payments on that interval. -/
theorem payment_unique_on {N : SingleParameterMechanism Player}
    (who : Player) (reports : SingleParameterReportProfile Player) {a b : ℝ}
    (hM : ∀ t ∈ Set.Icc a b,
      IsMaxOn (fun r => M.utility (Profile.update reports who r) who t) (Set.Icc a b) t)
    (hN : ∀ t ∈ Set.Icc a b,
      IsMaxOn (fun r => N.utility (Profile.update reports who r) who t) (Set.Icc a b) t)
    (hq : ∀ t ∈ Set.Icc a b,
      OwnAllocation M.allocation who reports t = OwnAllocation N.allocation who reports t)
    (hbase : M.utility (Profile.update reports who a) who a =
      N.utility (Profile.update reports who a) who a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    M.payment (Profile.update reports who t) who =
      N.payment (Profile.update reports who t) who := by
  rw [M.payment_identity_on who reports hM ht, N.payment_identity_on who reports hN ht,
    hq t ht, hbase]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht.1] at hs
  exact hq s ⟨hs.1, hs.2.trans ht.2⟩

/-- Truthful utility is a baseline utility plus the integral of the allocation
at fixed opponents' reports. -/
theorem utility_eq_add_integral (hdsic : M.IsDSIC) (who : Player)
    (reports : SingleParameterReportProfile Player) (a t : ℝ) :
    M.utility (Profile.update reports who t) who t =
      M.utility (Profile.update reports who a) who a +
        ∫ s in a..t, OwnAllocation M.allocation who reports s := by
  have hs : ∀ x y, (x - y) * OwnAllocation M.allocation who reports y ≤
      M.utility (Profile.update reports who x) who x -
        M.utility (Profile.update reports who y) who y := by
    intro x y
    have hic := (M.isDSIC_iff.mp hdsic) who (Profile.update reports who x) y
    simp only [utility, Profile.update_same, Profile.update_idem, OwnAllocation] at hic ⊢
    nlinarith
  have hint := Math.integral_eq_sub_of_supporting_slopes hs a t
  linarith

/-- The DSIC payment identity at an arbitrary baseline report. -/
theorem payment_identity (hdsic : M.IsDSIC) (who : Player)
    (reports : SingleParameterReportProfile Player) (a t : ℝ) :
    M.payment (Profile.update reports who t) who =
      M.payment (Profile.update reports who a) who +
        t * OwnAllocation M.allocation who reports t -
        a * OwnAllocation M.allocation who reports a -
        ∫ s in a..t, OwnAllocation M.allocation who reports s := by
  have h := M.utility_eq_add_integral hdsic who reports a t
  dsimp only [utility, OwnAllocation] at h ⊢
  linarith

/-- Equal allocations and equal baseline charges determine equal DSIC payments
at the supplied report profile. -/
theorem payment_unique (hdsic : M.IsDSIC) {N : SingleParameterMechanism Player}
    (hN : N.IsDSIC) (halloc : M.allocation = N.allocation) (who : Player)
    (reports : SingleParameterReportProfile Player) (a : ℝ)
    (hbase : M.payment (Profile.update reports who a) who =
      N.payment (Profile.update reports who a) who) :
    M.payment reports who = N.payment reports who := by
  have hM := M.payment_identity hdsic who reports a (reports who)
  have hN := N.payment_identity hN who reports a (reports who)
  rw [halloc, hbase] at hM
  simpa only [Profile.update_eq_self] using hM.trans hN.symm

private theorem rectangle_le_integral {q : ℝ → ℝ} (hq : Monotone q) (a b : ℝ) :
    (b - a) * q a ≤ ∫ s in a..b, q s := by
  rcases le_total a b with hab | hba
  · simpa only [intervalIntegral.integral_const, smul_eq_mul] using
      intervalIntegral.integral_mono_on hab (μ := volume)
        intervalIntegrable_const hq.intervalIntegrable
        (fun s hs => hq hs.1)
  · have hi := intervalIntegral.integral_mono_on hba (μ := volume) hq.intervalIntegrable
      (intervalIntegrable_const (c := q a)) (fun s hs => hq hs.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hi
    rw [intervalIntegral.integral_symm]
    linarith

/-- Monotonicity and the normalized payment formula characterize canonical
DSIC, including every real report deviation. -/
theorem isDSIC_iff_monotone_payment_identity :
    M.IsDSIC ↔ M.IsMonotone ∧ ∀ who reports t,
      M.payment (Profile.update reports who t) who =
        M.payment (Profile.update reports who 0) who +
          t * OwnAllocation M.allocation who reports t -
          ∫ s in 0..t, OwnAllocation M.allocation who reports s := by
  constructor
  · intro h
    refine ⟨M.isMonotone_of_isDSIC h, ?_⟩
    intro who reports t
    simpa only [zero_mul, sub_zero] using M.payment_identity h who reports 0 t
  · rintro ⟨hmono, hp⟩
    rw [M.isDSIC_iff]
    intro who reports r
    have hq := M.ownAllocation_monotone hmono who reports
    have htrue := hp who reports (reports who)
    have hreport := hp who reports r
    simp only [Profile.update_eq_self] at htrue
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hq.intervalIntegrable (μ := volume) (a := 0) (b := r))
      (hq.intervalIntegrable (a := r) (b := reports who))
    have hbound := rectangle_le_integral hq r (reports who)
    dsimp only [utility]
    dsimp only [OwnAllocation] at htrue hreport hbound hadd
    simp only [Profile.update_eq_self] at htrue
    nlinarith

/-- A real allocation is DSIC implementable exactly when it is monotone in
each player's own report. The witness uses the existing mechanism constructor. -/
theorem isImplementable_iff {allocation : SingleParameterReportProfile Player → Player → ℝ} :
    IsImplementable allocation ↔ AllocationIsMonotone allocation := by
  refine ⟨allocationIsMonotone_of_isImplementable, ?_⟩
  intro hmono
  let payment := fun (reports : SingleParameterReportProfile Player) who =>
    reports who * allocation reports who -
    ∫ s in 0..reports who, OwnAllocation allocation who reports s
  refine ⟨payment, (isDSIC_iff_monotone_payment_identity
    (SingleParameterMechanism.mk allocation payment)).mpr ⟨hmono, ?_⟩⟩
  intro who reports t
  simp only [payment, OwnAllocation, Profile.update_same, Profile.update_idem,
    zero_mul, intervalIntegral.integral_same, sub_self, zero_add]

private theorem integrable_value_allocation (hmono : M.IsMonotone)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (who : Player)
    (reports : SingleParameterReportProfile Player) {a b : ℝ}
    (hsupport : ∀ᵐ t ∂μ, t ∈ Set.Icc a b) :
    Integrable (fun t => t * OwnAllocation M.allocation who reports t) μ := by
  have hq : IntegrableOn (OwnAllocation M.allocation who reports) (Set.Icc a b) μ :=
    MonotoneOn.integrableOn_isCompact isCompact_Icc
      ((M.ownAllocation_monotone hmono who reports).monotoneOn _)
  have hi := hq.continuousOn_mul continuous_id.continuousOn isCompact_Icc
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hsupport] at hi

/-- Bounded type support makes the actual payment slice integrable. Allocation
monotonicity supplies all local bounds; no bounded global allocation is needed. -/
theorem integrable_payment (hdsic : M.IsDSIC) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (who : Player) (reports : SingleParameterReportProfile Player) {a b : ℝ}
    (hsupport : ∀ᵐ t ∂μ, t ∈ Set.Icc a b) :
    Integrable (fun t => M.payment (Profile.update reports who t) who) μ := by
  have hq := M.ownAllocation_monotone (M.isMonotone_of_isDSIC hdsic) who reports
  have hvalue := M.integrable_value_allocation (M.isMonotone_of_isDSIC hdsic)
    μ who reports hsupport
  have hcum := Math.Probability.integrable_intervalIntegral μ hq.intervalIntegrable hsupport
  exact (((integrable_const (M.payment (Profile.update reports who a) who)).add hvalue).sub
    (integrable_const (a * OwnAllocation M.allocation who reports a))).sub hcum
      |>.congr (Filter.Eventually.of_forall fun t =>
        (M.payment_identity hdsic who reports a t).symm)

/-- Expected payment is the baseline charge plus expected allocated value,
minus the baseline allocated value and the tail-weighted allocation integral.
Atoms and signed allocation quantities are permitted. -/
theorem integral_payment_eq (hdsic : M.IsDSIC) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (who : Player) (reports : SingleParameterReportProfile Player) {a b : ℝ}
    (hab : a ≤ b) (hsupport : ∀ᵐ t ∂μ, t ∈ Set.Icc a b) :
    (∫ t, M.payment (Profile.update reports who t) who ∂μ) =
      M.payment (Profile.update reports who a) who +
        (∫ t, t * OwnAllocation M.allocation who reports t ∂μ) -
        a * OwnAllocation M.allocation who reports a -
        ∫ s in a..b, OwnAllocation M.allocation who reports s *
          (μ (Set.Ici s)).toReal := by
  have hq := M.ownAllocation_monotone (M.isMonotone_of_isDSIC hdsic) who reports
  have hvalue := M.integrable_value_allocation (M.isMonotone_of_isDSIC hdsic)
    μ who reports hsupport
  have hcum := Math.Probability.integrable_intervalIntegral μ hq.intervalIntegrable hsupport
  have hp : (fun t => M.payment (Profile.update reports who t) who) =
      (fun t => M.payment (Profile.update reports who a) who +
        t * OwnAllocation M.allocation who reports t -
        a * OwnAllocation M.allocation who reports a -
        ∫ s in a..t, OwnAllocation M.allocation who reports s) :=
    funext (M.payment_identity hdsic who reports a)
  rw [hp]
  calc
    _ = (∫ t, M.payment (Profile.update reports who a) who +
        t * OwnAllocation M.allocation who reports t -
        a * OwnAllocation M.allocation who reports a ∂μ) -
        ∫ t, (∫ s in a..t, OwnAllocation M.allocation who reports s) ∂μ :=
      integral_sub (((integrable_const _).add hvalue).sub (integrable_const _)) hcum
    _ = _ := by
      have hs : (∫ t, M.payment (Profile.update reports who a) who +
          t * OwnAllocation M.allocation who reports t ∂μ) =
          M.payment (Profile.update reports who a) who +
            ∫ t, t * OwnAllocation M.allocation who reports t ∂μ :=
        (integral_add (integrable_const _) hvalue).trans (by simp)
      have hd : (∫ t, M.payment (Profile.update reports who a) who +
          t * OwnAllocation M.allocation who reports t -
          a * OwnAllocation M.allocation who reports a ∂μ) =
          M.payment (Profile.update reports who a) who +
            (∫ t, t * OwnAllocation M.allocation who reports t ∂μ) -
            a * OwnAllocation M.allocation who reports a :=
        (integral_sub ((integrable_const _).add hvalue) (integrable_const _)).trans
          (by simp only [Pi.add_apply]; rw [hs]; simp)
      rw [hd, Math.Probability.integral_intervalIntegral_eq_integral_mul_tail μ hab
        hq.intervalIntegrable hsupport]

/-- The same expected-payment identity for the canonical discrete law and
expectation. Bounded support need not be finite. -/
theorem expected_payment_eq (hdsic : M.IsDSIC) (μ : PMF ℝ) (who : Player)
    (reports : SingleParameterReportProfile Player) {a b : ℝ} (hab : a ≤ b)
    (hsupport : μ.support ⊆ Set.Icc a b) :
    Math.Probability.expect μ (fun t => M.payment (Profile.update reports who t) who) =
      M.payment (Profile.update reports who a) who +
        Math.Probability.expect μ (fun t => t * OwnAllocation M.allocation who reports t) -
        a * OwnAllocation M.allocation who reports a -
        ∫ s in a..b, OwnAllocation M.allocation who reports s *
          (μ.toMeasure (Set.Ici s)).toReal := by
  have hs : ∀ᵐ t ∂μ.toMeasure, t ∈ Set.Icc a b :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr
      ((μ.toMeasure_apply_eq_one_iff measurableSet_Icc).mpr hsupport)
  simpa only [Math.Probability.expect_eq_integral] using
    M.integral_payment_eq hdsic μ.toMeasure who reports hab hs

end GameTheory.Mechanism.SingleParameterMechanism
