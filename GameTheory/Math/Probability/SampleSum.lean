/-
# Sums of independent draws

`addLaw μ ν` is the law of `X + Y` for independent `X ∼ μ` and `Y ∼ ν`, and
`sampleSum μ m` is the law of the sum of `m` independent draws from `μ`.
Comparing empirical means of equally many draws is comparing these sums, so
this is the carrier of every sample-mean statistic.

Beyond the convolution algebra, the file bounds the support of a sum and
computes its second central moment, which yields Chebyshev's inequality for
the sum of draws from a law of bounded support.
-/
import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.ExpectationBind

noncomputable section

namespace GameTheory.Math.Probability

/-- The law of `X + Y` for independent `X ∼ μ` and `Y ∼ ν`. -/
def addLaw (μ ν : PMF ℝ) : PMF ℝ :=
  μ.bind fun a => ν.map (a + ·)

/-- The law of the sum of `m` independent draws from `μ`. -/
def sampleSum (μ : PMF ℝ) : ℕ → PMF ℝ
  | 0 => PMF.pure 0
  | m + 1 => addLaw (sampleSum μ m) μ

@[simp]
theorem sampleSum_zero (μ : PMF ℝ) : sampleSum μ 0 = PMF.pure 0 := rfl

theorem sampleSum_succ (μ : PMF ℝ) (m : ℕ) :
    sampleSum μ (m + 1) = addLaw (sampleSum μ m) μ := rfl

theorem addLaw_eq_bind_bind (μ ν : PMF ℝ) :
    addLaw μ ν = μ.bind fun a => ν.bind fun b => PMF.pure (a + b) := by
  simp only [addLaw, PMF.map, Function.comp_def]

theorem addLaw_comm (μ ν : PMF ℝ) : addLaw μ ν = addLaw ν μ := by
  rw [addLaw_eq_bind_bind, addLaw_eq_bind_bind, PMF.bind_comm]
  simp only [add_comm]

theorem addLaw_assoc (μ ν ρ : PMF ℝ) :
    addLaw (addLaw μ ν) ρ = addLaw μ (addLaw ν ρ) := by
  simp only [addLaw_eq_bind_bind, PMF.bind_bind, PMF.pure_bind, add_assoc]

@[simp]
theorem addLaw_pure_zero (μ : PMF ℝ) : addLaw (PMF.pure 0) μ = μ := by
  simp only [addLaw, PMF.pure_bind, zero_add]
  exact PMF.map_id μ

@[simp]
theorem addLaw_pure_zero_right (μ : PMF ℝ) : addLaw μ (PMF.pure 0) = μ := by
  rw [addLaw_comm, addLaw_pure_zero]

/-- Draws may be split into two independent batches. -/
theorem sampleSum_add (μ : PMF ℝ) (m n : ℕ) :
    sampleSum μ (m + n) = addLaw (sampleSum μ m) (sampleSum μ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, sampleSum_succ, ih, sampleSum_succ, addLaw_assoc]

/-- The sum of paired draws is the sum of the two separate sums. -/
theorem sampleSum_addLaw (μ ν : PMF ℝ) (m : ℕ) :
    sampleSum (addLaw μ ν) m = addLaw (sampleSum μ m) (sampleSum ν m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sampleSum_succ, ih, sampleSum_succ, sampleSum_succ, addLaw_assoc,
      addLaw_assoc]
    congr 1
    rw [← addLaw_assoc, addLaw_comm (sampleSum ν m) μ, addLaw_assoc]

/-- An additive map of the summands maps their sum. -/
theorem addLaw_map_of_map_add {g : ℝ → ℝ} (hg : ∀ a b, g (a + b) = g a + g b)
    (μ ν : PMF ℝ) : addLaw (μ.map g) (ν.map g) = (addLaw μ ν).map g := by
  simp only [addLaw_eq_bind_bind, PMF.map, Function.comp_def, PMF.bind_bind,
    PMF.pure_bind, hg]

/-- An additive map of the draws maps the sum of the draws. -/
theorem sampleSum_map_of_map_add {g : ℝ → ℝ} (hg : ∀ a b, g (a + b) = g a + g b)
    (hg0 : g 0 = 0) (μ : PMF ℝ) (m : ℕ) :
    sampleSum (μ.map g) m = (sampleSum μ m).map g := by
  induction m with
  | zero => simp [PMF.pure_map, hg0]
  | succ m ih => rw [sampleSum_succ, ih, addLaw_map_of_map_add hg, sampleSum_succ]

theorem addLaw_map_neg (μ ν : PMF ℝ) :
    addLaw (μ.map Neg.neg) (ν.map Neg.neg) = (addLaw μ ν).map Neg.neg :=
  addLaw_map_of_map_add neg_add μ ν

theorem sampleSum_map_neg (μ : PMF ℝ) (m : ℕ) :
    sampleSum (μ.map Neg.neg) m = (sampleSum μ m).map Neg.neg :=
  sampleSum_map_of_map_add neg_add neg_zero μ m

theorem sampleSum_map_mul (c : ℝ) (μ : PMF ℝ) (m : ℕ) :
    sampleSum (μ.map (c * ·)) m = (sampleSum μ m).map (c * ·) :=
  sampleSum_map_of_map_add (fun a b => mul_add c a b) (mul_zero c) μ m

theorem mem_support_addLaw {μ ν : PMF ℝ} {x : ℝ} :
    x ∈ (addLaw μ ν).support ↔
      ∃ a ∈ μ.support, ∃ b ∈ ν.support, a + b = x := by
  rw [addLaw, PMF.mem_support_bind_iff]
  simp only [PMF.mem_support_map_iff]


/-- A sum of `m` draws of magnitude at most `R` has magnitude at most `m * R`. -/
theorem abs_le_of_mem_support_sampleSum {μ : PMF ℝ} {R : ℝ}
    (hbound : ∀ x ∈ μ.support, |x| ≤ R) (m : ℕ) :
    ∀ s ∈ (sampleSum μ m).support, |s| ≤ m * R := by
  induction m with
  | zero =>
    intro s hs
    rw [sampleSum_zero, PMF.mem_support_pure_iff] at hs
    simp [hs]
  | succ m ih =>
    intro s hs
    rw [sampleSum_succ, mem_support_addLaw] at hs
    obtain ⟨a, ha, b, hb, rfl⟩ := hs
    calc
      |a + b| ≤ |a| + |b| := abs_add_le a b
      _ ≤ m * R + R := add_le_add (ih a ha) (hbound b hb)
      _ = ((m + 1 : ℕ) : ℝ) * R := by push_cast; ring

/-- Sums of nonnegative draws are nonnegative. -/
theorem nonneg_of_mem_support_sampleSum {μ : PMF ℝ} (hμ : ∀ x ∈ μ.support, 0 ≤ x) (m : ℕ) :
    ∀ s ∈ (sampleSum μ m).support, 0 ≤ s := by
  induction m with
  | zero =>
    intro s hs
    rw [sampleSum_zero, PMF.mem_support_pure_iff] at hs
    exact hs.ge
  | succ m ih =>
    intro s hs
    rw [sampleSum_succ, mem_support_addLaw] at hs
    obtain ⟨a, ha, b, hb, rfl⟩ := hs
    exact add_nonneg (ih a ha) (hμ b hb)

/-- The tower law for an independent sum. -/
theorem expect_addLaw (μ ν : PMF ℝ) (f : ℝ → ℝ)
    (hf : PayoffIntegrable (addLaw μ ν) f) :
    expect (addLaw μ ν) f = expect μ (fun a => expect ν (fun b => f (a + b))) := by
  rw [addLaw] at hf ⊢
  rw [expect_bind_tower μ _ f hf]
  apply expect_congr_on_support
  intro a _
  rw [expect_map]
  rfl

/-- A function bounded on an interval containing the support is integrable. -/
theorem payoffIntegrable_of_support_abs_le {μ : PMF ℝ} {R C : ℝ}
    (hbound : ∀ x ∈ μ.support, |x| ≤ R) (f : ℝ → ℝ)
    (hf : ∀ x, |x| ≤ R → |f x| ≤ C) : PayoffIntegrable μ f :=
  payoffIntegrable_of_bounded_on_support μ f fun x hx => hf x (hbound x hx)

section SecondMoment

variable {μ : PMF ℝ} {R : ℝ}

/-- The mean of a law on the reals. -/
abbrev lawMean (μ : PMF ℝ) : ℝ := expect μ id

/-- The variance of a law on the reals. -/
abbrev lawVariance (μ : PMF ℝ) : ℝ := expect μ fun x => (x - lawMean μ) ^ 2

private theorem abs_sq_sub_le {x R e : ℝ} (hx : |x| ≤ R) :
    |(x - e) ^ 2| ≤ (R + |e|) ^ 2 := by
  rw [abs_pow]
  have h : |x - e| ≤ R + |e| := (abs_sub x e).trans (add_le_add hx le_rfl)
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

theorem expect_sub_lawMean (hbound : ∀ x ∈ μ.support, |x| ≤ R) :
    expect μ (fun x => x - lawMean μ) = 0 := by
  have hid : PayoffIntegrable μ id :=
    payoffIntegrable_of_support_abs_le hbound id (C := R) fun x hx => hx
  change expect μ (fun x => id x - lawMean μ) = 0
  rw [expect_sub hid (payoffIntegrable_constant μ _), expect_constant]
  simp

/-- The second central moment of a sum of independent draws is additive. -/
theorem expect_sampleSum_centered_sq (hbound : ∀ x ∈ μ.support, |x| ≤ R) (m : ℕ) :
    expect (sampleSum μ m) (fun s => (s - m * lawMean μ) ^ 2) =
      m * lawVariance μ := by
  set e := lawMean μ
  set v := lawVariance μ
  induction m with
  | zero => simp [expect_pure]
  | succ m ih =>
    have hsum := abs_le_of_mem_support_sampleSum hbound (m + 1)
    rw [sampleSum_succ] at hsum ⊢
    have hint : PayoffIntegrable (addLaw (sampleSum μ m) μ)
        (fun s => (s - ((m + 1 : ℕ) : ℝ) * e) ^ 2) :=
      payoffIntegrable_of_support_abs_le hsum _ fun x hx => abs_sq_sub_le hx
    rw [expect_addLaw _ _ _ hint]
    have hinner : ∀ a ∈ (sampleSum μ m).support,
        expect μ (fun b => (a + b - ((m + 1 : ℕ) : ℝ) * e) ^ 2) =
          (a - m * e) ^ 2 + v := by
      intro a _
      have hexpand : (fun b => (a + b - ((m + 1 : ℕ) : ℝ) * e) ^ 2) =
          fun b => ((a - m * e) ^ 2 + 2 * (a - m * e) * (b - e)) + (b - e) ^ 2 := by
        funext b
        push_cast
        ring
      have hlin : PayoffIntegrable μ (fun b => 2 * (a - m * e) * (b - e)) :=
        payoffIntegrable_of_support_abs_le hbound _
          (C := |2 * (a - m * e)| * (R + |e|)) fun x hx => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              ((abs_sub x e).trans (add_le_add hx le_rfl)) (abs_nonneg _)
      have hsq : PayoffIntegrable μ (fun b => (b - e) ^ 2) :=
        payoffIntegrable_of_support_abs_le hbound _ fun x hx => abs_sq_sub_le hx
      rw [hexpand, expect_add (payoffIntegrable_add (payoffIntegrable_constant μ _) hlin) hsq,
        expect_add (payoffIntegrable_constant μ _) hlin, expect_constant,
        expect_const_mul, expect_sub_lawMean hbound]
      ring
    rw [expect_congr_on_support hinner]
    have hprev : PayoffIntegrable (sampleSum μ m) (fun a => (a - m * e) ^ 2) :=
      payoffIntegrable_of_support_abs_le (abs_le_of_mem_support_sampleSum hbound m) _
        fun x hx => abs_sq_sub_le hx
    rw [expect_add hprev (payoffIntegrable_constant _ _), ih, expect_constant]
    push_cast
    ring

/-- **Chebyshev's inequality** for a sum of independent bounded draws. -/
theorem sampleSum_deviation_le (hbound : ∀ x ∈ μ.support, |x| ≤ R) (m : ℕ)
    {t : ℝ} (ht : 0 < t) :
    ((sampleSum μ m).toOuterMeasure {s | t ≤ |s - m * lawMean μ|}).toReal ≤
      m * lawVariance μ / t ^ 2 := by
  classical
  have hsupp := abs_le_of_mem_support_sampleSum hbound m
  rw [← expect_indicator]
  have hmono : expect (sampleSum μ m)
      (fun s => if s ∈ {s | t ≤ |s - m * lawMean μ|} then (1 : ℝ) else 0) ≤
        expect (sampleSum μ m) (fun s => (t ^ 2)⁻¹ * (s - m * lawMean μ) ^ 2) := by
    refine expect_mono (fun s _ => ?_) ?_ ?_
    · by_cases hs : s ∈ {s | t ≤ |s - m * lawMean μ|}
      · simp only [hs, ite_true]
        rw [Set.mem_ofPred_eq] at hs
        have ht2 : 0 < t ^ 2 := by positivity
        rw [← div_eq_inv_mul, le_div_iff₀ ht2, one_mul, ← sq_abs (s - _)]
        exact pow_le_pow_left₀ ht.le hs 2
      · simp only [hs, ite_false]
        positivity
    · exact payoffIntegrable_of_support_abs_le hsupp _ (C := 1) fun x _ => by
        split_ifs <;> simp
    · exact payoffIntegrable_of_support_abs_le hsupp _
        (C := |(t ^ 2)⁻¹| * (m * R + |m * lawMean μ|) ^ 2) fun x hx => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_sq_sub_le hx) (abs_nonneg _)
  rw [expect_const_mul, expect_sampleSum_centered_sq hbound m] at hmono
  rw [div_eq_inv_mul]
  exact hmono

end SecondMoment

end GameTheory.Math.Probability
