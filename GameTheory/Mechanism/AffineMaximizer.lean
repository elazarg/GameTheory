/-
# Affine maximizers

An affine maximizer chooses an alternative maximizing positively weighted
reported welfare plus an alternative bias, then charges Clarke externality
payments.  Its output is the canonical capability-free quasilinear direct
mechanism, whose DSIC predicate uses the library's ordinary dominant-strategy
surface.
-/

import GameTheory.Mechanism.QuasiLinear

noncomputable section

open scoped BigOperators

namespace GameTheory.Mechanism

universe up ua ut

/-- Capability-free data whose finite maximization produces an affine
maximizer mechanism. -/
structure AffineMaximizer (Player : Type up) (Alternative : Type ua) where
  /-- Private type and report space of each player. -/
  Ty : Player → Type ut
  /-- Value of an alternative at a player's type. -/
  value : (who : Player) → Ty who → Alternative → ℝ
  /-- Player's coefficient in the affine objective. -/
  weight : Player → ℝ
  /-- Report-independent alternative bias. -/
  bias : Alternative → ℝ

namespace AffineMaximizer

variable {Player : Type up} {Alternative : Type ua}
variable (A : AffineMaximizer Player Alternative)

/-- Signature of direct type reports. -/
abbrev reportSignature : GameSignature Player where
  Strategy := A.Ty
  Outcome := Alternative

/-- A dependent profile of direct type reports. -/
abbrev ReportProfile := Profile A.reportSignature

/-- Positively weighted reported welfare plus the alternative bias. -/
def objective [Fintype Player] (reports : A.ReportProfile)
    (alternative : Alternative) : ℝ :=
  (∑ who, A.weight who * A.value who (reports who) alternative) +
    A.bias alternative

/-- An alternative maximizing the affine objective. -/
noncomputable def choose [Fintype Player] [Fintype Alternative]
    [Nonempty Alternative] (reports : A.ReportProfile) : Alternative :=
  (Finset.exists_max_image Finset.univ (A.objective reports)
    Finset.univ_nonempty).choose

/-- The selected alternative maximizes the affine objective. -/
theorem objective_le_choose [Fintype Player] [Fintype Alternative]
    [Nonempty Alternative] (reports : A.ReportProfile)
    (alternative : Alternative) :
    A.objective reports alternative ≤ A.objective reports (A.choose reports) :=
  (Finset.exists_max_image Finset.univ (A.objective reports)
    Finset.univ_nonempty).choose_spec.2 alternative (Finset.mem_univ alternative)

/-- Weighted reported welfare of every player except `who`, plus the bias. -/
def othersObjective [Fintype Player] [DecidableEq Player]
    (reports : A.ReportProfile) (who : Player)
    (alternative : Alternative) : ℝ :=
  (∑ other ∈ Finset.univ.erase who,
    A.weight other * A.value other (reports other) alternative) +
      A.bias alternative

/-- Best attainable affine objective of the other players and the bias. -/
noncomputable def pivotObjective [Fintype Player] [DecidableEq Player]
    [Fintype Alternative] [Nonempty Alternative]
    (reports : A.ReportProfile) (who : Player) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (A.othersObjective reports who)

/-- Replacing `who`'s report leaves the other-player objective unchanged. -/
theorem othersObjective_update [Fintype Player] [DecidableEq Player]
    (reports : A.ReportProfile) (who : Player) (replacement : A.Ty who)
    (alternative : Alternative) :
    A.othersObjective (Profile.update reports who replacement) who alternative =
      A.othersObjective reports who alternative := by
  unfold othersObjective
  congr 1
  apply Finset.sum_congr rfl
  intro other hother
  exact congrArg (fun report =>
    A.weight other * A.value other report alternative)
      (Profile.update_of_ne _ _ (Finset.mem_erase.mp hother).1)

/-- The other-player objective depends only on reports outside `who`. -/
theorem othersObjective_eq_of_agree [Fintype Player] [DecidableEq Player]
    {reports types : A.ReportProfile} {who : Player}
    (hagree : ∀ other, other ≠ who → reports other = types other) :
    A.othersObjective reports who = A.othersObjective types who := by
  funext alternative
  unfold othersObjective
  congr 1
  apply Finset.sum_congr rfl
  intro other hother
  rw [hagree other (Finset.mem_erase.mp hother).1]

/-- Replacing `who`'s report leaves the pivot objective unchanged. -/
theorem pivotObjective_update [Fintype Player] [DecidableEq Player]
    [Fintype Alternative] [Nonempty Alternative]
    (reports : A.ReportProfile) (who : Player) (replacement : A.Ty who) :
    A.pivotObjective (Profile.update reports who replacement) who =
      A.pivotObjective reports who := by
  unfold pivotObjective
  refine Finset.sup'_congr Finset.univ_nonempty rfl ?_
  intro alternative _
  exact A.othersObjective_update reports who replacement alternative

/-- Splitting the affine objective at one updated coordinate. -/
theorem objective_update [Fintype Player] [DecidableEq Player]
    (reports : A.ReportProfile) (who : Player) (replacement : A.Ty who)
    (alternative : Alternative) :
    A.objective (Profile.update reports who replacement) alternative =
      A.weight who * A.value who replacement alternative +
        A.othersObjective reports who alternative := by
  have hsum :
      ∑ other ∈ Finset.univ.erase who,
          A.weight other *
            A.value other ((Profile.update reports who replacement) other)
              alternative =
        ∑ other ∈ Finset.univ.erase who,
          A.weight other * A.value other (reports other) alternative := by
    apply Finset.sum_congr rfl
    intro other hother
    exact congrArg (fun report =>
      A.weight other * A.value other report alternative)
        (Profile.update_of_ne _ _ (Finset.mem_erase.mp hother).1)
  unfold objective othersObjective
  rw [← Finset.add_sum_erase Finset.univ
    (fun other => A.weight other *
      A.value other ((Profile.update reports who replacement) other)
        alternative) (Finset.mem_univ who)]
  rw [Profile.update_same, hsum]
  ring

/-- The affine maximizer with Clarke externality payments, represented by the
canonical quasilinear direct-mechanism owner. -/
noncomputable def toQuasiLinearMechanism [Fintype Player]
    [DecidableEq Player] [Fintype Alternative] [Nonempty Alternative] :
    QuasiLinearMechanism Player Alternative where
  Ty := A.Ty
  value := A.value
  choose := A.choose
  payment reports who :=
    (1 / A.weight who) *
      (A.pivotObjective reports who -
        A.othersObjective reports who (A.choose reports))

/-- Scaling true utility by a nonzero weight recovers the affine objective at
the selected alternative, less the report-independent pivot. -/
theorem weight_mul_trueUtility [Fintype Player] [DecidableEq Player]
    [Fintype Alternative] [Nonempty Alternative]
    (reports : A.ReportProfile) (who : Player) (trueType : A.Ty who)
    (hweight : A.weight who ≠ 0) :
    A.weight who *
        A.toQuasiLinearMechanism.trueUtility reports who trueType =
      A.objective (Profile.update reports who trueType) (A.choose reports) -
        A.pivotObjective reports who := by
  simp only [QuasiLinearMechanism.trueUtility, toQuasiLinearMechanism]
  rw [A.objective_update]
  field_simp
  ring

/-- Clarke externality payments are nonnegative when the player's weight is
positive. -/
theorem payment_nonneg [Fintype Player] [DecidableEq Player]
    [Fintype Alternative] [Nonempty Alternative]
    (reports : A.ReportProfile) (who : Player) (hweight : 0 < A.weight who) :
    0 ≤ A.toQuasiLinearMechanism.payment reports who := by
  simp only [toQuasiLinearMechanism]
  refine mul_nonneg (le_of_lt (div_pos one_pos hweight)) ?_
  rw [sub_nonneg]
  exact Finset.le_sup' (A.othersObjective reports who)
    (Finset.mem_univ (A.choose reports))

/-- Positive-weight affine maximizers are dominant-strategy incentive
compatible through the canonical Bayesian direct-mechanism predicate. -/
theorem toQuasiLinearMechanism_isDSIC [Fintype Player] [DecidableEq Player]
    [Fintype Alternative] [Nonempty Alternative]
    (hweight : ∀ who, 0 < A.weight who) :
    A.toQuasiLinearMechanism.IsDSIC := by
  intro who types reports misreport
  simp only [QuasiLinearMechanism.toBayesianMechanism]
  have hdeviation := A.weight_mul_trueUtility
    (Profile.update reports who misreport) who (types who)
    (ne_of_gt (hweight who))
  have htruth := A.weight_mul_trueUtility
    (Profile.update reports who (types who)) who (types who)
    (ne_of_gt (hweight who))
  simp only [QuasiLinearMechanism.trueUtility,
    Profile.update_idem] at hdeviation htruth
  have hpivot :
      A.pivotObjective (Profile.update reports who misreport) who =
        A.pivotObjective (Profile.update reports who (types who)) who := by
    rw [A.pivotObjective_update, A.pivotObjective_update]
  have hmax := A.objective_le_choose
    (Profile.update reports who (types who))
    (A.choose (Profile.update reports who misreport))
  apply (mul_le_mul_iff_of_pos_left (hweight who)).mp
  calc
    _ = A.objective (Profile.update reports who (types who))
          (A.choose (Profile.update reports who misreport)) -
        A.pivotObjective (Profile.update reports who misreport) who :=
      hdeviation
    _ ≤ A.objective (Profile.update reports who (types who))
          (A.choose (Profile.update reports who (types who))) -
        A.pivotObjective (Profile.update reports who (types who)) who := by
      rw [hpivot]
      exact sub_le_sub_right hmax _
    _ = _ := htruth.symm

/-- Unit weights and zero bias give the Clarke-pivot VCG mechanism. -/
noncomputable def vcgMechanism (Ty : Player → Type ut)
    (value : (who : Player) → Ty who → Alternative → ℝ)
    [Fintype Player] [DecidableEq Player]
    [Fintype Alternative] [Nonempty Alternative] :
    QuasiLinearMechanism Player Alternative :=
  (AffineMaximizer.mk Ty value (fun _ => 1) (fun _ => 0))
    |>.toQuasiLinearMechanism

/-- The Clarke-pivot VCG specialization is DSIC. -/
theorem vcgMechanism_isDSIC (Ty : Player → Type ut)
    (value : (who : Player) → Ty who → Alternative → ℝ)
    [Fintype Player] [DecidableEq Player]
    [Fintype Alternative] [Nonempty Alternative] :
    (vcgMechanism Ty value).IsDSIC :=
  (AffineMaximizer.mk Ty value (fun _ => 1) (fun _ => 0))
    |>.toQuasiLinearMechanism_isDSIC (fun _ => one_pos)

end AffineMaximizer

end GameTheory.Mechanism
