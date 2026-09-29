import GameTheory.Math.Probability.ExpectationComposition
import GameTheory.Math.Probability.ExpectationMixture

/-! # The payoff component affected by correlation

Two laws on a product with the same marginals agree on every additive payoff.
Conversely, a bounded payoff is unaffected by every such change of coupling
only when it is additive; balanced two-by-two switches already detect any
failure. For an arbitrary bounded payoff, its centered interaction component
accounts for the entire expectation difference, and the gain from correlating
the coordinates relative to independent sampling is its mean interaction.

The bound supplies every summability certificate, including for laws of
infinite support. The additive identity itself needs only integrability of the
two one-coordinate payoffs under the shared marginals.
-/

noncomputable section

namespace GameTheory.Math.Probability

variable {First Second : Type*}

/-- Additive payoffs see only the marginals of a law on a product. -/
theorem expect_additive_eq_of_marginals {first second : PMF (First × Second)}
    (hleft : first.map Prod.fst = second.map Prod.fst)
    (hright : first.map Prod.snd = second.map Prod.snd)
    {row : First → ℝ} {column : Second → ℝ}
    (hrow : PayoffIntegrable (first.map Prod.fst) row)
    (hcolumn : PayoffIntegrable (first.map Prod.snd) column) :
    expect first (fun outcome => row outcome.1 + column outcome.2) =
      expect second (fun outcome => row outcome.1 + column outcome.2) := by
  have hrow' : PayoffIntegrable (second.map Prod.fst) row :=
    payoffIntegrable_congr_law hleft hrow
  have hcolumn' : PayoffIntegrable (second.map Prod.snd) column :=
    payoffIntegrable_congr_law hright hcolumn
  have hsplit (law : PMF (First × Second))
      (hr : PayoffIntegrable (law.map Prod.fst) row)
      (hc : PayoffIntegrable (law.map Prod.snd) column) :
      expect law (fun outcome => row outcome.1 + column outcome.2) =
        expect (law.map Prod.fst) row + expect (law.map Prod.snd) column := by
    have hr' := (payoffIntegrable_map_iff Prod.fst law row).1 hr
    have hc' := (payoffIntegrable_map_iff Prod.snd law column).1 hc
    rw [expect_map Prod.fst law row, expect_map Prod.snd law column]
    exact expect_add hr' hc'
  rw [hsplit first hrow hcolumn, hsplit second hrow' hcolumn']
  exact congrArg₂ (· + ·) (expect_congr_law hleft _)
    (expect_congr_law hright _)

section Bounded

variable {payoff : First × Second → ℝ} {C : ℝ}

namespace TwoFactor

private theorem bound_nonneg (hbound : ∀ outcome, |payoff outcome| ≤ C)
    (outcome : First × Second) : 0 ≤ C :=
  (abs_nonneg _).trans (hbound outcome)

/-- The mean payoff of a fixed first coordinate against the second reference. -/
def rowMean (payoff : First × Second → ℝ) (right : PMF Second) (first : First) : ℝ :=
  expect right (fun second => payoff (first, second))

/-- The mean payoff of a fixed second coordinate against the first reference. -/
def columnMean (payoff : First × Second → ℝ) (left : PMF First) (second : Second) : ℝ :=
  expect left (fun first => payoff (first, second))

theorem abs_rowMean_le (right : PMF Second)
    (hbound : ∀ outcome, |payoff outcome| ≤ C) (first : First) :
    |rowMean payoff right first| ≤ C := by
  obtain ⟨second, -⟩ := right.support_nonempty
  exact expect_abs_le_of_bounded (bound_nonneg hbound (first, second))
    (fun second => hbound (first, second))

theorem abs_columnMean_le (left : PMF First)
    (hbound : ∀ outcome, |payoff outcome| ≤ C) (second : Second) :
    |columnMean payoff left second| ≤ C := by
  obtain ⟨first, -⟩ := left.support_nonempty
  exact expect_abs_le_of_bounded (bound_nonneg hbound (first, second))
    (fun first => hbound (first, second))

/-- The payoff averaged over both reference laws, drawn independently. -/
def grandMean (payoff : First × Second → ℝ) (left : PMF First) (right : PMF Second) : ℝ :=
  expect left (rowMean payoff right)

/-- Averaging the column means gives the same grand mean: the two orders of
integration agree for a bounded payoff. -/
theorem expect_columnMean (left : PMF First) (right : PMF Second)
    (hbound : ∀ outcome, |payoff outcome| ≤ C) :
    expect right (columnMean payoff left) =
      grandMean payoff left right := by
  have hjoint := payoffIntegrable_of_bounded (bindPairLaw left fun _ => right) payoff hbound
  have hswapped := payoffIntegrable_of_bounded (bindPairLaw right fun _ => left)
    (payoff ∘ Prod.swap) (fun outcome => hbound outcome.swap)
  have hforward := expect_bindPairLaw_tower left right payoff hjoint
  have hbackward := expect_bindPairLaw_tower right left (payoff ∘ Prod.swap) hswapped
  have hswap := expect_map Prod.swap (bindPairLaw left fun _ => right) (payoff ∘ Prod.swap)
  simp only [Function.comp_def, Prod.swap_swap] at hswap
  calc
    _ = expect (bindPairLaw right fun _ => left) (payoff ∘ Prod.swap) :=
      hbackward.symm
    _ = expect ((bindPairLaw left fun _ => right).map Prod.swap) (payoff ∘ Prod.swap)
           := expect_congr_law (bindPairLaw_const_map_swap left right).symm _
    _ = expect (bindPairLaw left fun _ => right) payoff := hswap
    _ = grandMean payoff left right := hforward

/-- The part of a two-coordinate payoff not explained by its two one-coordinate
effects, centered at independent reference laws for the coordinates. -/
def interaction (payoff : First × Second → ℝ) (left : PMF First) (right : PMF Second)
    (outcome : First × Second) : ℝ :=
  payoff outcome - rowMean payoff right outcome.1 - columnMean payoff left outcome.2 +
    grandMean payoff left right

theorem abs_interaction_le (left : PMF First) (right : PMF Second)
    (hbound : ∀ outcome, |payoff outcome| ≤ C) (outcome : First × Second) :
    |interaction payoff left right outcome| ≤ 4 * C := by
  have hrow := abs_rowMean_le right hbound outcome.1
  have hcolumn := abs_columnMean_le left hbound outcome.2
  have hgrand : |grandMean payoff left right| ≤ C := by
    exact expect_abs_le_of_bounded (bound_nonneg hbound outcome)
      (abs_rowMean_le right hbound)
  have hpayoff := hbound outcome
  unfold interaction
  calc
    _ ≤ |payoff outcome| + |rowMean payoff right outcome.1| +
          |columnMean payoff left outcome.2| + |grandMean payoff left right| := by
      have h1 := abs_sub (payoff outcome - rowMean payoff right outcome.1 -
        columnMean payoff left outcome.2) (-grandMean payoff left right)
      have h2 := abs_sub (payoff outcome - rowMean payoff right outcome.1)
        (columnMean payoff left outcome.2)
      have h3 := abs_sub (payoff outcome) (rowMean payoff right outcome.1)
      rw [sub_neg_eq_add, abs_neg] at h1
      linarith
    _ ≤ 4 * C := by linarith

/-- Integrability of the centered interaction under every law. -/
theorem payoffIntegrable_interaction (law : PMF (First × Second)) (left : PMF First)
    (right : PMF Second) (hbound : ∀ outcome, |payoff outcome| ≤ C) :
    PayoffIntegrable law (interaction payoff left right) :=
  payoffIntegrable_of_bounded _ _ (abs_interaction_le left right hbound)

/-- The interaction's expectation, split into the payoff's expectation and its
marginal corrections. -/
theorem expect_interaction (law : PMF (First × Second)) (left : PMF First)
    (right : PMF Second) (hbound : ∀ outcome, |payoff outcome| ≤ C) :
    expect law (interaction payoff left right) =
      expect law payoff -
        expect (law.map Prod.fst) (rowMean payoff right) -
        expect (law.map Prod.snd) (columnMean payoff left) +
        grandMean payoff left right := by
  have hp := payoffIntegrable_of_bounded law payoff hbound
  have hr := payoffIntegrable_of_bounded law (fun outcome => rowMean payoff right outcome.1)
    (fun outcome => abs_rowMean_le right hbound outcome.1)
  have hc := payoffIntegrable_of_bounded law
    (fun outcome => columnMean payoff left outcome.2)
    (fun outcome => abs_columnMean_le left hbound outcome.2)
  have hm := payoffIntegrable_constant law (grandMean payoff left right)
  have hrow := expect_map Prod.fst law (rowMean payoff right)
  have hcolumn := expect_map Prod.snd law (columnMean payoff left)
  have hsplit := expect_add (payoffIntegrable_sub (payoffIntegrable_sub hp hr) hc) hm
  rw [expect_sub (payoffIntegrable_sub hp hr) hc, expect_sub hp hr,
    expect_constant] at hsplit
  rw [hrow, hcolumn]
  exact hsplit

/-- **Only the interaction changes under recoupling.** For laws with the same
marginals, the payoff's expectation difference is the interaction's, whatever
the reference laws used to center it. -/
theorem expect_sub_eq_interaction_of_marginals {first second : PMF (First × Second)}
    (hleft : first.map Prod.fst = second.map Prod.fst)
    (hright : first.map Prod.snd = second.map Prod.snd)
    (left : PMF First) (right : PMF Second) (hbound : ∀ outcome, |payoff outcome| ≤ C) :
    expect first payoff -
        expect second payoff =
      expect first (interaction payoff left right) -
        expect second (interaction payoff left right) := by
  rw [expect_interaction first left right hbound, expect_interaction second left right hbound,
    expect_congr_law hleft (rowMean payoff right) ,
    expect_congr_law hright (columnMean payoff left)]
  ring

/-- For each first coordinate, the interaction averages to zero over the
second reference law. -/
theorem expect_interaction_right (left : PMF First) (right : PMF Second)
    (hbound : ∀ outcome, |payoff outcome| ≤ C) (first : First) :
    expect right (fun second => interaction payoff left right (first, second))
         = 0 := by
  have hp := payoffIntegrable_of_bounded right (fun second => payoff (first, second))
    (fun second => hbound (first, second))
  have hr := payoffIntegrable_constant right (rowMean payoff right first)
  have hc := payoffIntegrable_of_bounded right _ (abs_columnMean_le left hbound)
  have hm := payoffIntegrable_constant right (grandMean payoff left right)
  have hsplit := expect_add (payoffIntegrable_sub (payoffIntegrable_sub hp hr) hc) hm
  rw [expect_sub (payoffIntegrable_sub hp hr) hc, expect_sub hp hr] at hsplit
  unfold interaction
  refine (hsplit.trans ?_)
  rw [expect_constant, expect_constant, expect_columnMean left right hbound]
  unfold rowMean
  ring

/-- For each second coordinate, the interaction averages to zero over the
first reference law. -/
theorem expect_interaction_left (left : PMF First) (right : PMF Second)
    (hbound : ∀ outcome, |payoff outcome| ≤ C) (second : Second) :
    expect left (fun first => interaction payoff left right (first, second))
         = 0 := by
  have hp := payoffIntegrable_of_bounded left (fun first => payoff (first, second))
    (fun first => hbound (first, second))
  have hr := payoffIntegrable_of_bounded left _ (abs_rowMean_le right hbound)
  have hc := payoffIntegrable_constant left (columnMean payoff left second)
  have hm := payoffIntegrable_constant left (grandMean payoff left right)
  have hsplit := expect_add (payoffIntegrable_sub (payoffIntegrable_sub hp hr) hc) hm
  rw [expect_sub (payoffIntegrable_sub hp hr) hc, expect_sub hp hr] at hsplit
  unfold interaction
  refine (hsplit.trans ?_)
  rw [expect_constant, expect_constant]
  unfold columnMean grandMean
  ring

/-- **The value of correlation is the mean interaction.** Relative to
independent sampling from the same marginals, a coupling gains exactly the
expected interaction centered at those marginals. -/
theorem expect_sub_independent_eq_interaction (law : PMF (First × Second))
    (hbound : ∀ outcome, |payoff outcome| ≤ C) :
    expect law payoff -
        expect (bindPairLaw (law.map Prod.fst) fun _ => law.map Prod.snd) payoff =
      expect law (interaction payoff (law.map Prod.fst) (law.map Prod.snd)) := by
  let independent := bindPairLaw (law.map Prod.fst) fun _ => law.map Prod.snd
  have hleft : law.map Prod.fst = independent.map Prod.fst :=
    (bindPairLaw_map_fst _ _).symm
  have hright : law.map Prod.snd = independent.map Prod.snd := by
    rw [bindPairLaw_map_snd, PMF.bind_const]
  rw [expect_sub_eq_interaction_of_marginals hleft hright (law.map Prod.fst)
    (law.map Prod.snd) hbound]
  have hzero : expect independent (interaction payoff (law.map Prod.fst) (law.map Prod.snd))
       = 0 := by
    rw [expect_bindPairLaw_tower _ _ _ (payoffIntegrable_interaction _ _ _ hbound)]
    simp only [expect_interaction_right _ _ hbound]
    exact expect_zero _
  rw [hzero, sub_zero]

end TwoFactor

/-- **Exactly the additive payoffs ignore correlation.** A bounded payoff has
the same expectation under all laws with equal marginals if and only if it is a
sum of one-coordinate payoffs. -/
theorem expect_eq_of_marginals_iff_additive [Nonempty First] [Nonempty Second]
    (hbound : ∀ outcome, |payoff outcome| ≤ C) :
    (∀ first second : PMF (First × Second),
      first.map Prod.fst = second.map Prod.fst →
      first.map Prod.snd = second.map Prod.snd →
      expect first payoff =
        expect second payoff) ↔
      ∃ row : First → ℝ, ∃ column : Second → ℝ,
        ∀ outcome, payoff outcome = row outcome.1 + column outcome.2 := by
  constructor
  · intro hpreserves
    let rowBase : First := Classical.ofNonempty
    let columnBase : Second := Classical.ofNonempty
    refine ⟨fun row => payoff (row, columnBase),
      fun column => payoff (rowBase, column) - payoff (rowBase, columnBase), ?_⟩
    rintro ⟨row, column⟩
    have half₀ : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have half₁ : (1 / 2 : ℝ) ≤ 1 := by norm_num
    let diagonal := mix (1 / 2) half₀ half₁
      (PMF.pure (row, column)) (PMF.pure (rowBase, columnBase))
    let crossed := mix (1 / 2) half₀ half₁
      (PMF.pure (row, columnBase)) (PMF.pure (rowBase, column))
    have hleft : diagonal.map Prod.fst = crossed.map Prod.fst := by
      simp only [diagonal, crossed, mix_map, PMF.pure_map]
    have hright : diagonal.map Prod.snd = crossed.map Prod.snd := by
      simp only [diagonal, crossed, mix_map, PMF.pure_map]
      ext value
      simp only [mix_apply]
      norm_num
      ring
    have hequal := hpreserves diagonal crossed hleft hright
    simp only [diagonal, crossed] at hequal
    rw [expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
      expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
      expect_pure, expect_pure, expect_pure, expect_pure] at hequal
    dsimp only
    linarith
  · rintro ⟨row, column, hrepresentation⟩ first second hleft hright
    have hsame : payoff = fun outcome => row outcome.1 + column outcome.2 :=
      funext hrepresentation
    obtain ⟨rowBase⟩ := ‹Nonempty First›
    obtain ⟨columnBase⟩ := ‹Nonempty Second›
    have hrowBound (value : First) :
        |row value| ≤ C + |column columnBase| := by
      have := hbound (value, columnBase)
      rw [hrepresentation] at this
      calc
        |row value| = |(row value + column columnBase) - column columnBase| := by ring_nf
        _ ≤ |row value + column columnBase| + |column columnBase| := abs_sub _ _
        _ ≤ _ := by linarith
    have hcolumnBound (value : Second) :
        |column value| ≤ C + |row rowBase| := by
      have := hbound (rowBase, value)
      rw [hrepresentation] at this
      calc
        |column value| = |(row rowBase + column value) - row rowBase| := by ring_nf
        _ ≤ |row rowBase + column value| + |row rowBase| := abs_sub _ _
        _ ≤ _ := by linarith
    subst hsame
    exact expect_additive_eq_of_marginals hleft hright
      (payoffIntegrable_of_bounded _ _ hrowBound)
      (payoffIntegrable_of_bounded _ _ hcolumnBound)

end Bounded

end GameTheory.Math.Probability
