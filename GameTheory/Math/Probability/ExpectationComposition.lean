import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.Joint

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

/-- A global payoff bound provides all summability certificates for the tower.
The bound is required to be nonnegative so the inner values inherit it.
-/
theorem expect_bind_tower_bounded {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ b, |f b| ≤ C) :
    expect (p.bind q) f (payoffIntegrable_of_bounded (p.bind q) f hbound) =
      expect p
      (fun a => expect (q a) f (payoffIntegrable_of_bounded (q a) f hbound))
        (payoffIntegrable_of_bounded p _ (fun a =>
          expect_abs_le_of_bounded hC hbound
            (payoffIntegrable_of_bounded (q a) f hbound))) := by
  let hbind := payoffIntegrable_of_bounded (p.bind q) f hbound
  let hcond := fun a => payoffIntegrable_of_bounded (q a) f hbound
  have htower := expect_bind_tower p q f hbind hcond
  calc
    expect (p.bind q) f
        (payoffIntegrable_of_bounded (p.bind q) f hbound) =
      expect p (fun a => expect (q a) f (hcond a))
        (payoffIntegrable_bind_conditionalExpectation p q f hbind hcond) :=
          htower
    _ = expect p (fun a => expect (q a) f
        (payoffIntegrable_of_bounded (q a) f hbound))
        (payoffIntegrable_of_bounded p _ (fun a =>
          expect_abs_le_of_bounded hC hbound
            (payoffIntegrable_of_bounded (q a) f hbound))) := by
      exact expect_proof_irrel p _ _ _

/-- An independently sampled pair can be integrated by rows. The guard on the
joint law is necessary in addition to the row and outer expectation guards. -/
theorem expect_bindPairLaw_tower {α β : Type*}
    (p : PMF α) (q : PMF β) (f : α × β → ℝ)
    (hjoint : PayoffIntegrable (bindPairLaw p (fun _ => q)) f)
    (hrow : ∀ a, PayoffIntegrable q (fun b => f (a, b)))
    (houter : PayoffIntegrable p (fun a =>
      expect q (fun b => f (a, b)) (hrow a))) :
    expect (bindPairLaw p (fun _ => q)) f hjoint =
      expect p (fun a => expect q (fun b => f (a, b)) (hrow a)) houter := by
  let kernel : α → PMF (α × β) := fun a => q.map fun b => (a, b)
  have hcond : ∀ a, PayoffIntegrable (kernel a) f := fun a =>
    (payoffIntegrable_map_iff (fun b => (a, b)) q f).mpr (hrow a)
  have hrowEq (a : α) :
      expect (kernel a) f (hcond a) =
        expect q (fun b => f (a, b)) (hrow a) :=
    expect_map (fun b => (a, b)) q f (hrow a) (hcond a)
  have houterMapped :=
    payoffIntegrable_bind_conditionalExpectation p kernel f hjoint hcond
  calc
    expect (bindPairLaw p (fun _ => q)) f hjoint =
        expect (p.bind kernel) f hjoint := rfl
    _ = expect p (fun a => expect (kernel a) f (hcond a)) houterMapped :=
      expect_bind_tower p kernel f hjoint hcond
    _ = expect p (fun a => expect q (fun b => f (a, b)) (hrow a)) houter :=
      expect_congr_on_support (fun a _ => hrowEq a) houterMapped houter

end GameTheory.Math.Probability
