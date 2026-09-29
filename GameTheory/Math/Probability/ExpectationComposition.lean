import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.Joint

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

/-- A global payoff bound makes every law integrable, so the tower law holds
unconditionally. -/
theorem expect_bind_tower_bounded {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℝ)
    {C : ℝ} (hbound : ∀ b, |f b| ≤ C) :
    expect (p.bind q) f = expect p (fun a => expect (q a) f) :=
  expect_bind_tower p q f (payoffIntegrable_of_bounded (p.bind q) f hbound)

/-- An independently sampled pair can be integrated by rows once the joint law
is integrable. -/
theorem expect_bindPairLaw_tower {α β : Type*}
    (p : PMF α) (q : PMF β) (f : α × β → ℝ)
    (hjoint : PayoffIntegrable (bindPairLaw p (fun _ => q)) f) :
    expect (bindPairLaw p (fun _ => q)) f =
      expect p (fun a => expect q (fun b => f (a, b))) := by
  let kernel : α → PMF (α × β) := fun a => q.map fun b => (a, b)
  calc
    expect (bindPairLaw p (fun _ => q)) f =
        expect (p.bind kernel) f := rfl
    _ = expect p (fun a => expect (kernel a) f) :=
      expect_bind_tower p kernel f hjoint
    _ = expect p (fun a => expect q (fun b => f (a, b))) :=
      expect_congr_on_support (fun a _ => expect_map (fun b => (a, b)) q f)

end GameTheory.Math.Probability
