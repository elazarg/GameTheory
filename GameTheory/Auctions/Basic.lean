import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# Quasi-Linear Games and Auctions

An auction is a `KernelGame` whose utility admits a **quasi-linear
decomposition**: `u_i(ω) = v_i(allocation(ω)) − payment(ω, i)`.

This quasi-linear structure is additional data on a `KernelGame`, not a
separate game type. Properties like individual rationality, revenue,
efficiency, and budget balance are predicates on kernel games equipped
with this structure.

## Main definitions

* `KernelGame.QuasiLinear` — witnesses a quasi-linear utility decomposition
* `KernelGame.QuasiLinear.IsExPostIR` — every outcome gives non-negative utility
* `KernelGame.QuasiLinear.NoPosTransfers` — payments are non-negative
* `KernelGame.QuasiLinear.IsEfficient` — allocation maximizes total valuation
* `auctionGame` — constructs a deterministic quasi-linear `KernelGame`

## Main results

* `auctionGame_eu` — EU of the deterministic auction game
* `auctionGame_quasiLinear` — canonical quasi-linear structure
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- Quasi-linear decomposition of a kernel game's utility.

    Witnesses that utility factors as `v_i(allocation(ω)) − payment(ω, i)`.
    A game equipped with this structure is an auction: the outcome determines
    an allocation of resources, and each player's payoff is their valuation
    of the allocation minus a monetary transfer. -/
structure QuasiLinear (G : KernelGame ι) where
  /-- Space of possible allocations. -/
  Alloc : Type
  /-- Extracts the allocation from an outcome. -/
  allocation : G.Outcome → Alloc
  /-- Extracts per-player payments from an outcome. -/
  payment : G.Outcome → ι → ℝ
  /-- Player valuations over allocations. -/
  val : ι → Alloc → ℝ
  /-- The game's utility is valuation minus payment. -/
  utility_eq : ∀ ω i, G.utility ω i = val i (allocation ω) - payment ω i

namespace QuasiLinear

variable {G : KernelGame ι} (ql : G.QuasiLinear)

/-- Ex-post individual rationality: every outcome gives non-negative utility
    to every player. -/
def IsExPostIR : Prop :=
  ∀ ω i, ql.val i (ql.allocation ω) ≥ ql.payment ω i

/-- No positive transfers: payments are always non-negative. -/
def NoPosTransfers : Prop :=
  ∀ ω i, ql.payment ω i ≥ 0

/-- Allocative efficiency: every outcome's allocation maximizes
    total valuation over all possible allocations. -/
def IsEfficient [Fintype ι] : Prop :=
  ∀ ω (a' : ql.Alloc), ∑ i, ql.val i (ql.allocation ω) ≥ ∑ i, ql.val i a'

/-- Strong budget balance: total payments sum to zero for every outcome. -/
def StrongBudgetBalanced [Fintype ι] : Prop :=
  ∀ ω, ∑ i, ql.payment ω i = 0

end QuasiLinear

-- ============================================================================
-- Deterministic auction construction
-- ============================================================================

open Classical in
/-- Construct a deterministic auction game. Strategies are bids,
    and the outcome is the bid profile itself. Utility is quasi-linear:
    `v_i(alloc(bids)) − payment(bids, i)`. -/
noncomputable def auctionGame {Bid : ι → Type} {Alloc : Type}
    (alloc : (∀ i, Bid i) → Alloc)
    (payment : (∀ i, Bid i) → ι → ℝ)
    (v : ι → Alloc → ℝ) : KernelGame ι where
  Strategy := Bid
  Outcome := ∀ i, Bid i
  utility := fun bids i => v i (alloc bids) - payment bids i
  outcomeKernel := fun σ => PMF.pure σ

/-- EU of the deterministic auction equals valuation minus payment. -/
@[simp] theorem auctionGame_eu {Bid : ι → Type} {Alloc : Type}
    (alloc : (∀ i, Bid i) → Alloc)
    (payment : (∀ i, Bid i) → ι → ℝ)
    (v : ι → Alloc → ℝ) (b : ∀ i, Bid i) (i : ι) :
    (auctionGame alloc payment v).eu b i = v i (alloc b) - payment b i := by
  simp [eu, auctionGame, expect_pure]

/-- The canonical quasi-linear structure on `auctionGame`. -/
noncomputable def auctionGame_quasiLinear {Bid : ι → Type} {Alloc : Type}
    (alloc : (∀ i, Bid i) → Alloc)
    (payment : (∀ i, Bid i) → ι → ℝ)
    (v : ι → Alloc → ℝ) :
    (auctionGame alloc payment v).QuasiLinear where
  Alloc := Alloc
  allocation := alloc
  payment := payment
  val := v
  utility_eq := fun _ _ => rfl

open Classical in
/-- In a deterministic auction, IC (truthful bidding is dominant) implies
    truthful bidding is Nash. -/
theorem auctionGame_ic_isNash {Bid : ι → Type} {Alloc : Type}
    (alloc : (∀ i, Bid i) → Alloc)
    (payment : (∀ i, Bid i) → ι → ℝ)
    (v : ι → Alloc → ℝ)
    (embed : ∀ i, Bid i)
    (hIC : ∀ (i : ι) (b : ∀ j, Bid j) (b' : Bid i),
      v i (alloc (Function.update b i (embed i))) - payment (Function.update b i (embed i)) i ≥
      v i (alloc (Function.update b i b')) - payment (Function.update b i b') i) :
    (auctionGame alloc payment v).IsNash embed := by
  intro who s'
  simp only [auctionGame_eu]
  have := hIC who embed s'
  simp only [Function.update_eq_self] at this
  linarith

end KernelGame

end GameTheory
