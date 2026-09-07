# Add finite-product projection, one-participant predrawing, and bounded-run lemmas

## Purpose

Extend GameTheory's finite-probability and execution-protocol APIs with reusable
lemmas for marginalization, continuation composition, and sampling one
participant's randomness before execution. These results should depend only on
the existing `FinDist`, `ExecutionProtocol`, and `InformationModel` abstractions.
They require no utilities, equilibrium assumptions, or additional axioms.

The signatures below specify the requested API; proof bodies are omitted.

## 1. Finite distributions

Add the following in `GameTheory/Math/Probability/FinDist.lean`, in namespace
`GameTheory.Math.Probability.FinDist`.

### Linearity in one product marginal

Replacing one marginal of an independent product by a mixture commutes with
taking the product. All other marginals remain unchanged.

```lean
theorem pi_update_bind {ι α : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} (laws : ∀ i, FinDist (A i)) (who : ι)
    (μ : FinDist α) (choices : α → FinDist (A who)) :
    FinDist.pi (FinDist.DependentAssignment.setOne laws ⟨who, μ.bind choices⟩) =
      μ.bind (fun a => FinDist.pi (FinDist.DependentAssignment.setOne laws ⟨who, choices a⟩))
```

`pi_eq_map_product` supplies a proof route: split off the selected coordinate,
then use associativity of `bind`. Refactor the existing
`GameForm.pi_update_mixed` proof to use this theorem with
`choices := FinDist.pure`, rather than retain two independent proofs.

### Composition through equal summary laws

Equal distributions of summaries permit composition with continuation laws
that agree on matching supported summaries. Neither summary map needs an
inverse, and the original distributions may have different carrier types.

```lean
theorem bind_eq_of_map_eq {α β γ δ : Type*}
    (μ : FinDist α) (ν : FinDist β) (f : α → γ) (g : β → γ)
    (hmap : μ.map f = ν.map g)
    (F : α → FinDist δ) (H : β → FinDist δ)
    (hagree : ∀ a ∈ μ.support, ∀ b ∈ ν.support,
      f a = g b → F a = H b) :
    μ.bind F = ν.bind H
```

Agreement is required only on support, not on unreachable values. One proof
route chooses a supported representative of each attained summary and factors
both continuations through the resulting common kernel.

### Projection onto an embedded set of coordinates

Projecting an independent product onto any injectively selected coordinates
gives the product of their marginals.

```lean
theorem pi_map_embedding {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : ι → Type*} (e : κ ↪ ι) (laws : ∀ i, FinDist (A i)) :
    (FinDist.pi laws).map (fun values k => values (e k)) =
      FinDist.pi (fun k => laws (e k))
```

This extends the existing single-coordinate marginal and equivalence-based
reindexing results. Injectivity is essential: selecting one random coordinate
twice generally produces correlated copies, not independent draws. No
finiteness assumption on the value types `A i` is needed.

## 2. Predrawing one participant

Place these results in the protocol layer, in namespace
`GameTheory.Protocol.InformationModel`. A dedicated
`GameTheory/Protocol/Predraw.lean` importing `Protocol.Information` owns these
results. Use `Profile.update` with the existing `M.behavioralSignature`, now
owned by `Protocol.Information`, for participant replacement.

Use the following common context, with the probability namespace open:

```lean
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} (M : InformationModel E)
```

### One joint draw is linear in one participant's policy

```lean
theorem behavioralJoint_update_bind {α : Type*}
    (profile : Profile M.behavioralSignature) (who : ι)
    (μ : FinDist α) (policies : α → M.BehavioralPolicy who)
    {state : E.State} (trace : E.Trace state)
    (hterm : ¬ E.terminal state) :
    M.behavioralJoint
        (Profile.update profile who
          (fun info => μ.bind (fun a => policies a info))) trace hterm =
      μ.bind (fun a =>
        M.behavioralJoint (Profile.update profile who (policies a)) trace hterm)
```

Derive this from `FinDist.pi_update_bind`. It concerns a single joint draw;
pointwise mixing of behavioral policies does not generally equal sampling one
whole policy before a multi-step run.

### Explicit finite-table predrawing

```lean
theorem runBehavioralFrom_predrawOneOn
    (who : ι) [DecidableEq (M.InfoState who)]
    (hfresh : ∀ first later : E.History,
      first.trace.length < later.trace.length →
        M.infoOf who later.trace ≠ M.infoOf who first.trace)
    (profile : Profile M.behavioralSignature)
    (fuel : Nat) (policy : M.BehavioralPolicy who)
    (sites : Finset (M.InfoState who)) (fallback : M.Policy who)
    (start : E.History)
    (hfinite : ∀ info, info ∉ sites →
      policy info = FinDist.pure (fallback info)) :
    ((policy.toMixedOn sites fallback).bind fun purePolicy =>
      M.runBehavioralFrom
        (Profile.update profile who purePolicy.toBehavioral) fuel start) =
      M.runBehavioralFrom (Profile.update profile who policy) fuel start
```

`toMixedOn` samples the participant's action at each selected information state
and uses the deterministic fallback elsewhere. The theorem preserves the
complete history law, with every other participant's behavioral policy intact.

Keep `hfresh` explicit: it quantifies over **all pairs of histories of different
lengths**, not merely prefix-related histories or decision sites. This is a
sufficient hypothesis, not a claim that it is necessary or equivalent to
perfect recall. Weakening it is outside this issue.

### Existence for a fixed finite run

```lean
theorem exists_predrawOne (who : ι)
    (hfresh : ∀ first later : E.History,
      first.trace.length < later.trace.length →
        M.infoOf who later.trace ≠ M.infoOf who first.trace)
    (profile : Profile M.behavioralSignature)
    (fuel : Nat) (start : E.History) :
    ∃ policies : FinDist (M.Policy who),
      (policies.bind fun policy =>
        M.runBehavioralFrom
          (Profile.update profile who policy.toBehavioral) fuel start) =
        M.runBehavioralFrom profile fuel start
```

Construct the finite table from `behavioralSupportSitesFrom`, use
`supportFallback` outside that table, and apply the explicit predrawing result
plus support-local run congruence.

The witness may depend on the entire profile, starting history, and horizon.
This is not a uniform translation across opponent profiles. It requires
neither globally finite information states nor finite action carriers:
`FinDist` and the finite horizon provide the required finite support.

## 3. Bounded execution

### A run terminates or consumes its fuel

Add in `GameTheory/Protocol/Randomized.lean`, namespace `ExecutionProtocol`:

```lean
theorem runRandomizedFor_terminal_or_length
    {ι : Type*} {E : ExecutionProtocol ι}
    (chooser : E.RandomizedChooser) (fuel : Nat)
    (start next : E.History)
    (hnext : next ∈ (E.runRandomizedFor chooser fuel start).support) :
    E.terminal next.state ∨ start.trace.length + fuel ≤ next.trace.length
```

### A certified horizon reaches terminal histories

Add the following two results in `GameTheory/Protocol/Information.lean`,
namespace `InformationModel`, using this context:

```lean
variable {ι : Type*} [Fintype ι]
  {E : ExecutionProtocol ι} (M : InformationModel E)
```

```lean
theorem runBehavioralFrom_terminal_of_bound
    (profile : (who : ι) → M.BehavioralPolicy who) {bound : Nat}
    (hbound : E.BoundedHorizon bound) (start next : E.History)
    (hnext : next ∈ (M.runBehavioralFrom profile bound start).support) :
    E.terminal next.state

theorem runBehavioralFrom_bound_add
    (profile : (who : ι) → M.BehavioralPolicy who) {bound : Nat}
    (hbound : E.BoundedHorizon bound) (extra : Nat) (start : E.History) :
    M.runBehavioralFrom profile (bound + extra) start =
      M.runBehavioralFrom profile bound start
```

`BoundedHorizon bound` means every legal history of length at least `bound`
is terminal. These statements allow any starting history; they do not assume
execution starts at the initial state. The second follows from the first,
`runBehavioralFrom_add`, and terminal absorption.

## Acceptance criteria

- Prove all nine statements without `sorry`, new axioms, or warning suppression.
- Keep the probability results independent of the protocol layer and the
  protocol results independent of utility and equilibrium definitions.
- Expose any new module through the appropriate library aggregator and build
  it in CI.
- Replace the independent proof of `GameForm.pi_update_mixed` with its
  specialization of `pi_update_bind`.
- Check projection for identity embeddings, a proper subset, and an empty
  index set; check predrawing at zero fuel, from a terminal history, and in
  a two-step run with randomized opponents whose information states repeat.
- Retain explicit documentation of freshness, finite-support scope, and the
  profile-local existential witness. Do not infer a whole-run mixture law
  from the one-step linearity lemma.
- Run the full warning-free library build and the project's axiom checks.

No changes to policy representations, equilibrium definitions, or public
compiler interfaces are requested. Realizing a finite mixture of behavioral
policies as a single behavioral policy is a separate result.
