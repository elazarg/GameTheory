# Module Families (Abstraction-Oriented)

Use this as the first-pass clustering for assumption trimming.

## F1. Core Game Objects

Representative files:

- `GameForm.lean`
- `NFG.lean`
- `EFG.lean`
- `SequentialForm.lean`
- `MAID.lean`
- `TwoPlayerGame.lean`

Focus:

- state/action/utility carriers
- profile and strategy representations
- conversion-safe structural interfaces

## F2. Conversion / Representation Bridges

Representative files:

- `EFG_NFG.lean`, `NFG_EFG.lean`
- `MAID_EFG.lean`, `EFG_Sequential.lean`
- `EFG_Proto.lean`, `NFG_Proto.lean`, `MAID_Proto.lean`
- `SequentialODP.lean`, `SequentialZermelo.lean`

Focus:

- representation invariants
- semantics-preservation under translation
- minimal assumptions for round-trip properties

## F3. Protocol / Trace / Sequential Reasoning

Representative files:

- `ProtoKuhn.lean`, `ProtoZermelo.lean`, `ProtoSPE.lean`, `ProtoODP.lean`
- `SeqProto.lean`
- `OneShotDeviation.lean`

Focus:

- list-of-step kernel composition
- update invariance / non-interference conditions
- disintegration-style constructions

## F4. Equilibrium and Stability Concepts

Representative files:

- `SolutionConcepts.lean`, `NashProperties.lean`, `NashExistence*.lean`
- `CorrelatedEqProperties.lean`, `CorrelatedNashMixed.lean`
- `StrictNashProperties.lean`, `EvolutionaryStability.lean`
- `ApproximateNash.lean`, `Rationalizability.lean`

Focus:

- best-response/fixed-point theorem interfaces
- support conditions and existence assumptions
- concept implication lattice

## F5. Dominance / Potential / Dynamics

Representative files:

- `Dominance*.lean`
- `Potential*.lean`
- `BestResponse*.lean`
- `Regret.lean`

Focus:

- monotonic descent arguments
- finite improvement path assumptions
- order/well-foundedness as primary non-game assumptions

## F6. Mechanism / Auction / Social Choice

Representative files:

- `Auction.lean`, `VickreyAuction.lean`, `VCG.lean`, `MechanismDesign.lean`
- `SocialChoice.lean`, `PublicGoods.lean`, `Matching.lean`

Focus:

- incentive constraints as inequalities/argmax conditions
- truthfulness/IR/efficiency as algebraic predicates
- decomposition into feasibility + dominance + optimality kernels

## F7. Global Minimax / Welfare / Value Theorems

Representative files:

- `Minimax*.lean`, `ZeroSum*.lean`
- `WelfareTheorems.lean`
- `ParetoOptimal.lean`, `TeamGame*.lean`

Focus:

- convexity/compactness/finiteness interfaces
- saddle-point and duality patterns
- theorem-shape reuse across representations

