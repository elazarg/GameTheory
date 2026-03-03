# Family → Building-Block Map

This map strips mnemonics and modeling choices and records which structural
blocks dominate each file family.

Blocks refer to `70-GlobalBuildingBlocks.md`.

## F1/F8 Core+Meta

Primary blocks:

- `B0` finite index algebra
- `B5` translation/refinement preservation
- `B10` adapter minimality

## F2 Bridge

Primary blocks:

- `B5` translation/refinement preservation
- `B3` reachability-restricted extensionality
- `B0` finite index algebra

## F3 Trace / Sequential

Primary blocks:

- `B2` locality/non-interference
- `B3` reachable extensionality
- `B4` disintegrate/recombine
- `B1` distributional composition
- `B7` recursive value construction (for Zermelo-like tracks)

## F4 Equilibrium Concepts / Existence

Primary blocks:

- `B6` fixed-point transfer skeleton
- `B8` continuity/convex transfer
- `B11` feasible-region geometry layer
- `B9` inequality rearrangement
- `B1` distributional composition

## F5 Dynamics / Potential / Dominance

Primary blocks:

- `B2` locality/non-interference
- `B9` inequality and monotonicity algebra
- `B7` well-founded descent/termination style

## F6 Mechanism / Auction / Social Aggregation

Primary blocks:

- `B5` refinement-preservation (format conversions)
- `B9` inequality decomposition
- `B0` relation/update algebra
- `B11` feasible-region geometry when IR-like constraints are explicit

## F7 Value / Minimax / Welfare

Primary blocks:

- `B7` well-founded/recursive value construction
- `B6` fixed-point or saddle transfer skeleton
- `B9` inequality optimization algebra
- `B11` feasible-region geometry layer

## Survey usage

For any theorem:

1. assign family,
2. map to 2-4 primary blocks,
3. verify assumptions are block-minimal (not format artifacts),
4. if needed, extract one-shot lemmas in block language.
