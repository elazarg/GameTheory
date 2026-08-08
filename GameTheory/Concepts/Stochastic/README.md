# Stochastic games

This directory contains the reusable stochastic-game library. Its public
surface is imported by `GameTheory.Concepts.Stochastic` and is organized by
mathematical role:

- `Core/`: histories, finite-horizon payoffs, stage games, and play measures;
- `Equilibrium/`: discounted, asymptotic, and uniform equilibrium notions and
  stable transfer results;
- `Strategy/` and `Transform/`: history potentials, controllers, legality
  normalization, payoff transforms, and repeated-game adapters;
- `Classes/`, `Welfare/`, and `ZeroSum/`: reusable game classes and established
  theorem surfaces; and
- `Models/`: model definitions and their basic semantics, currently including
  quitting games.

The uniform-equilibrium existence research program lives entirely under
[`UniformEquilibrium/`](UniformEquilibrium/README.md). It imports this generic
library; generic modules must never import the research subtree. This one-way
dependency is the extraction boundary for moving that program to a repository
which uses GameTheory as a submodule.

Import `GameTheory.Concepts.Stochastic` for the generic API. Import
`GameTheory.Concepts.Stochastic.UniformEquilibrium` explicitly for the research
program's aggregate surface.

Directory names own their mathematical context, so module basenames do not
repeat the corresponding family prefix. For example, `Models/Quitting/Game`
and `UniformEquilibrium/Quitting/Projective/Lasso` use the path to supply
`Quitting` and `Projective`. A family's primary module is named `Basic.lean`.
Qualifiers are retained when removing one would merge distinct siblings.
