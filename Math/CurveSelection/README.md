# Math/CurveSelection

This directory is the proof of a single semialgebraic curve-selection lemma,
exported by `PolynomialSignCellArc.lean` as
`hasPositiveCoordinateAnalyticArcAt_signCell`. That lemma is consumed only by
`GameTheory/Concepts/Stochastic/AnalyticBellmanExistence.lean`.

The 45 files here are organized as **proof chapters**, not as a reusable
library: most have no module docstring, several use `Scratch` namespaces, and
several disable linters locally. None of that is meant to be depended on
outside this directory.

The one supported entry point is
`PolynomialSignCellArc.hasPositiveCoordinateAnalyticArcAt_signCell`. Internal
files, lemma names, and structure may change freely as long as that export
keeps its statement and keeps compiling.
