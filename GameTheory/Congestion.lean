module

/-
# `GameTheory.Congestion`

Opt-in stable finite-player congestion games, Rosenthal's potential, and the
affine `5/2` pure price-of-anarchy theorem.  This root is intentionally not
re-exported from `GameTheory`: congestion theory is a domain package built on
the stable static core.
-/

public import GameTheory.Congestion.Rosenthal
public import GameTheory.Congestion.AffinePoA
public import GameTheory.Congestion.Examples

@[expose] public section

namespace GameTheory

end GameTheory
