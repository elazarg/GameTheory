import GameTheory.Languages.FOSG.Basic
import GameTheory.Languages.FOSG.Compile
import GameTheory.Languages.FOSG.Kuhn
import GameTheory.Languages.FOSG.Values
import GameTheory.Languages.Bridges.FOSG.AugmentedEFG

/-!
# GameTheory.Languages.FOSG.Theorems

Thin public theorem interface for FOSG.

This file exposes the major FOSG theorems via re-export.  Substantive
game-theoretic ports should land in the generic theorem files and then be
re-exported here.

## Headline theorems

Native FOSG semantics (`FOSG/Compile`):
- `FOSG.toKernelGameOfBoundedHorizon_outcomeKernel`
- `FOSG.toKernelGameOfBoundedHorizon_eu_eq`

FOSG → augmented-EFG bridge (`Bridges/FOSG/AugmentedEFG`), forward:
- `FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon_outcomeKernel_eq_runDist`
- `FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon_outcomeKernel_eq_nativeBounded`
- `FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon_eu_eq_native`

Inverse strategy translation and round-trip:
- `FOSG.AugmentedEFGBridge.efgToFOSGProfile`
- `FOSG.AugmentedEFGBridge.efgToFOSGProfile_translateBehavioralProfile_apply`
- `FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon_outcomeKernel_eq_efgToFOSG`
- `FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon_eu_eq_efgToFOSG`
- `FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon_udistPlayer_eq_efgToFOSG`

Native FOSG Kuhn (`FOSG/Kuhn`):
- behavioral ↔ mixed equivalence on legal FOSG profiles, exposed both as a
  native theorem and via the `ObsModelCore` bridge.
-/
