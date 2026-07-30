# D15: normal-form and factored-observation language surfaces

- **Status:** adopted; experimental one-shot transfer passes, promotion
  unblocked
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-042

## Decision / question

How deterministic normal-form syntax and factored-observation stochastic games
should meet the already-adopted static and sequential semantics, and whether
the frozen T4 NFG-to-FOSG commuting theorem survives that layering.

## Competing designs

1. Give NFG and FOSG independent strategic forms, histories, utilities, and
   solution predicates, then relate them by a generic morphism.
2. Make NFG a deterministic frontend to `GameForm`; make FOSG a transparent
   pairing of `ExecutionProtocol` with its `InformationModel`; prove the named
   one-shot transfer directly through the canonical Protocol compiler.
3. Sequentialize the simultaneous NFG action profile through the single-mover
   tree/EFG frontend.
4. Keep NFG solely as direct static examples and retire the FOSG transfer.

Design 2 is adopted. Design 1 conflicts with D4–D7 by duplicating accepted
semantics. Design 3 was already refuted by D6:
`sequentialization_enlarges_strategy_space` exhibits a contingent target plan
that simultaneous play does not possess. Design 4 remains the fallback only if
the direct general-state transfer later fails its exact law.

## Representative hostile slice

EXP-042 uses two real source players with Boolean actions. Both are active at
the target's single initial state, and the terminal outcome records both
actions. Changing only the column player's action changes the outcome while the
row player's phase-only information state and lifted action remain unchanged.

The generic theorem lifts an arbitrary source profile, runs the actual
information-local Protocol history evaluator for one step, maps the terminal
history back to the source outcome, and proves equality with the deterministic
source `GameForm.play`. A second theorem maps an arbitrary external utility
over both laws and proves equality of the joint utility distributions.

## Measurements

| Measure | EXP-042 result |
|---|---|
| authored size | 401 nonblank lines; 42 declarations across compiler and hostile test |
| stable API change during experiment | 0 declarations and 0 imports |
| authored import | `GameTheory.Protocol.Strategic` only |
| focused build | 1,722 jobs |
| full build | 3,339 jobs |
| source trust/audit tokens | 0 placeholders, native decisions, direct updates, transports, `HEq`, tactic `change`, custom axioms, or `open Classical` |
| repository audits | Phase 2 and Phase 3 expected source measurements pass; full reachability is rerun after promotion |
| axiom profile | `propext`, `Classical.choice`, `Quot.sound` only |
| target evaluator | existing `InformationModel.run` through `toGameForm`; no FOSG runner |
| target players/actions | definitionally the source players and source action family |
| horizon/progress capabilities | horizon fixed by the named compiler; `Nonempty` actions requested only by execution construction |
| simultaneous/locality probe | both players active together; changing the opponent's current action leaves the row policy action unchanged |
| exact laws | generic outcome-law and arbitrary-utility-law equalities |

## Kill condition

Reject the design if it needs a synthetic player, sequentially observable
current action, padding/default action, target policy access to execution state,
duplicated transition/history/equilibrium semantics, utility stored in
execution syntax, a generic certificate hierarchy needed only to package the
direct theorem, stored finite capabilities, direct `Function.update`,
user-visible equality transport, or an unequal actual compiled target law.

No kill condition fired.

## Result

Adopt utility-free `NFG.Game` as deterministic syntax compiling to the
canonical `GameForm`. Finiteness, utility, and executable algorithms remain
operation-local. No NFG-specific Nash or deviation API is permitted.

Adopt `FOSG.Game` as the transparent general sequential specialization:
one accepted execution protocol together with its information model. Unlike
EFG it adds no single-mover or tree-shaped law; simultaneous action is native.
It owns no evaluator, history, strategy, utility, or solution concept separate
from Protocol and Core.

Adopt the one-shot NFG-to-FOSG compiler as a named bridge. Its terminal state
retains the source profile, its public signal exposes only the completed phase,
and its private signal is trivial. The direct outcome theorem is T4's
certificate; the predecessor's generic morphism wrapper is retired under D7.
The explicit arbitrary-utility consequence credits the frozen utility-law
claim without putting utility into language syntax.

Promotion must split syntax, FOSG specialization, and the named bridge into
separate modules so import probes can verify the intended boundaries. The
hostile fixture remains experimental.

