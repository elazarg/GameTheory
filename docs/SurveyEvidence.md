# Equilibrium information levels: GameTheory survey

Nov 10, 2026 · @Elazar Gershuni

Most GameTheory solution concepts only need a per-player comparison of the status quo against one deviation, yet many are stated with real-valued expected utility. The gap is largest in the language bridges and the Protocol/EFG family, where theorems that hold for every preference on outcome laws are proved only for expected utility.

## Vocabulary

An equilibrium check asks one thing per candidate: is there a move, owned by some judge, that the judge counts as a gain? Everything stored beyond that answer either enables more questions or enforces consistency. Six independent axes describe what is stored; the judgment ladder is the main one.

### Judgment ladder: how a move is judged

| Level | Stored information | First question it enables | Typical consumer |
| --- | --- | --- | --- |
| Verdict | a predicate on candidates | is this candidate an equilibrium? | nothing else |
| Menu | a choice function, menu to chosen subset | blocking by sets, substitutability | contract stability |
| Better-move | a relation "this move is profitable" | improvement paths | finite improvement property |
| Stay-vs-move | per judge, the incumbent compared with one deviation | no profitable deviation | Nash, correlated equilibrium, DSIC |
| Pairwise | per judge, any two outcomes compared | best response, dominance, strictness | iterated elimination |
| Order | Pairwise plus transitivity, totality or antisymmetry | chains, argmax | simulations, Gale–Shapley |
| Mixable | a relation on outcome laws that respects mixing; no numbers | closure under mixing, mixed dominance | correlated-equilibrium convexity |
| Score | values in an ordered type | monotone re-encoding of values | ordinal invariance |
| Slack | values in an ordered additive monoid | ε-approximation | ε-Nash transport |
| Cardinal | values in ℝ or an ordered vector space | differences, scaling, integrals | envelope theorem, Groves |
| Expected | outcome laws plus a utility, combined by expectation | dynamic consistency, interim decomposition | one-shot deviation principle |
| Law-only | outcome laws; the utility is quantified in the statement | "for every payoff" results | Kuhn, law simulations |

The ladder branches. Mixable needs no numbers, while Score, Slack and Cardinal add them; both branches meet at Expected. Law-only stores the same laws as Expected but removes the utility from the data, so a Law-only theorem implies the Expected one for every utility. Menu sits beside Better-move: a choice function judges sets of contracts, not single moves.

A bare relation is not automatically Stay-vs-move. It is Stay-vs-move when the library only ever applies it to (incumbent, deviation) pairs, whatever its type says.

### Other axes

| Axis | Options | Example |
| --- | --- | --- |
| Arena: where states and moves live | Shared arena (one type for candidates and deviation targets); Gated arena (one type plus a validity predicate on candidates); Split arena (separate candidate and outcome types); Moves-as-data (a type of moves per judge and candidate, with a target map) | correlated equilibrium's moves are maps of the own recommendation, not outcomes |
| Gate: validity of candidates | integrability, Bayes consistency, feasibility, restricted report sets | weak PBE's Bayes-consistency filter |
| Judges: who evaluates a move | Players; Indexed judges (player × type, player × recommendation, root × player); Coalition moves (several judges on one move, unanimous gain required); Unjudged (one planner) | interim Bayesian optimality judges per (player, type) |
| Sharing: what judges have in common | Private scales; Common scale (sums across players); Common score (one function for all: potential, team games) | price of anarchy needs a Common scale |
| Derivation: where moves and values come from | product decomposition of profiles; game tree or information structure; values factored through outcome laws | unilateral replacement in `Π i, A i` |
| Space: structure on states | topology, convexity, measurability, finiteness, lattice order | Kakutani, Tarski |

## Where GameTheory's concepts sit

GameTheory's core is already split along these axes: `GameForm` is utility-free (`play : Profile → PMF Outcome`), `Ranking` is a bare relation with laws as named hypotheses (`Core/Rank.lean:26`), and `DeviationScheme` has an arbitrary deviator index with moves as data (`Core/Deviation.lean:40`). `IsEquilibrium` (`Core/Deviation.lean:126`) applies the relation only as `weaklyPrefers who (law of statusQuo) (law of deviation)`, so every concept defined through it is Stay-vs-move.

Paths are relative to `GameTheory/GameTheory/`. "Needs" is what the statement and proof use; "Stated at" is what the signature demands.

### Strategic-form concepts

| Concept | Anchor | Stated at | Needs | What forces the level |
| --- | --- | --- | --- | --- |
| `IsNash` | `Core/Equilibrium.lean:198` | Pairwise relation on laws | Stay-vs-move; Derivation: product | `Profile.update` |
| `IsCorrelatedEq`, `IsCoarseCorrelatedEq` | `Core/Equilibrium.lean:209`, `:204` | Pairwise | Stay-vs-move; Moves-as-data | CE and CCE differ only in the move type, never in judgment |
| `IsCorrelatedEq.mix` | `Core/Equilibrium.lean:357` | Mixable (`Preference.Convex`) | Mixable | mixing two status-quo laws |
| `IsStrongNash` | `Core/Equilibrium.lean:216` | Coalition moves via `Preference.coalition` | Stay-vs-move with "some member" aggregation | the "no member strictly gains" iff (`:273`) adds totality |
| `IsBestResponse` | `Core/Response.lean:40` | Pairwise | Pairwise | compares a candidate with an alternative, neither the incumbent |
| `StrictlyDominates` and `.trans` | `Core/Response.lean:94`, `:512` | Pairwise | Pairwise; Order for `.trans` | uses both directions; transitivity for chains |
| `IsStrictNash` | `Core/Response.lean:138` | Expected (ℝ) | Stay-vs-move with strict comparison | only `<` is used |
| `ImprovingStep`, `WeaklyAcyclic` | `Core/Response.lean:148`, `:160` | Expected plus integrability | Better-move; Shared arena | `ReflTransGen` over profiles |
| `IsOrdinalPotential.exists_isNash` | `Core/Potential.lean:103` | Expected; potential in ℝ | Better-move plus a Common score into a finite linear order | `Set.exists_max_image` |
| `IsExactPotential` | `Core/Potential.lean:39` | Cardinal | Cardinal; Common score | subtraction |
| `IsεNash` | `Core/Approximate.lean:29` | Expected | Slack | additive slack; works because `IsEquilibrium` is Stay-vs-move, so a non-transitive ε-relation plugs in |
| `StrictlyDominatedByMixed.not_isBestResponse` | `Core/Rationalizability.lean:146` | Expected | Mixable (betweenness) | a mixture of laws each below a base stays below it |
| `isNash_mixed_iff` | `Core/Utility.lean:319` | Expected | Mixable | bind-linearity of the payoff |
| `IsNash.expectedUtility_eq_of_mem_support` | `Core/Mixed.lean:189` | Expected | Cardinal | real equality across the support |
| `exists_isNash_mixed` | `Analysis/Nash.lean:239` | Expected | Expected; Space: compact convex, Kakutani | best-reply sets are convex because expected utility is affine |
| `IsSmooth.coarseCorrelated_bound` | `Analysis/RobustWelfare.lean:127` | Cardinal, Expected | Cardinal; Common scale | welfare sum over players |
| `IsESS` | `Evolutionary/Basic.lean:164` | ℝ | Score for the definition, Cardinal for `isESS_iff_small_invasion` | the iff mixes (1−ε)a + εb |

### Extensive form, protocols and bridges

| Concept | Anchor | Stated at | Needs | What forces the level |
| --- | --- | --- | --- | --- |
| `IsSubgamePerfect` | `Protocol/SubgamePerfect.lean:258` | Expected via `Context` (ℝ, EReal) | Pairwise on continuation laws; Indexed judges (root × player) | compares two laws per (root, player) |
| one-shot deviation principle | `Protocol/SubgamePerfect.lean:480` | Expected | Expected | local gains chained through the backward law |
| `exists_isSubgamePerfect` (Zermelo) | `Protocol/Zermelo.lean:927` | Expected | Order without chance nodes; Expected with them | `Finite.exists_max` on a real choice value |
| `IsSequentiallyRational` | `Protocol/BehavioralAssessment.lean:189` | Expected | Pairwise once the belief is fixed | belief mixed in by `Context.ofBelief` |
| `IsWeakPBE` | `Protocol/WeakPBE.lean:36` | Expected | as above, plus a Gate (Bayes consistency) | reach-weight ratios |
| `IsConditionalPBE` | `Protocol/ConditionalPBE.lean:79` | Expected | a Gate that is an existential over a conditional probability system | not local to the candidate |
| `IsLocallyOptimal.of_outcome_coverage` | `Protocol/ContextTransport.lean:22` | Expected | Law-only | hypotheses are law equalities |
| Kuhn Nash transfer | `Languages/EFG/Kuhn.lean:228`, `:254` | Expected (`euPreference`) | Law-only | proof is `congrArg₂ (euPreference utility who)` on equal laws |
| `isNash_native_iff_compiled` (MAID) | `Languages/MAID/Strategic.lean:451` | Expected, through ε = 0 | Law-only | `native_play_eq_compiled_play` is an exact law equality |
| `isNash_serialized_iff_source` (FOSG) | `Languages/Bridges/FOSGToEFGStrategic.lean:265` | Expected, through ε | Law-only | laws equal after erasure; deviations in bijection |
| `isNash_toProtocolForm_iff` (Bayesian) | `Languages/Bayesian/Strategic.lean:111` | Expected | Law-only | laws equal up to `map some` |
| `isNash_iff_interim` | `Core/BayesianEquilibrium.lean:418` | Expected | Expected; changes Judges from Players to (player × type) | division by the type-fibre mass |

### Cooperative games, matching, mechanisms

| Concept | Anchor | Stated at | Needs | What forces the level |
| --- | --- | --- | --- | --- |
| `IsInCore` | `Core/Coalitional.lean:94` | Cardinal | Stay-vs-move per coalition; Common scale | transferable utility turns a coalition into one judge |
| `isBalanced_iff_core_nonempty` | `Cooperative/Balancedness.lean:183` | Cardinal | Cardinal; Space: finite | LP duality |
| matching `IsStable` | `Cooperative/Matching/Capacitated.lean:58` | Pairwise (bare `Ranking`) | Coalition moves (pairs); Pairwise | both partners must strictly prefer |
| `deferredAcceptance_proposerOptimal` | `Cooperative/GaleShapley/Optimality.lean:106` | Order | Pairwise, not rooted | compares two stable matchings |
| `exists_stable` (Gale–Shapley) | `Cooperative/GaleShapley.lean:574` | Order (linear) | Order (linear); Space: finite | a strict top choice |
| `weaklyMonotone_of_isDSIC` | `Mechanism/QuasiLinear.lean:92` | Cardinal | Cardinal; Derivation: quasilinear | two IC constraints added so payments cancel |
| `groves_truthful` | `Mechanism/Groves.lean:92` | Cardinal | Cardinal; Common scale | sum of others' values |
| `revelation_principle` | `Mechanism/Revelation.lean:77` | Expected with a PMF prior | Stay-vs-move | composing a strategy into the mechanism |
| `IsEnvyFree` | `Mechanism/FairDivision/Basic.lean:50` | Cardinal, additive valuations | Stay-vs-move; Moves-as-data (move = another agent's bundle) | comparing own bundle with one other bundle |
| Gibbard–Satterthwaite | `Core/GibbardSatterthwaite.lean:801` | Order (linear) | Order; Indexed judges (voter × profile) | the type space is the set of linear orders |

## Stored above need

The largest cost is in the language bridges: five bridges prove exact outcome-law equality, which is a Law-only fact, and then conclude only for expected utility. Items marked (checked) were read directly for this report; the others come from the survey agents' reads.

### 1. Bridges conclude at Expected but prove Law-only (checked for Kuhn and MAID)

The Kuhn transfer `isNash_toMixed_of_isNash_behavioral` (`Languages/EFG/Kuhn.lean:228`) takes `utility : G.History → ι → ℝ` and `euPreference utility`. Its proof never looks inside the preference:

```lean
have hrelation := congrArg₂ (euPreference utility who)
  hbaseLaw.symm hdevLaw.symm
exact hrelation.mp (hnash who ...)
```

`congrArg₂` works for any function of two laws, so the same proof proves the result for every `WeakPreference`. The MAID bridge is less direct: exact Nash goes through ε-Nash at ε = 0 (`Languages/MAID/Strategic.lean:466`, `rw [isNash_iff_isεNash_zero, ...]`), although `native_play_eq_compiled_play` is an exact law equality. FOSG → EFG, Bayesian → protocol and NFG → FOSG follow the same pattern.

**Alternative.** One generic lemma covers all five: if base laws are equal and deviations correspond with equal laws, `IsEquilibrium` transfers both ways for any preference. Sketch only, not compiled:

```lean
theorem isEquilibrium_iff_of_law_eq
    (pref : WeakPreference Deviator O)
    (hbase : F.outcomeLaw p = G.outcomeLaw q)
    (e : ∀ who, D.Dev who ≃ E.Dev who)
    (hdev : ∀ who d,
      F.outcomeLaw (D.apply p who d) =
        G.outcomeLaw (E.apply q who (e who d))) :
    IsEquilibrium F pref p D ↔
      IsEquilibrium G pref q E
```

Each bridge then supplies its law equality and its deviation bijection, which it already proves.

### 2. The Protocol layer fixes real utility (checked)

`Context` (`Protocol/Context.lean:27`) bundles `outcome : Choice → PMF Outcome` with `continuation : Outcome → ℝ`, and `IsLocallyOptimal` compares extended expectations in EReal. Subgame perfection, sequential rationality and both PBE variants inherit this. As definitions they compare two continuation laws per (root, player), which is Pairwise. Expected is earned only by the one-shot deviation principle, ex-ante/interim equivalence, and chance nodes in Zermelo.

**Alternative.** Parameterize `Context` by a relation on `PMF Outcome`, and keep an expected-utility specialization for the theorems that chain local gains. The definitions then match `IsEquilibrium`, and SPE could be stated through it if the outcome records the continuation law per root.

### 3. Ordinal results stated in expected utility

Score is almost never used on its own: the library goes from relations straight to Expected. Examples:

- `IsStrictNash` (`Core/Response.lean:138`) uses only a strict comparison.
- `ImprovingStep` and `WeaklyAcyclic` (`:148`, `:160`) need a Better-move relation, yet require real expected utility plus integrability.
- `IsOrdinalPotential.exists_isNash` (`Core/Potential.lean:103`) needs a potential into a finite linear order; it uses ℝ.
- `IsεProper` (`Core/Proper.lean:32`) uses expected utility only through `<`; its ε bounds probabilities, not values.
- The ESS definition (`Evolutionary/Basic.lean:164`) uses ≥, = and > only.

**Alternative.** State these over `Ranking` with its `strict` part, as `IsBestResponse` and dominance already are.

### 4. Mixable results stated in expected utility

`Preference.Convex` already exists and drives `IsCorrelatedEq.mix` (`Core/Equilibrium.lean:357`). Three results need only that kind of hypothesis but are stated at Expected:

- `StrictlyDominatedByMixed.not_isBestResponse` (`Core/Rationalizability.lean:146`) uses `extendedExpect_bind_le`: a mixture of laws, each below a base, stays below it. That is betweenness.
- `isNash_mixed_iff` (`Core/Utility.lean:319`) uses bind-linearity to reduce mixed deviations to pure ones.
- `IsNash.survivesCorrelatedElimination` (`Core/Rationalizability.lean:444`) for the same reason as the first.

**Alternative.** Name a betweenness law beside `Preference.Convex` and state these three under it. Expected utility then becomes one instance.

### 5. The product decomposition is hard-wired (checked)

`DeviationScheme` stores `members : Deviator → Finset ι` and acts on subprofiles (`Core/Deviation.lean:40`). A deviation that is not a coordinate rewrite cannot be expressed, and repeated games use `recordProfile` with `Outcome :=` the whole profile as a workaround (`Analysis/Repeated/Folk.lean:41`). Deterministic games also pass through `PMF.pure`.

**Alternative.** Make the scheme an arbitrary law transformer per deviator, with the product-based scheme as a constructor. This trades the subprofile locality lemmas for generality.

### 6. Smaller items

- `EFG.Game.treeShaped` (`Languages/EFG.lean:34`) is used only for `historyFintype`; SPE, Kuhn and Zermelo do not use it.
- MAID `Semantics` carries `utility` into a play law that never reads it.
- Zermelo's `PayoffIntegrable` covers every chooser, more than the deterministic case needs.
- `IsStrategyproof` (`Mechanism/Strategyproof.lean:31`) uses `PMF.pure` and expected utility for a deterministic map; Stay-vs-move suffices.
- `IsEnvyFree` (`Mechanism/FairDivision/Basic.lean:50`) uses additive real valuations; envy-freeness and EF1 need only a per-agent relation on bundles. Proportionality genuinely needs additivity.

## Concepts outside the one-step scheme

Coalition moves are the one systematic misfit that a library change could absorb; the rest are different kinds of objects. The table says what each concept is instead and whether a custom judge index or relation makes it fit.

| Concept | Anchor | What it is instead | Can it be made to fit? |
| --- | --- | --- | --- |
| Strong Nash | `Core/Equilibrium.lean:216` | a move carries a coalition; blocked unless every member strictly gains | Yes, already: `Preference.coalition` aggregates by "some member weakly prefers the status quo". The equivalence with "not all gain" needs totality. |
| Matching stability | `Cooperative/Matching/Capacitated.lean:58` | a blocking pair: two judges must both strictly prefer | Yes, with the pair as judge and its gain as the conjunction of two strict comparisons |
| Transferable-utility core | `Core/Coalitional.lean:94` | coalition blocking | Fits only because a sum collapses the coalition to one judge; the non-transferable core is the Coalition-moves pattern again |
| Iterated elimination | `Core/Response.lean:121`, `:132` | a decreasing ℕ-indexed sequence of allowed sets | No; each round is Pairwise, the concept is the limit of rounds |
| ESS | `Evolutionary/Basic.lean:164` | Nash plus a second-order test that applies only on ties | No; it compares `payoff r m` with `payoff m m`, neither the incumbent's outcome |
| Bellman equilibrium | `Stochastic/OneStep.lean:56` | part of the candidate (the value function) is pinned by an equation | Partly: the statewise Nash part fits with judges (state × player) |
| Trembling-hand perfect, proper | `Analysis/TremblingHand.lean:60`, `Analysis/Proper.lean:30` | limits of equilibria of perturbed games | The perturbed equilibrium fits (`IsEquilibrium` with a subtype move scheme); the limit does not |
| Learning dynamics | `Analysis/Learning.lean:458` | convergence of a process | Conclusions are ordinary `IsNash` or ε-CCE |
| Shapley value | `Core/Shapley.lean:1099` | axioms characterizing a map from games to allocations | No judge index helps |
| Nash bargaining | `Cooperative/Bargaining.lean:72` | maximizing a product of gains | Unjudged: one social maximization |
| Epistemic agreement | `Epistemic/Agreement.lean:167` | posteriors and partitions, no preferences | Outside the scheme |

## Arrows between levels

GameTheory's arrows mostly change the judge index or the move scheme, not the judgment level; the level-raising arrows each cost expected utility. An arrow here is a theorem that turns a result at one level or index into a result at another.

| Arrow | Anchor | From | To | What it costs |
| --- | --- | --- | --- | --- |
| best response at the incumbent equals Nash | `isNash_iff_isBestResponse`, `Core/Response.lean:219` | Pairwise | Stay-vs-move | nothing; holds for any relation |
| CE implies CCE | scheme homomorphism transport | one move scheme | a coarser one | nothing; holds for any relation |
| ex-post Nash implies Bayes–Nash | `IsExPostNash.isNash`, `Core/BayesianEquilibrium.lean:434` | Judges (player × type profile) | Players with a prior | monotonicity of expectation |
| ex-ante equals interim | `isNash_iff_interim`, `Core/BayesianEquilibrium.lean:418` | Players | Indexed judges (player × own type) | Expected: division by fibre mass |
| mixed equals behavioral laws | `kuhn_mixed_to_behavioral`, `Languages/EFG/Kuhn.lean:129` | one game form | another | perfect recall; Law-only |

**Missing.** A generic Law-only bridge lemma (see Stored above need, item 1) would replace five specialized proofs. A betweenness law on preferences would give a Mixable rung between Order and Expected. Utility-representation arrows (from an order to a score) were not surveyed in GameTheory.

## Design options for GameTheory

The survey supports a small number of named judgment levels, each with its own theorems, rather than one structure per concept. These are options, ordered by how much existing code they touch.

1. **Generic Law-only bridge.** One lemma for law equality plus deviation correspondence; each language bridge supplies its two facts. Touches only the bridge files; the Expected and ε versions become corollaries.
2. **Betweenness beside `Preference.Convex`.** Restate mixed dominance, `isNash_mixed_iff` and the rationalizability inclusions under it. Expected utility becomes an instance.
3. **Ordinal restatements.** State strict Nash, improvement paths, ordinal potentials and ε-proper over `Ranking`. The real-valued versions remain as instances.
4. **Relation-valued `Context`.** Let the Protocol layer take a relation on continuation laws, and keep the expected-utility version for the one-shot deviation principle, interim equivalence and Zermelo with chance. This aligns SPE and PBE with `IsEquilibrium`.
5. **First-class coalition moves.** A move that carries its coalition, judged by strict unanimity over it. Strong Nash, matching stability and a non-transferable core would share it.
6. **Product as a constructor, not a field.** Generalize `DeviationScheme` to arbitrary law transformers. This is the most invasive option and loses subprofile locality, so it needs a client first.

The common thread is the Kuhn proof: when a proof never inspects the preference, its statement should not fix one.

## Method and unverified items

About 80 GameTheory definitions and theorems were classified by reading their statements and proofs; nothing was built. The sample covers `Core`, `Analysis`, `Evolutionary`, `Stochastic`, `Repeated`, `Languages`, `Protocol`, `Cooperative` and `Mechanism`, and excludes `Experimental`, `Tests` and `Examples`. A companion survey of MathEconLib uses the same vocabulary.

Checked directly for this report: `Ranking`, `DeviationScheme`, `IsEquilibrium`, `Context`, the Kuhn proof, and the MAID ε = 0 route. The following rest on the survey reads and should be confirmed before acting on them:

- that the one-shot deviation principle genuinely needs Expected, inferred from its statements rather than a line-by-line read of the proof;
- that `treeShaped` is unused outside `historyFintype`;
- that the FOSG and Bayesian bridges admit the generic lemma without extra coherence conditions;
- the line numbers in the evidence tables, which were collected by the survey agents.
