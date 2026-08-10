# GameTheory 2: Greenfield Design and Fast Falsification Plan

Status: design RFC for a rewrite from scratch
Date: 2026-07-22

## 1. Purpose

This document specifies a greenfield architecture for a second GameTheory
library and, equally importantly, a cheap way to discover that any proposed
decision is wrong.

This is not a migration plan. It assumes:

- no source compatibility;
- no preservation of existing declaration names;
- no obligation to reproduce the existing module graph;
- no adapters whose only purpose is moving old proofs into the new library;
- no broad theorem port until the architectural spikes below have passed.

The choice to authorize a rewrite rather than refactor the existing library is
an external premise of this RFC. A separate project-decision document may
compare those options using the existing library as evidence; this document
answers the narrower question, "given a rewrite from scratch, what should be
built?" It therefore does not introduce transitional implementations or
compatibility work as validation paths.

The target is a theorem library for finite and discrete game theory with:

- a small stochastic strategic-form semantic core where it demonstrably avoids
  duplicated concepts or proofs;
- retained operational/information semantics for sequential languages;
- equilibrium concepts defined once from preferences and deviations, with
  profile-quantified response concepts defined once at their own logical shape;
- a computable finite-table frontend for concrete examples;
- explicit boundaries around countable probability, continuous probability,
  infinite-path probability, fixed-point analysis, and research-frontier
  formalisms.

The rewrite succeeds only if it makes representative proofs shorter, APIs
harder to misuse, and architectural rules mechanically visible. A prettier
directory tree is not sufficient.

EconCSLib is useful external evidence for this RFC, but not a precedent to copy
uncritically. Its public library is early-stage and its own paper describes
coverage as uneven. Its strongest evidence concerns local assumptions,
executable checkers, package discipline, and counterexample-driven API repair.
Its game-bound profiles, duplicate mixed-game APIs, and incomplete sequential
semantics are counterexamples that the spikes below must catch. See its
[design guide](https://github.com/gametheoryinlean/EconCSLib/blob/main/docs/design.md),
[implementation](https://github.com/gametheoryinlean/EconCSLib), and
[architecture paper](https://arxiv.org/html/2606.16144).

## 2. Design principles

1. **Put semantic invariants in types or first-class certificates.** Directory
   placement and prose may explain a boundary, but must not be the only thing
   enforcing it.
2. **Define a concept at the lowest sufficient semantic layer.** Outcome-law
   Nash belongs on a game form plus preferences. Perfect recall does not.
3. **Prefer one generic definition plus transparent specializations.** Avoid a
   second logical definition merely to provide a familiar name.
4. **Separate proof semantics from executable presentations.** Mathematical
   generality and reliable `#eval` are different products and should meet at a
   proved refinement boundary.
5. **Generalize only after two concrete implementations expose the same
   interface.** In particular, do not invent a universal probability monad or
   category-theoretic framework speculatively.
6. **Every foundational choice needs a kill test.** If a small vertical slice
   falsifies the expected benefit, replace the design before porting breadth.
7. **Distinguish trust, completeness, and API stability.** A file can contain no
   `sorry` and still expose a semantic stub; a well-typed open problem is not a
   proved library fact.

## 3. Candidate stratified semantic tower

```text
Language syntax
      |
      v
Native operational semantics
      |
      +---- protocol-adequacy certificate ----+
      v                                        v
Execution protocol <---- Information model    retained sequential semantics
      |                       |
      +-----------+-----------+
                  |
                  +---- strategic-adequacy certificate
                  v
            Strategic GameForm
                  |
      +-----------+-----------+
      |                       |
Weak preference          Utility evaluation
      |                       |
      +-----------+-----------+
                  |
       Equilibrium and response concepts
```

This diagram is the default **hybrid candidate**, not a premise. D0 compares it
against a universal hub and coordinated domain branches with only bespoke
bridges. If the hybrid survives, `GameForm` is the common target for outcome-law
concepts. It is not claimed to retain enough structure for recall, subgames,
sequential rationality, or causal claims. Sequential languages retain their
protocol semantics and expose a forgetful compilation to `GameForm` only when
that compilation supports named downstream theorems.

Coalitional games, matching, and bargaining remain a parallel semantic branch.
The foundational characteristic-function game and its core live in
`GameTheory.Core.Coalitional`; they do not acquire artificial strategy profiles
merely to fit this diagram. Larger cooperative developments may still warrant
their own dependency root.

Finite hidden-action contracts are likewise native to the opt-in mechanism
branch.  D32 represents each action by its own finite-support outcome law and
states agent optimality and explicit participation directly; it does not add
dummy strategic players merely to reuse `GameForm`.

Quasilinear direct mechanisms also have a capability-free native owner in the
opt-in mechanism branch.  D33 stores only report types, valuations, allocation,
and payments; it compiles to the canonical Bayesian direct-mechanism language,
defines DSIC transparently through that language's incentive-compatibility
predicate, and derives weak monotonicity by cancelling payments.  Groves/VCG,
affine-maximizer, and Myerson structures are consumers of this owner rather
than fields forced into its foundation.

## 4. Decision summary

| ID | Current/default decision | Status | Fastest serious test |
|---|---|---|---|
| D0 | Share static forms, incentive logic, and one execution base; use direct named bridges | Final | Mine the existing hub, price direct bridges, and prototype only the hybrid |
| D1 | Bind profiles to a signature and store that signature in each form | Decided | Implement six core operations in indexed and bundled-signature prototypes |
| D2 | Represent finite-support laws by a finite-support `PMF` subtype | Adopted | Compare a finite-support `PMF` subtype with normalized `Finsupp`, including their finite-carrier simplex bridge |
| D3 | Do not introduce a generic probability-monad class in the baseline | Adopted | Revisit only after a second probability model shares three nontrivial theorems |
| D4 | Separate `GameForm`, preferences, and utility evaluation | Adopted | Define Nash, CE, welfare, and utility invariance without duplicate predicates |
| D5 | Define equilibrium once from local, law-linear deviations; keep profile-quantified response concepts distinct | Accepted | Express five equilibria plus best response, dominance, and one Bayesian slice |
| D6 | Keep execution and information separate; use general-state execution primarily and finite trees as a derived presentation | Decided | Compare both execution orders on terminal, chance, locality, and assessment tests |
| D7 | Use direct named bridges; add no semantic certificate hierarchy in the baseline | Rejected for the baseline | Compare certificate composition with a bespoke direct-bridge baseline |
| D8 | Keep only a minimal transformation taxonomy | Adopted | Prove relabeling, reindexing, mixed lifting, and equilibrium transport |
| D9 | Treat finiteness as independent capabilities | Adopted | Audit assumptions in the vertical slices |
| D10 | Add a separate rational, finite, executable frontend | Adopted | `#eval` pure Nash/dominance and prove the output specification |
| D11 | Keep measurable and infinite-path probability outside the baseline | Adopted | A later isolated measurable-kernel spike may reopen this decision |
| D12 | Split general mathematics, challenges, and frontier research from the stable core | Adopted | Enforce trust, dependency, documentation-sync, and cold-build tests |

## 5. Core decisions and falsification plans

### D0. Compete a universal hub, coordinated branches, and a stratified hybrid

The rewrite must not assume that cross-representation unification repays its
cost. Compare three architectures:

1. **Universal hub:** every game representation compiles to one semantic game
   object, and most concepts and transfers are stated there.
2. **Coordinated branches:** strategic, extensive, graphical, and other games
   share only foundation vocabulary; bridges are added directly for particular
   theorems.
3. **Stratified hybrid:** static outcome-law semantics share
   `GameSignature`/`GameForm`; sequential languages retain native protocols;
   named protocol, strategic, and incentive certificates support only the
   transfers that need them.

The provisional favorite is the stratified hybrid. EconCSLib demonstrates that
coordinated branches plus a few bespoke bridges can support broad subject
coverage, but it does not demonstrate deep cross-language theorem reuse. The
existing GameTheory library supplies the opposite evidence: substantial Kuhn,
EFG, MAID, FOSG, and observation-model results, but also substantial bridge
maintenance. D0 prices that trade directly rather than deciding it from line
counts or architectural taste.

#### Validation spike

Inventory the exact existing theorems that are intended to justify shared
semantics. Use three deliberately asymmetric evidence sources rather than
reimplementing the most expensive theorem three times:

- treat the current library's `KernelGame` architecture as the completed
  universal-hub experiment and mine its imports, casts, bridge proof size,
  change concentration, and reused theorems;
- implement the theorem-specific direct bridge that a coordinated-branch
  design would actually expose, where the current library does not already
  contain one;
- build a small greenfield prototype only for the stratified hybrid, because
  that is the genuinely untested candidate.

Apply those evidence sources to:

1. pure and mixed Nash transfer through finite-tree strategic-form extraction;
2. behavioral/mixed correspondence under perfect recall;
3. one EFG/MAID or EFG/FOSG outcome-law and equilibrium transfer;
4. one language transformation commuting with compilation.

Do not attempt a second full proof of Kuhn's mixed-to-behavioral direction in
the spike. Audit the current proof's actual dependencies—including recall,
posterior locality, and reachability side conditions—then require the hybrid
interfaces to state those dependencies faithfully. Prove only smaller
representative preservation lemmas until the architecture survives that audit.
The coordinated-branch candidate must include the direct bridge it would
actually expose; the hybrid candidate may not count a certificate that merely
stores the desired theorem as a field.

Measure:

- duplicated public concept definitions and equivalence lemmas;
- bridge/certificate definitions and proof lines;
- language-specific fields or escape hatches in shared objects;
- user-visible transports and casts;
- how many evaluation-correctness facts are reused rather than reproved;
- whether two same-level transfers compose without reopening native semantics;
- the ratio of certificate payload to the native semantics it is meant to
  summarize.

#### Disproof condition

Reject the universal hub if two native languages require dummy data,
language-specific escape fields, or a hub object essentially as large as their
native semantics. Reject coordinated branches if three representative branches
duplicate the same equilibrium logic or reprove the same outcome-law transfer.
Reject a certificate level if its payload mirrors the whole source language,
if the named transfer inventory is too short to amortize it, or if a bespoke
bridge is consistently smaller and clearer without causing duplicated concepts.

D0 may select coordinated branches for protocol semantics while retaining a
shared static `GameForm`; the candidates are not required to win uniformly at
every semantic level. Phase 0 produces a provisional D0 decision and an
explicit bridge/certificate cost budget before incentive or sequential
infrastructure is built. The decision is finalized after the sequential slice
has tested the only new candidate. D7 cannot be frozen before that record
exists.

### D1. Signature-bound profiles, testing indexed against bundled signatures

The first prototype should use a signature separated from the game law:

```lean
universe uι us uo

structure GameSignature (ι : Type uι) where
  Strategy : ι → Type us
  Outcome : Type uo

abbrev Profile {ι : Type uι} (sig : GameSignature ι) :=
  ∀ i, sig.Strategy i

structure GameForm {ι : Type uι} (sig : GameSignature ι) where
  play : Profile sig → FinDist sig.Outcome
```

This keeps carrier choices explicit in result types. For example, mixed
extension returns a form indexed by a signature whose strategy family is
definitionally `fun i => FinDist (sig.Strategy i)`.

`Profile` is bound to the signature, not to the full payoff- or
preference-bearing game. Namespaces and explicit arguments may still provide
`G.Profile`-style ergonomics, but changing the play law or preference data must
not create a new profile type. EconCSLib's game-bound profile is therefore a
comparison case, not independent validation of this design.

This is not expected to eliminate all transport. Reindexing along an arbitrary
equivalence still turns `S (e (e.symm k))` into `S k`, which is propositionally,
not definitionally, equal. The hypothesis is narrower: signature indexing will
localize casts and improve reduction for map, product, mixed extension, and
heterogeneous transformations.

Do not make games typeclass instances. Multiple games routinely share the same
player, strategy, and outcome carriers, so instance search cannot select a
canonical game.

#### Validation spike

Implement the following twice: once with the indexed signature above and once
with a bundled form that stores `sig : GameSignature ι` as a field. In the
second candidate, `Strategy` and `Outcome` are still owned by `sig`; they are not
independent payoff-bearing game fields.

1. player reindexing along `ι ≃ κ`;
2. outcome mapping;
3. product of forms;
4. mixed extension;
5. heterogeneous form-homomorphism composition;
6. unilateral profile update and its simp API.

Also construct two forms with the same signature but different outcome laws and
preferences. A profile, mixed profile, and profile-update theorem must be usable
for both without conversion or restatement.

Exercise both versions in downstream-only stress files modeled on real usage:
an NFG mixed extension, a player-reindexed language compiler, an outcome
relabeling, and a heterogeneous game equivalence. The existing library may
supply representative shapes and pain points without becoming a compatibility
target.

Measure:

- source-level explicit `cast`, `Eq.ndrec`, `Eq.mpr`, `HEq`, and `change`
  occurrences outside the signature/transport module;
- number of custom projection simp lemmas;
- proof lines for associativity and identity laws;
- elaboration time for a file composing all six operations;
- declaration signatures as seen by a downstream user.

#### Disproof condition

Reject parameter indexing if it does not materially reduce
transport/projection plumbing outside the transport module, or if ordinary
theorem signatures become materially harder to infer and read. The
"at least half" ratio is a quantitative gate only when the baseline contains at
least ten source-level occurrences; at smaller counts, use absolute counts and
a downstream API review. A form storing a bundled signature remains a valid
fallback. Binding profiles to the whole play/payoff object is not a fallback:
the two-law reuse test above makes signature ownership an independent
invariant. This decision must be made from the spike, not aesthetics.

### D2. Finite-support probability and its concrete representation

The default game form uses a finite-support distribution on an arbitrary
carrier. The carrier itself need not be finite.

The largest immediate payoff is that real expectation becomes unconditional:
every observable is summable on the law's finite support. The core should not
need parallel bounded-utility lemmas merely to justify bind, map, or payoff-law
transport.

Finite support also gives:

- lawful finite bind and map;
- unconditional real expectation for arbitrary utilities on the finite
  support;
- finite-support mixed strategies over countable or infinite action carriers;
- no silent interpretation of a nonsummable real series as an expected payoff.

The main API should distinguish these notions:

```text
finite support of a particular law  -- built into FinDist
finite player carrier               -- needed for independent products
finite strategy carrier             -- needed for enumeration/existence proofs
finite outcome carrier              -- needed by particular compactness/sum arguments
countably supported probability     -- separate extension layer
```

The finite-support policy and its representation are separate decisions. Two
representations must compete before the core API freezes:

```lean
universe u

-- Candidate A: inherit Mathlib's PMF theory.
def FiniteSupportPMF (α : Type u) :=
  { μ : PMF α // μ.support.Finite }

-- Candidate B: make the finite sum explicit.
structure NormalizedFinsupp (α : Type u) where
  weight : α →₀ ℝ≥0
  mass_one : weight.sum (fun _ p => p) = 1
```

Candidate A should inherit more probability lemmas but is likely to retain
noncomputable `PMF` operations. Its weights live in `ℝ≥0∞`, so real-valued
finite expectation may expose recurring `ENNReal.toReal` plumbing even when
summability is trivial. Candidate B should expose finite sums directly but
requires a new monad-law and interoperability development. Neither is assumed
to serve D10: arbitrary real or nonnegative-real weights are not an executable
substitute for a rational distribution.

This is not a clean-room comparison. The current
`comparison corpus` already implements the `PMF` subtype
and substantial pure/map/bind/product/expectation/support theory, with further
bind, conditioning, independence, and update experience under `comparison corpus`.
Mine those proofs as measured prior art. In particular, count the actual
`toReal`, classical, support, and reducibility costs before deciding whether to
reuse, extract, or replace that implementation. The current convergence layer's
use of explicit pointwise convergence because `PMF` lacks the desired bundled
topology is also evidence for the simplex-bridge test, not a hypothetical risk.

#### Validation spike

First implement for both candidates:

1. `pure`, `map`, `bind`, product, and their laws;
2. real expectation and expectation-through-bind;
3. support lemmas used by conditioning and deviation proofs;
4. dependent finite products for finitely many players;
5. conversion to Mathlib `PMF` and preservation theorems;
6. on finite carriers, a round-trip equivalence with Mathlib `stdSimplex` that
   preserves pure distributions, products, expectation, and affine structure.

Measure:

- proof lines required for monad and expectation laws;
- source-level `ENNReal.toReal` and coercion plumbing in real expectation;
- explicit classical/noncomputable declarations;
- reduction and simp behavior of pure, bind, and mixed extension;
- interoperability proof burden with Mathlib probability;
- proof burden of reaching Mathlib's convex/topological simplex APIs;
- elaboration time on the mixed-extension and CE slices;
- whether support and expectation computations can be inspected in concrete
  examples without unfolding representation internals.

Then complete all of the following using the winning finite-support API:

1. deterministic NFG compilation;
2. an EFG with a nontrivial chance node;
3. independent mixed extension for finitely many players;
4. correlated and coarse-correlated equilibrium definitions;
5. a finitely supported mixed strategy on a countably infinite action type.

Also choose one flagship theorem from learning or repeated games and identify
whether any distribution in its statement genuinely requires infinite support
or a probability law on an infinite path space.

Then prove one finite-game Nash-existence slice through the finite-law to
`stdSimplex` equivalence. It must reuse the public mixed-profile, expected-value,
and equilibrium definitions. Introducing parallel `MixedProfile`, expected
payoff, or mixed-Nash predicates for the geometry layer fails the spike. The
probability coefficient type must not be selected implicitly from the payoff
scalar merely to make multiplication convenient.

#### Disproof condition

Reject either concrete representation if it loses its predicted advantage: a
`PMF` subtype that still requires extensive support/expectation repair, or a
normalized `Finsupp` that recreates a large probability library without
improving reduction or downstream proofs. If neither wins clearly, prefer the
`PMF` subtype for Mathlib interoperability and keep the representation hidden.

If the finite-law/simplex bridge dominates the existence proof, does not expose
the topology required by Mathlib without wrapper-breaking, or repeatedly forces
representation-level reasoning on users, consider `stdSimplex` as the
Analysis-facing representation. Even then, retain one canonical semantic
equilibrium predicate and prove a representation equivalence; do not fork the
logical API.

Do not make finite support the only semantic core if a flagship theorem needs
an infinite-support law in its statement and cannot be cleanly isolated in a
countable extension. In that event, keep distinct finite and countable forms
unless a precise shared interface has already passed D3's reopening test.

Infinite repetition has a stricter the baseline boundary. Stable repeated-game theorems
may use stagewise expected utility, deterministic paths of mixed stage
profiles, recursive/Bellman expectations, and finite-prefix distributions of
realized signals. They must not encode a stochastic law on the entire infinite
signal-history space as `FinDist` or as a merely countably supported law. Under
indefinitely nondegenerate stochastic monitoring, such a path law is generally
not countably supported. The current
`comparison corpus` presentation—an `ℕ`-indexed
path of stage profiles evaluated per round—is positive evidence for this
boundary; `comparison corpus` currently stops at
finite-prefix signal laws. Genuine path-space probability waits for D11's
measurable layer.

### D3. No generic probability monad in the first release

A `pure`/`map`/`bind` interface is not enough to support continuous games.
Continuous probability additionally needs measurable spaces, measurable
kernels, product measurability, integration, and almost-everywhere reasoning.
A small `GProb` class would conceal these obligations rather than solve them.

Therefore:

- the baseline uses a concrete finite-support probability type;
- a countable `PMF` extension may be added with explicit expectation
  hypotheses;
- continuous and infinite-path probability are a separate measurable research
  spike, not a type parameter threaded through the initial library.

#### Reopening condition

Reopen this decision only after two concrete probability implementations exist
and at least three substantial theorems—not merely monad identities—have
identical proofs modulo a proposed interface. Candidate theorems must include
one involving expectation and one involving independent products.

If the common interface requires implementation-specific side conditions in
most theorem statements, do not abstract it.

### D4. Game form, preference, and utility are separate data

The utility-free form is canonical. Preferences compare outcome laws:

```lean
universe uι

abbrev WeakPreference (Agent Outcome : Type*) :=
  Agent → FinDist Outcome → FinDist Outcome → Prop

abbrev Utility {ι : Type uι} (sig : GameSignature ι) :=
  sig.Outcome → ι → ℝ

structure UtilityGame {ι : Type uι} (sig : GameSignature ι) where
  form : GameForm sig
  utility : Utility sig
```

Expected-utility preference is derived from a `Utility`. `UtilityGame` is only
the dependent pair of a form and its evaluation; it does not repeat the form's
strategy, outcome, or play fields. Generic solution concepts continue to take
the form and preference explicitly, so bundling is an ergonomic option rather
than a second semantic definition.

Preference laws such as reflexivity and transitivity are predicates or
property structures about a particular relation. The preference itself is an
explicit argument, not a typeclass instance, because a form may be studied
under several preferences.

The argument orientation is a public invariant:

```text
weaklyPrefers i preferred alternative
```

Thus equilibrium compares `statusQuo` first and `deviated` second. Definitions
and theorem names must use `preferred`/`alternative` or
`statusQuo`/`deviated`, never anonymous `x`/`y` where reversing the relation
would silently change the concept. Reflexivity is not baked into the relation
type, but is a named property required whenever a theorem treats a no-op as an
allowed deviation.

Expected utility stays specialized to `ℝ`. Algebraic generalization of the
payoff scalar should occur theorem-by-theorem when it buys a real reuse case.
Scalar polymorphism is not allowed to choose the probability representation or
create a second mixed-game API. EconCSLib's generic finite payoff definitions
are useful evidence, but its separate rational/real mixed predicates show that
polymorphism alone does not guarantee one semantic layer.

#### Validation spike

Using one `GameForm`, define:

- ordinal Nash under an arbitrary law preference;
- expected-utility Nash as a transparent specialization;
- Pareto efficiency;
- positive-affine utility invariance;
- outcome relabeling and utility pullback.

Additionally implement the purely algebraic finite-expectation lemmas once over
the weakest practical ordered-field assumptions and instantiate them at `ℚ`
and `ℝ`. Keep this factoring only if it removes genuine duplicated lemmas
without leaking scalar parameters through ordinal preferences or probability
laws.

The expected-utility names should unfold to the general predicates or require
only one direction-free `rfl`/`simp` theorem. There should be no recurring
`IsNash_iff_IsNashFor_eu` rewrite pattern.

#### Disproof condition

Revise the separation if basic expected-utility theorem statements require
pervasive dependent projections or if type inference cannot recover the form
from an evaluation. Fix projection ergonomics before adding wrapper
definitions with duplicate logical content.

### D5. A single local, law-linear deviation predicate

The deviation type must enforce two independent invariants:

1. **law-linearity:** a deviation acts pointwise and lifts to profile laws by
   bind;
2. **information locality:** a deviating unit sees only its own recommended
   component, not the entire profile.

A candidate interface makes the affected footprint explicit and derives the
full-profile update centrally:

```lean
universe uι

variable {ι : Type uι} {sig : GameSignature ι}

abbrev Subprofile
    (sig : GameSignature ι) (members : Finset ι) :=
  (i : { i // i ∈ members }) → sig.Strategy i.1

namespace Profile

def restrict (members : Finset ι) (profile : Profile sig) :
    Subprofile sig members :=
  fun i => profile i.1

def override [DecidableEq ι]
    (members : Finset ι) (local : Subprofile sig members)
    (profile : Profile sig) : Profile sig :=
  fun i => if h : i ∈ members then local ⟨i, h⟩ else profile i

end Profile

structure DeviationScheme
    (sig : GameSignature ι) (Deviator : Type*) where
  members : Deviator → Finset ι
  Dev : Deviator → Type*
  actLocal : ∀ who, Dev who →
    Subprofile sig (members who) → FinDist (Subprofile sig (members who))

def GameForm.outcomeLaw
    (F : GameForm sig) (μ : FinDist (Profile sig)) : FinDist sig.Outcome :=
  μ.bind F.play

variable [DecidableEq ι]
variable {Deviator : Type*}

def DeviationScheme.apply
    (D : DeviationScheme sig Deviator)
    (μ : FinDist (Profile sig)) (who) (d : D.Dev who) :=
  μ.bind fun profile =>
    (D.actLocal who d (Profile.restrict (D.members who) profile)).map
      fun local => Profile.override (D.members who) local profile

def IsEquilibrium
    (F : GameForm sig)
    (weaklyPrefers : WeakPreference Deviator sig.Outcome)
    (μ : FinDist (Profile sig))
    (D : DeviationScheme sig Deviator) : Prop :=
  ∀ who d,
    weaklyPrefers who
      (F.outcomeLaw μ)
      (F.outcomeLaw (D.apply μ who d))
```

For unilateral deviations, `members who = {who}`. For a coalition, it is the
coalition's member set. The local kernel can express constant,
recommendation-dependent, and randomized replacements; its input contains no
nonmember recommendation. `Profile.override` proves once that every nonmember
coordinate remains unchanged.

If a standard solution concept truly needs law-dependent or nonlocal
deviations, that is evidence for an explicitly broader interface rather than a
silently overpowered base definition.

Instances/specializations:

| Concept | Status quo | Units | Deviations |
|---|---|---|---|
| Pure Nash | `pure σ` | players | constant unilateral replacements |
| Mixed Nash | `pure σ` in mixed extension | players | replacement mixed strategies |
| CCE | arbitrary profile law | players | constant unilateral replacements |
| CE | arbitrary profile law | players | recommendation-dependent maps |
| Strong Nash | `pure σ` | nonempty coalitions | joint member replacements |

All profile mutation goes through `Profile.update` and `Profile.override`, and
all subprofile access goes through `Profile.restrict`. Their constructive
definitions require explicit `[DecidableEq ι]` only when they branch on
membership or coordinate equality;
`Subprofile` and `Profile.restrict` do not carry that phantom instance. A
proof-only wrapper may install classical decidability locally, but the
executable frontend must always supply its genuine `DecidableEq` instance.
Direct `Function.update` use outside the profile module is an architecture
failure.

Equilibrium of a law is only one logical shape. Best response, dominance, and
rationalizability quantify over fixed or varying opponent profiles and must not
be disguised as degenerate instances of `IsEquilibrium`:

- `IsBestResponse F weaklyPrefers i opponents candidate` compares `candidate`
  with every unilateral alternative while `opponents` remains fixed;
- `WeaklyDominates F weaklyPrefers i candidate alternative` compares the two
  strategies at every opponents' profile;
- strict dominance and dominant strategies/profiles are built once from those
  profile-quantified predicates;
- EXP-073/EXP-076/D40 distinguishes correlated-belief mixed-dominator
  elimination (`correlatedSurvivors`, `IsCorrelatedRationalizable`) from the
  pure-dominator iteration (`pureSurvivors`,
  `SurvivesAllPureEliminationRounds`).  The
  Bernheim--Pearce independent-belief notion is not represented by an
  unqualified alias;
- `IsIndividuallyRational F utility reservation profile` compares an explicit
  reservation vector with the same canonical expected utilities and consumes
  Pareto improvement directly.  Mechanism participation and cooperative or
  repeated-game acceptability remain separate, timing-specific concepts.

These predicates share `GameForm.outcomeLaw`, preferences, and the profile
operations with equilibrium, but they are a separate concept family. D10's
boolean dominance and pure-elimination algorithms prove correctness against
the explicitly named pure definitions; correlated rationalizability stays
proof-semantic until a separate executable certificate gate passes.

#### Validation spike

Implement all five rows above and prove:

- pure Nash implies CCE of the point mass;
- CE implies CCE by a deviation-scheme morphism;
- dominant-strategy profiles are Nash;
- singleton coalition deviations recover unilateral deviations;
- two profiles with the same local recommendation induce the same distribution
  of local replacements;
- a deliberately malicious CE deviation attempting to inspect another
  player's recommendation is untypeable;
- randomized deviations reduce to deterministic ones in one finite linear-EU
  example;
- the profile-quantified dominant-profile predicate implies Nash, and one
  finite dominance/rationalizability checker is correct against its abstract
  predicate;
- one finite Bayesian slice expresses an interim, type-dependent deviation
  without exposing other players' types or recommendations.

The Bayesian slice is a scope probe, not a commitment to encode incomplete
information as an ordinary static form. A player's own type may be supplied as
local context or as part of its recommendation when that matches the theorem,
but interim preference and type-contingent feasibility must remain explicit.
If they do not fit without conflating types, actions, and recommendations, give
Bayesian games their own coordinated branch sharing only the appropriate
signature and preference vocabulary.

#### Disproof condition

Reject or extend the local-kernel design if a standard in-scope concept needs a
deviation depending on the full prior law or on information not expressible as
the affected subprofile, and encoding it locally changes the mathematical
statement. Add an explicitly named observation-dependent deviation interface
only for such concepts; do not weaken the standard CE interface. Reject the
single equilibrium predicate if its specializations require more boilerplate
than direct definitions and generic transport theorems do not repay that cost.
Reject any attempt to force best response or dominance through
`IsEquilibrium` if it obscures their quantification over opponent profiles or
creates duplicate correctness targets for D10.

### D6. Separate execution protocols from information models

Sequential semantics has two related but distinct responsibilities:

1. execution: legal actions, stochastic transitions, terminality, and traces;
2. information: what each player observes, how local information accumulates,
   and which strategies are information-local.

The greenfield default is two composable interfaces, not one record containing
both concerns. Two execution orderings remain live during the spike:

- **finite-first:** inductive finite histories/trees are primary, with a later
  general state-space interface;
- **general-state-first:** a state transition system is primary, with bounded
  horizon/well-foundedness supplied by certificates.

Mere representability of infinite games is not evidence for the second design.
It must also provide usable terminal, chance, and strategy semantics. The
general-state candidate starts from the active-player and legality design
already exercised by finite stochastic games:

```lean
universe uι us ua

structure ExecutionProtocol (ι : Type uι) where
  State : Type us
  Action : ι → Type ua
  init : State
  active : State → Finset ι
  available : State → (i : ι) → Set (Action i)
  terminal : State → Prop
  legal : State → (∀ i, Option (Action i)) → Prop
  legal_iff_active_available : ...
  step : (state : State) →
    { joint : (∀ i, Option (Action i)) // legal state joint } →
    FinDist State
  terminal_no_legal : ...
  nonterminal_exists_legal : ...

variable {ι : Type uι}

structure StepEvent (E : ExecutionProtocol ι) where
  source : E.State
  joint : ∀ i, Option (E.Action i)
  isLegal : E.legal source joint
  target : E.State
  realized : target ∈ (E.step source ⟨joint, isLegal⟩).support
```

`legal_iff_active_available` states that active players choose available
actions and inactive players choose `none`. Chance-only or administrative
steps use the unique no-op joint action while stochasticity lives in `step`.
The spike may replace `Finset` by a proposition-valued active predicate if the
former forces unwanted decidability into proof semantics, but legality remains
explicit and legal actions remain a subtype accepted by `step`.

An information model is layered over an execution protocol:

```lean
structure InformationModel (E : ExecutionProtocol ι) where
  PublicSignal : Type*
  PrivateSignal : ι → Type*
  -- Initial views and signals emitted by a realized legal transition.
  initialPublic : PublicSignal
  initialPrivate : ∀ i, PrivateSignal i
  publicSignal : StepEvent E → PublicSignal
  privateSignal : ∀ i, StepEvent E → PrivateSignal i
  -- Possibly compressed player-local information state.
  InfoState : ι → Type*
  initInfo : ∀ i, PrivateSignal i → PublicSignal → InfoState i
  pushInfo : ∀ i, InfoState i → Option (E.Action i) →
    PrivateSignal i → PublicSignal → InfoState i
```

The exact representation of realized support evidence is left to the spike,
but the boundary is fixed: execution does not know how observations are
accumulated, and the information layer does not redefine the transition law.
Both state-derived observations and transition-emitted observations must fit
without dummy data.

Run semantics must inspect terminality before requesting an action. No public
runner may require a total legal-joint chooser of type
`(s : E.State) → {joint : ∀ i, Option (E.Action i) // E.legal s joint}` when
terminal states have no legal actions. Chance must be carried by the transition
law or an explicit chance policy; a `none` mover with no probability law is not
chance semantics.

Deterministic information-local policies, behavioral policies, and mixed
policies are defined over the composed execution/information pair and induce
laws over histories. The pure and behavioral types compile to `GameForm`
without a second evaluator, and the ordinary mixed extension of the pure form
is definitionally the existing mixed-policy runner. Point-mass theorems recover
deterministic play, and the behavioral/mixed correspondence commutes with
compilation in both directions under its respective no-revisit and recall-like
hypotheses. Under perfect recall the protocol layer also preserves history laws
for an arbitrary one-player replacement while holding every opponent's induced
policy fixed; the EFG leaf uses this stronger statement to transfer Nash in
both directions. A bare execution protocol also compiles state-indexed policies
to a perfect-information or controller-supplied `GameForm`.

The finite-horizon information-local theorem remains the forward adapter from
one-shot optimality at every history to whole-policy optimality and ordinary
Nash in the compiled form. EXP-036 established the distinct well-founded
historywise theorem in `Protocol.SubgamePerfect`; EXP-075/D42 corrected its
public name after the imperfect-information root test. History-preserving
backward recursion uses the existing `WellFoundedPlay` certificate and agrees
with the forward history runner wherever that runner has stopped.
`IsHistorywiseOptimal` quantifies over every player, whole replacement policy,
and complete history. Under `ActsOnceWhereItMatters`, it is equivalent to
`HasNoProfitableOneShotDeviation`. `IsSubgamePerfect` instead quantifies over
histories whose continuation is closed under every active decision information
set, and historywise optimality implies it. A general imperfect-information
one-shot iff SPE theorem is false: EXP-078 gives a finite perfect-recall
protocol whose incumbent defeats every single-information-state replacement
but loses to a complementary whole-policy replacement in its only proper
subgame.
At finite horizon, `historyContext` still packages the actual continuation,
and the local one-shot condition is equivalent to
`IsSequentiallyRationalAt` in that context.

EXP-032 adds the assessment carrier needed by the limit-consistency layer, and
EXP-033 sharpens it on a hostile EFG. Policies remain total on `InfoState`,
including values no play reaches, but beliefs are indexed by
`InformationSite`: a reached information-state value with an explicitly
nonterminal history and a genuine action in its menu. Reached inactive, chance,
and terminal observations do not require beliefs. The nonterminal witness is
separate because `active` is deliberately unconstrained after play stops.
Beliefs are laws over complete histories, not merely execution states, because
two histories may merge into one state. Their projection
satisfies the existing state-level `BeliefOn` predicate. Sequential rationality
compares whole continuation behavioral policies; a local-law reduction requires
a separately proved one-shot-deviation theorem. Finite Bayes consistency at
positive-mass information sites and a
predicate-parametric limit schema stay in Protocol; pointwise convergence and
Kreps-Wilson consistency live in the one-way
`GameTheory.Analysis.Protocol` bridge.

Finite EFG syntax is a transparent Protocol specialization: it stores the
accepted execution and information objects with tree-shapedness and a
single-mover law, and defines no second runner or policy. For finite state
carriers, tree-shapedness gives an explicit equivalence from histories to
reachable states and hence an explicit history `Fintype`. The analytic EFG
adapter supplies those instances and the assessment-induced continuation
contexts; stable syntax imports neither Analysis nor solution concepts.

EXP-034 proves the assessment path is inhabited. Stable Protocol can normalize the
existing finite history reach weights into a Bayes belief whenever an
information site has positive mass. The analytic bridge turns any fully mixed
Bayes-consistent assessment into a sequentially consistent one through its
constant approximating sequence. On the hostile hidden-Boolean EFG, the
canonical runner gives both decision histories mass `1 / 2`, yielding a
concrete sequential equilibrium for zero continuation payoff. EXP-035 replaces
that vacuous payoff with one for matching the hidden Boolean: the canonical
Bayes belief is the fair mixture, and every whole replacement behavioral
policy has continuation value `1 / 2`, so the same assessment is sequentially
rational for a nonconstant payoff. These are concrete witnesses, not a general
finite-EFG existence theorem.

Information locality must hold by construction. A player's policy may receive
its `InfoState`, recommendation, and a legal-menu value determined by that
`InfoState`, but not the hidden execution state or a proof from which that state
can be recovered. An adequacy law relates the information-local menu to
`ExecutionProtocol.available`; the policy API does not compute the menu from a
hidden state. In particular, two native states mapped to the same information
state must be indistinguishable to a well-typed strategy; a later proposition
asserting constancy is insufficient.

Histories used for recall, tree-shapedness, and extraction are data containing
events or predecessor choices, not merely proofs of a `Reachable : Prop`.
`Subsingleton (Reachable s t)` is vacuous under proof irrelevance and must not
be accepted as uniqueness of histories. Strategic-form extraction must index a
player's contingent choices by the actual decision sites of the game, not by
all syntactically possible nodes or unreachable foreign games.

Terminality is a `Prop` in proof semantics. Finite or exact horizon is a
predicate/certificate about reachable traces, not a stored `Nat` field:

```lean
def BoundedHorizon (E : ExecutionProtocol ι) (k : Nat) : Prop := ...
```

Stopping or absorbing run semantics is derived and proved correct rather than
duplicating terminality with a horizon field. This protocol is not the
representation of infinite repeated games; those may compile directly to a
game form or use a later infinite-horizon execution interface.

The existing `comparison corpus`,
`comparison corpus`, and
`comparison corpus` are the empirical baseline for
beliefs, consistency, sequential rationality, and one-shot deviations. The
spike must inventory their conditional-law and locality obligations rather than
designing `InfoState` only around strategy compilation.

#### Validation spike

Compile these native semantics into the candidate layers:

1. a perfect-information EFG with chance;
2. an imperfect-information EFG with two nodes in one information set;
3. a three-node MAID with one chance, one decision, and one utility node;
4. a small FOSG with simultaneous active players;
5. a two-round simultaneous-action protocol.

Encode the perfect-information EFG in both the finite-first and
general-state-first execution candidates. The general candidate wins only if
the finite evaluator and backward-induction API arise through a small
well-founded/bounded certificate rather than a second parallel semantics.

For each, record separately:

- execution encoding: active players, legality, chance/no-op behavior,
  terminality, and one-step/run-law correspondence;
- information encoding: initial views, emitted observations, local-state
  accumulation, and information-local strategies;
- derivation of strategic profiles and terminal outcome laws.

Then instantiate one generic perfect-recall statement and one generic
strategic-form compilation theorem. Also implement one finite
assessment/conditional-belief slice: a conditional law over hidden states at an
information state, sequential rationality of a strategy given that assessment,
and the interface needed by a one-shot-deviation theorem. Compare state-indexed
action families with constant actions plus legality only if the default
encoding produces casts in downstream strategy proofs.

Add hostile compile/proof tests:

1. a terminating protocol runs without a global action chooser at terminal
   states;
2. a nontrivial chance node has a normalized law and the expected terminal
   outcome law;
3. the compiler proves that two intended nodes in one information set map to
   equal `InfoState` values, so every information-local strategy chooses equal
   outputs there by function congruence; separately, a policy accepting raw
   execution state fails the public strategy API's type check;
4. cyclic and merging arenas fail the premises of tree extraction for the
   intended reason;
5. a finite tree with finite local actions yields a genuinely finite extracted
   strategic strategy type over its own decision sites.

#### Disproof condition

Split the interfaces further if execution still needs language-specific
observation fields or the information layer must redefine transitions. Reduce
them to a smaller shared base if EFG and MAID cannot share `ExecutionProtocol`
without fake players, fake actions beyond the canonical no-op, or
language-specific escape fields. Merge them only if all five examples show
that separation adds certificates and casts without enabling independent
reuse. The outcome of D6 may legitimately be more than one execution
interface; a universal record is not a success criterion.

Reject general-state-first for the baseline if it passes syntax examples but fails any
terminal, chance, locality, or finite-extraction hostile test. Reject
finite-first if the simultaneous-action and MAID/FOSG slices require duplicate
execution/evaluation theories rather than a small extension. A MAID is not
required to pretend that all decisions are synchronous joint-action steps.
Reject or refine the information interface if conditional beliefs,
assessments, sequential rationality, or one-shot deviations require exposing
hidden state to policies or restating native information equivalence outside
the compiler certificate.

### D7. If selected by D0, stratify semantic certificates by preservation level

Do not designate FOSG, EFG, or another surface language as the mandatory
intermediate representation. If D0 selects the hybrid, certificates compose
only within the semantic level whose data they preserve:

1. **Protocol adequacy** preserves initial states, legal steps, traces,
   terminality, public/private signals, and relevant information properties.
2. **Strategic adequacy** preserves strategy profiles and induced outcome
   laws. It deliberately says nothing about recall or internal causality.
3. **Incentive adequacy** adds preference compatibility and a correspondence
   between allowed deviation schemes; this is the level that transports
   equilibrium.

A compiler may produce a protocol certificate and use generic theorems to
derive strategic and incentive certificates. An NFG may construct strategic
and incentive certificates directly without pretending to be a sequential
protocol.

A language-to-language bridge is obtained by composing certificates at the
required level. Direct bridges remain appropriate when they establish stronger
syntax-level facts, produce an executable translation, or avoid genuine
information loss. They must state what they add beyond certificate
composition.

#### Validation spike

Construct:

- NFG directly to strategic and incentive adequacy;
- EFG to protocol adequacy, then derive strategic adequacy;
- MAID to protocol adequacy, then derive strategic adequacy;
- one protocol-level recall transfer;
- one strategic outcome-law transfer;
- one equilibrium transfer using incentive adequacy.

For each nontrivial certificate path, implement the theorem-specific bespoke
direct bridge as a measured baseline. A certificate path gets credit only for
facts or composition reused by a second transfer.

Record proof size, composition laws, and every fact that cannot move at a lower
certificate level. In particular, a failure to transport recall through
strategic adequacy is expected behavior, not a failed certificate.

#### Disproof condition

Revise a certificate level if two language pairs repeatedly require the same
missing field. Retain direct bridges for isolated stronger facts rather than
growing universal certificates. Reject the stratification if deriving the
next level routinely requires reproving native evaluation rather than using
the preceding certificate, or if certificates at the same level do not compose
without language-specific proof obligations.

Also reject a level if its fields restate the target transfer theorem, if its
payload approaches the size of the native semantics, or if the D0 theorem
inventory is too small to amortize its abstraction and composition laws. In
that case, retain shared `GameForm` concepts where useful and use explicit
bespoke bridges for the remaining sequential theorems.

### D8. Minimal transformation taxonomy

Use precise names and introduce a structure only when it supports distinct
theorems.

Initial vocabulary:

- `FormHom`: strategy and outcome maps preserving outcome laws;
- `FormEquiv`: invertible `FormHom` data;
- `PayoffLawHom`: profile map preserving the joint payoff law;
- `PayoffLawEquiv`: invertible payoff-law preservation;
- `ProtocolSimulation` and `ProtocolBisimulation`: reserved for transition
  systems;
- deviation-scheme homomorphisms: maps of allowed deviations used by generic
  equilibrium transport.

Expected-utility preservation is a theorem derived from payoff-law
preservation, not a new structure. Do not create `EUMorphism`.

Not every form homomorphism preserves Nash: target deviations may not lift to
source deviations. Equilibrium transport must state the required deviation
reflection/surjectivity explicitly rather than hiding it behind an optimistic
name.

#### Validation spike

Cover:

1. outcome relabeling;
2. player reindexing;
3. strategy relabeling;
4. embedding a pure game into its mixed extension;
5. lifting an equivalence through mixed extension;
6. transporting Nash and CE with explicit deviation hypotheses.

#### Disproof condition

Add a new transformation structure only if two examples need the same extra
law and that law supports a theorem unavailable from existing structures.
Aliases whose only purpose is alternate terminology do not pass this test.

### D9. Independent finiteness capabilities

Do not bundle a monolithic global `FiniteGame` assumption into the semantic
core. Requirements differ legitimately:

- independent product needs finitely many players;
- enumeration needs finite strategy carriers;
- some expectation arguments need finite outcomes, though finite support often
  removes that need;
- topological existence theorems need additional nonemptiness and topology.

Proof-oriented theorem signatures should prefer proposition-valued `Finite`
when enumeration data is irrelevant. Executable modules use `Fintype` and
`DecidableEq`.

`Fintype.ofFinite` is allowed only in a tightly scoped proof that receives no
genuine `Fintype` instance and exports no enumeration-dependent data. Never mix
an `ofFinite`-derived instance with a supplied `Fintype`: their `Finset.univ`
values need not be definitionally equal, creating instance diamonds and
unstable enumeration proofs. The executable frontend never uses
`Fintype.ofFinite`; it carries and consistently uses its actual enumeration.

A convenience structure collecting all finite-carrier assumptions may be
provided for examples and theorem bundles, but it is not the foundational game
type.

#### Validation spike

For every theorem in the initial vertical slices, record a capability table:

| Theorem/definition | finite players | finite strategies | finite outcomes | decidable equality |
|---|---:|---:|---:|---:|
| mixed extension | yes | no | no | implementation-dependent |
| pure Nash definition | no | no | no | yes for standard unilateral lens construction |
| enumerate pure Nash | yes | yes | no | yes |
| finite-game Nash existence | yes | yes | theorem-specific | yes/local |

The actual table produced by the spike replaces this illustrative one.

#### Disproof condition

Introduce a stronger bundled capability only if at least five adjacent public
theorems repeat exactly the same assumption set and the bundle reduces user
work without causing instance ambiguity.

### D10. A separate executable finite-game frontend

Proof semantics over arbitrary real utilities cannot promise executable
decisions. The executable layer should instead use finite carriers and
computable scalars, initially `ℚ`.

Candidate representation:

```lean
structure FiniteTableGame (ι : Type*) [Fintype ι] [DecidableEq ι] where
  Action : ι → Type*
  actionFintype : ∀ i, Fintype (Action i)
  actionDecEq : ∀ i, DecidableEq (Action i)
  payoff : (∀ i, Action i) → ι → ℚ
```

It provides boolean/decidable algorithms for:

- pure Nash verification and enumeration;
- weak/strict dominance;
- finite iterated-dominance/rationalizability checks for the selected notion;
- Pareto efficiency;
- exact verification of a supplied rational mixed profile;
- finite expected payoff computation.

Compilation maps rational payoffs into real-valued proof semantics. Every
algorithm has a theorem equating its output with the abstract predicate.
The frontend's player/action `Fintype` and `DecidableEq` instances are
authoritative throughout compilation and correctness proofs; they are never
replaced by `Fintype.ofFinite`.

An equilibrium solver is not required initially. In particular, exact finite
mixed equilibria need not have rational coordinates.

Keep execution and proof linkage in separate modules. Modules below
`GameTheory.Finite.Algorithm` contain the data, enumeration, and boolean
procedures and must not import real-valued or noncomputable semantics. Modules
below `GameTheory.Finite.Correctness` may import Core and real-valued proof
semantics to state correctness, but not topology or fixed-point theory unless a
specific theorem genuinely requires it.

#### Validation spike

Require successful `#eval` tests for Prisoner's Dilemma, Matching Pennies,
Battle of the Sexes, and a three-player game. Prove:

```text
σ appears in enumeratePureNash G  ↔  compiled G is Nash at σ
```

Audit the algorithm modules directly: importing
`GameTheory.Finite.Algorithm` must not pull real analysis, topology, measure
theory, or fixed-point packages. The correctness root is audited against its
broader but explicit dependency budget rather than being mistaken for a purely
executable module.

#### Disproof condition

Change the concrete representation if evaluation requires classical choice,
opaque real arithmetic, or large proof terms at runtime. The proof-semantic
target remains stable; only the executable representation should change.

### D11. Measurable and infinite-path probability are outside the baseline

Continuous auctions, continuous mixed strategies, and stochastic laws on an
entire infinite realized-signal path require a measurable-kernel/integration
design, not a cosmetic replacement of `PMF`. Do not burden the finite core with
measurable-space parameters in anticipation of future work.

After the baseline, run an isolated spike formalizing one continuous Bayesian auction and
one continuous mixed-strategy game, plus one infinite stochastic-monitoring
path law. Compare:

- a separate `MeasureGame` core;
- a genuinely shared distribution-law interface;
- compilation of finite games into the measurable core.

Adopt shared abstraction only if it preserves the simplicity of finite theorem
statements and supports substantive shared proofs.

#### Validation and disproof condition

During the architecture spike, classify every selected flagship theorem by its
actual probability needs. D11 is validated if the stable finite/discrete slice
requires no measurable-kernel imports. It is disproved as a the baseline scope decision
if an explicitly selected flagship result—not a hypothetical future auction—
essentially quantifies over continuous distributions or an infinite stochastic
path law. In that case, design a separate measurable core before freezing the
finite API; do not simulate it through a generic monad placeholder.

Infinite repeated games do not by themselves disprove D11. the baseline presentation
boundary from D2 permits stagewise expected utility, deterministic paths of
mixed stage profiles, recursive values, and finite-prefix signal laws. A
theorem requiring the stochastic law of an entire infinite realized-signal
path is routed to the measurable spike: a countably supported `PMF` layer is
not an adequate substitute.

EXP-030 validates the lower half of this boundary in the greenfield code:
history-dependent deterministic paths, normalized discounted utility, and an
exact finite-prefix Protocol compiler require neither a measurable kernel nor
an infinite-path `FinDist`. EXP-031 validates the full deterministic discounted
folk theorem on the same representation: observable mixed stage profiles,
periodic continuations, and public trigger punishments still require no law on
an infinite realized path. Its convex geometry is isolated under
`GameTheory.Analysis.Repeated`.

EXP-032 likewise needs no measurable path law. Sequential consistency is
pointwise convergence of finite local strategy and belief coordinates, even
though those coordinates are indexed by Protocol histories. That topology is
isolated under `GameTheory.Analysis.Protocol`.

EXP-064 validates the public-monitoring equilibrium waist on the same side of
the boundary.  Every horizon has a finite `FinDist` of public signals and the
discounted payoff is an ordinary real series of those stage expectations.
Perfect-public equilibrium is canonical `IsNash` after every typed finite
public history, including zero-probability histories, and uniformly bounded
stage expected payoffs imply the exact one-shot-deviation principle without
constructing a law on an infinite realized path.

### D12. Package and stability boundaries

Use separate dependency roots, not only directories:

```text
GameTheory.Core          static foundations and foundational social/coalitional theory
GameTheory.Protocol      transition/information semantics and execution
GameTheory.Finite        executable rational frontend
GameTheory.Languages     stable language syntax and compilers
GameTheory.Analysis      fixed points, LP, minimax, existence
  ├─ Protocol            one-way analytic bridge over stable assessments
  ├─ Repeated            one-way analytic bridge over stable repeated play
  └─ Learning            one-way quantitative bridge over finite self-play
GameTheory.Repeated      stable stagewise and finite-prefix repeated-game theory
GameTheory.Cooperative   larger cooperative theories, matching, bargaining
GameTheory.Frontier      unstable open-game and repeated-monitoring research
GameTheory.Challenges    untrusted, opt-in formal targets and open problems
GameTheory.Tests         compilation and architecture tests
GameTheory.Examples      reader-facing examples
GameTheoryMath           independently reusable mathematical infrastructure
```

The exact number of Lake packages/targets is an implementation question, but
the following dependency properties are mandatory:

- Core does not import topology, fixed points, LP, or a language;
- syntax modules do not import solution concepts;
- stable packages do not import Frontier;
- no stable or Frontier package imports Challenges;
- executable modules do not import noncomputable analysis;
- general mathematics can be tested and versioned without importing games.

EXP-031 fixes one instance of the last two rules. Continuation, periodic-path,
and trigger-incentive theorems remain in `GameTheory.Repeated`; feasible-payoff
geometry, opponent minmax, and the discounted folk theorem live in the one-way
`GameTheory.Analysis.Repeated` bridge; generic denominator clearing lives in
the separate `GameTheoryMath` target. The stable root retains negative
`stdSimplex`/`Polynomial` probes, while positive bridge probes require the
trigger, minmax, and generic approximation sides to remain reachable. Protocol
is deliberately unreachable from this bridge.

EXP-032 fixes the complementary bridge direction needed by sequential
consistency. Stable `GameTheory.Protocol` owns behavioral assessments,
history-supported beliefs, finite positive-mass Bayes consistency, and a topology-free limit
schema. `GameTheory.Analysis.Protocol` owns pointwise convergence and the
Kreps-Wilson specialization. Protocol rejects both analytic declarations;
positive bridge probes reach stable rationality, stable Bayes consistency, and
the analytic convergence definition; the bridge rejects `stdSimplex` and
`Polynomial`. Basic topology names are already transitively reachable through
Mathlib, so project-declaration probes, not vocabulary probes, enforce this
boundary.

EXP-049/D21 applies the same enforced split to finite online learning. Core
owns only product-law, normalization, and finite regret-to-CCE identities.
`GameTheoryMath.OnlineLearning` proves multiplicative-weights regret over a
normalized real vector without importing either game semantics or `FinDist`;
`GameTheory.Probability.OnlineLearning` alone packages that vector as the
canonical finite law; `GameTheory.Analysis.Learning` composes the two sides.
Negative probes keep the algorithm and adapter unreachable from Core, while
positive probes require the bridge to reach both and the stable self-play
theorem. Protocol and the fixed-point dependency remain unreachable from the
learning bridge.

EXP-050/D22 applies the stratified rule to finite stochastic games. Native
stochastic data stores only state, actions, a `FinDist` transition, and stage
utility. A named perfect-public-monitoring bridge supplies the accepted
Protocol execution, proof-free public history, and behavioral runner; each
finite horizon then uses canonical expected utility and approximate Nash.
`GameTheory.Stochastic` is opt-in and positively probes all four promoted
layers while rejecting Repeated and the fixed-point dependency. It contains no
infinite-path law or general uniform-equilibrium existence claim.

EXP-051/D23 closes the mature discounted-value gate without reversing that
dependency. `GameTheory.Stochastic.ZeroSum` adds only pointwise zero-sum data
and a proof-free row/column action presentation. `Core.MatrixGame` owns the
topology-free finite matrix compiler, canonical mixed profiles and expected
payoff, the saddle/Nash identification, and row-guarantee/column-cap
characterization. `Analysis.MatrixValue` adds only selected minimax values,
nonempty optimal-strategy sets, and the value consequences of those Core
certificates. The one-way `Analysis.Stochastic` bridge then proves
the normalized Shapley contraction, unique discounted Bellman value, and
stationary statewise saddle selectors. A positive probe reaches the theorem
identifying the constructed column utility with the native player-one return;
positive probes also require the existing D12 Kakutani/minimax path to remain
live. Negative probes keep Analysis and Kakutani out of the stable stochastic
root and keep Protocol and Repeated out of the discounted bridge.
No arbitrary infinite-history optimality theorem is inferred from the
statewise result.

EXP-072/D39 extends the same one-way bridge to finite general-sum discounted
games.  The stable stochastic carrier remains unchanged.  Analysis constructs
one product of the canonical mixed-action polytope and a bounded continuation-
value cube, applies the already-admitted Brouwer dependency, and decodes the
fixed point as canonical mixed Nash in every statewise auxiliary
`UtilityGame`.  `GameTheoryMath` owns only the game-independent positive-part
fixed-point identity used to verify the Nash adjustment.  The promoted surface
uses `FinDist`, `Profile.update`, and `IsNash` exclusively; it adds no PMF,
infinite-path, stored-discount, or parallel equilibrium layer.  Uniform
equilibrium existence remains a separate open problem.

EXP-052/D24 adds the first shared welfare consumer without creating a new
semantic branch.  `Core.Welfare` defines aggregate and finite-law expected
welfare plus smoothness directly on `UtilityGame`, then derives the
division-free pure Nash bound through canonical unilateral updates.  EXP-053
closes the robust gate in a theorem-only `Core.RobustWelfare` leaf above both
Welfare and Learning, preserving their natural dependency direction while
reusing the existing epsilon/exact CCE predicates.  The opt-in congestion root
uses the same bridge for pure and correlated affine `5/2` cost bounds.  Pigou
and Braess exercise the same game form and Nash predicate.  No generic
price-of-anarchy ratio is introduced.

EXP-033 closes the finite-EFG adapter under that boundary. Stable
`GameTheory.Languages.EFG` positively reaches its execution, information, and
finite-history inputs while rejecting solution and analytic declarations.
`GameTheory.Analysis.Protocol.EFG` positively reaches the stable EFG carrier,
generic consistency, and assessment continuation contexts. This is a one-way
specialization and does not introduce a language-specific equilibrium
semantics.

General results suitable for Mathlib should be written to Mathlib conventions
from the beginning and upstreamed aggressively. Project-specific glue remains
under a project namespace rather than the global `Math` namespace.

Trust and maturity are separate axes:

- **stable:** proved, reviewed against its intended mathematical object,
  non-stub public API, and part of supported imports;
- **provisional:** proved but still under API or semantic review, imported only
  explicitly;
- **Frontier:** proved research work behind unstable interfaces;
- **Challenges:** well-typed targets that may contain the narrowly approved
  `answer(sorry)`/proof-hole pattern and are never proof dependencies.

The knowledge blueprint is math-first: mathematical statements and source
references precede encoding details, which belong in implementation remarks.
Lean is authoritative for what has been proved. Tagged public declarations,
blueprint links, and proof/maturity status are checked in both directions so
that proved theorems cannot remain recorded as gaps and blueprint declarations
cannot silently disappear. Stable aggregation is similarly checked rather than
maintained only by convention.

An `answer(sorry)` target is machine-checked only in the limited sense that its
statement elaborates. It is not evidence that the statement faithfully models
the source problem and is not a theorem available to trusted code. A refuted
source claim belongs in a proved counterexample theorem, not in Challenges.

#### Validation spike

Add CI checks that parse imports and reject forbidden edges, reject
`sorry`/`admit` in every trusted target, prevent dependency paths from
Challenges, validate blueprint/declaration synchronization, detect unexported
stable modules, and maintain a zero-warning baseline. Measure cold build time
and transitive module counts for:

```lean
import GameTheory.Core
import GameTheory.Finite.Algorithm
import GameTheory.Finite.Correctness
import GameTheory.Languages.NFG
import GameTheory
```

Frontier work passes its own tests but is not part of the stable umbrella until
its interface and theorem statements have settled. Challenges build and run
their specialized placeholder checker separately and are never included in the
ordinary library or example build.

#### Disproof condition

Revise the package split if the vertical slices expose a genuine logical cycle
between two proposed stable packages, or if a public root intended to be small
must import most of the repository to be useful. Merge packages only after
identifying the shared semantic layer causing the cycle; do not solve the issue
with umbrella imports or duplicated declarations.

## 6. Namespace, universe, and API rules

These decisions are cheap when made at the beginning and expensive later.

- All public declarations live below `GameTheory`.
- Languages live below `GameTheory.Languages.NFG`, `.EFG`, `.MAID`, and so on.
- Generic support code uses `GameTheory.Probability`,
  `GameTheory.Semantics`, or a separate package namespace—not global `Math` or
  `Semantics`.
- Foundational carrier types are universe-polymorphic.
- `DecidableEq`, `Finite`, and `Fintype` occur on operations/theorems that need
  them, not on syntax structures by default.
- `Profile.update` and `Profile.override` are the sole public profile mutation
  operations; `Profile.restrict` is the sole subprofile projection. Their
  constructive forms take `DecidableEq` only when their implementation needs
  it; only proof-facing wrappers may choose it classically.
- Familiar EU names are reducible specializations, not parallel definitions.
- Static law maps are not called simulations or bisimulations.
- Every compiler participating in D0's shared transfer architecture returns or
  is paired with a named protocol, strategic, or incentive adequacy
  certificate. A compiler used only by a bespoke bridge documents that choice
  instead. An unqualified `Adequacy` catch-all is not a public API.
- No file called `Facts` becomes a dumping ground. Facts belong to the
  structure/certificate they establish or to focused theorem modules.

## 7. Architecture tests

The following tests should be automated before theorem porting begins.

### 7.1 Forbidden-pattern checks

- no `Function.update` outside the profile implementation;
- no `cast`/`Eq.ndrec` outside designated signature and transport modules,
  except documented local exceptions;
- no `open Classical` in `GameTheory.Finite.Algorithm`;
- no `Fintype.ofFinite` in `GameTheory.Finite.Algorithm`;
- no solution-concept imports from syntax modules;
- no Frontier imports from stable packages;
- no Challenges imports from any trusted package;
- no `sorry`, `admit`, custom axioms, or ordinary proof holes in stable,
  provisional, Frontier, examples, or tests;
- no fixed-point imports from Core, Protocol, or Finite;
- no duplicate public logical definitions for EU and preference-parametric
  versions of the same concept;
- no unilateral/coalitional deviation implementation whose local action
  function receives the entire profile;
- no unnamed binary preference arguments in public equilibrium definitions;
- no stable module whose advertised concept is only an alias for another
  concept plus an `Iff.rfl` theorem;
- no blueprint proof status or declaration list that disagrees with tagged Lean
  declarations.

The transport check is a source-syntax check over authored declarations, as is
D1's cast count. Elaborated proof terms naturally contain `Eq.ndrec`, `Eq.mpr`,
and related equality eliminators produced by tactics; scanning compiled terms
would create noise rather than measure user-visible transport. The remaining
checks are architectural regression tests, not style lint.

### 7.2 Vertical-slice proof tests

Before adding breadth, the repository must contain:

1. one finite table NFG compiled to `GameForm`;
2. pure Nash, mixed Nash, CCE, and CE through the single deviation predicate;
3. one chance/imperfect-information EFG compiled through execution and
   information layers;
4. one MAID compiled through the same layers, or a recorded rejection of their
   common execution base;
5. D0's named transfer theorems through the selected shared architecture, with
   bespoke direct-bridge baselines where certificates are proposed;
6. one player reindex and one mixed-extension transport proof;
7. executable pure-Nash enumeration with an abstract correctness theorem;
8. one existence theorem isolated in the Analysis dependency layer and reached
   through the finite-law/simplex bridge;
9. all five terminal/chance/locality/history/finite-strategy hostile tests from
   D6;
10. one assessment/conditional-belief and sequential-rationality slice, with
    the interface required for a one-shot-deviation theorem;
11. abstract best-response/dominance predicates and one executable checker
    proved correct against them;
12. one Bayesian interim-deviation scope probe.

### 7.3 Usability tests

Create downstream files, written without opening implementation namespaces,
that perform the following:

- define Prisoner's Dilemma in under 25 nonblank lines;
- state and prove its unique pure Nash equilibrium;
- define Matching Pennies and verify the standard supplied mixed equilibrium;
- define a two-stage perfect-information game and invoke its compilation;
- relabel players and transport a theorem without writing an explicit cast;
- switch the same form from EU preferences to an ordinal preference;
- reuse one signature-bound profile unchanged across two different play laws or
  payoff/preference packages.

If downstream use requires knowledge of internal certificates or transport
proofs, the public API has failed even if the implementation is elegant.

### 7.4 Performance tests

Record on a fixed CI runner:

- cold build time for each public root;
- incremental rebuild after changing one NFG example;
- peak memory for the carrier/reindex stress file;
- elaboration time for the largest adequacy certificate;
- proof and elaboration cost of the corresponding bespoke direct bridge;
- number of imported modules for core and executable smoke tests.

Use ratios and regression thresholds rather than developer-machine absolute
times. A proposed abstraction should not be accepted if its representative
slice is more than 25% slower without eliminating significant proof or API
complexity.

## 8. Dependency-gated architecture spike

No domain-wide porting occurs during this spike.

### Phase 0: Scope, flagship results, and architecture evidence

- Name the existing results that are supposed to justify shared semantics.
- Classify each as protocol-, strategic-, incentive-, or syntax-level.
- Record the native data each theorem actually uses and what it forgets.
- Select D0's four representative transfers and the bespoke-bridge baselines.
- Mine the current `KernelGame` implementation as the universal-hub datapoint:
  bridge and cast sites, proof size, imported dependencies, reused results, and
  change concentration.
- Freeze a named flagship-theorem list. At minimum it samples finite Nash
  existence, CE or learning, Kuhn behavioral/mixed correspondence, backward
  induction or one-shot deviation, one Bayesian/interim result, one
  mechanism-design truthfulness result, and the discounted repeated-game
  result used to classify infinite-horizon probability needs.
- Give every existing domain an explicit the baseline disposition. The initial defaults
  to confirm or overturn are:

| Domain | Default the baseline disposition | Required probe |
|---|---|---|
| Mechanism design | stable coordinated layer over shared forms/preferences | one truthfulness or incentive-compatibility theorem |
| Bayesian/incomplete-information games | provisional native branch sharing only justified vocabulary | one interim, type-dependent deviation slice |
| Auctions | finite/discrete models in the baseline; continuous models in D11 | one finite auction plus the D11 continuous-auction statement audit |
| Voting and social choice | stable coordinated branch; do not force strategic form where unnecessary | one rule/property theorem and one strategic compilation if useful |
| Knowledge/epistemic games | provisional information/protocol consumer or separate branch | one knowledge result testing whether `InfoState` retains enough structure |
| Potential games | stable static-form theory | potential-improvement implies pure-equilibrium existence on a finite game |
| Evolutionary stability | provisional separate static/dynamic branch | one ESS or replicator statement with its actual scalar/topology needs |
| Repeated games | stable stagewise/recursive and finite-prefix theory; stochastic infinite path laws wait for D11 | discounted folk-theorem presentation plus one monitoring prefix law |
| Sequential rationality | stable target of the protocol/information layer | assessment, conditional belief, and one-shot-deviation slice |
| Cooperative games, matching, bargaining | parallel stable branches | one representative theorem without artificial strategy profiles |

Deliverables: the transfer inventory, frozen flagship list, domain-disposition
matrix with concrete declaration names, measured the baseline hub baseline, and a
provisional D0 decision with an explicit bridge/certificate complexity budget.
There are no generic “future bridge” entries. A certificate abstraction
receives no credit for hypothetical consumers.

### Phase 1: Core competition

- Implement indexed-signature and bundled-signature miniatures.
- Implement both finite-support representation candidates, including law
  operations, expectation, and the finite-carrier `stdSimplex` equivalence.
- Select a provisional D1 winner from measurements; do not freeze it until the
  downstream usability and transformation slices pass.
- Choose the D2 representation from measurements and demonstrate the Analysis
  bridge without a second mixed-game API.
- Establish namespaces, import audits, and build measurements.

Deliverable: a short decision record containing raw cast counts, proof sizes,
and elaboration timings.

Phase 2 starts only after D1 has a provisional decision record and the D2
representation has an explicit decision record. It also requires Phase 0's
provisional D0 decision, so the slice does not silently accumulate
infrastructure for every candidate.

### Phase 2: Incentive vertical slice

- Implement form, preference, utility evaluation, profile operations, and
  local deviation schemes and preference-orientation properties.
- Instantiate Nash, mixed Nash, CCE, CE, and strong Nash.
- Define best response, dominance, and the selected rationalizability target as
  profile-quantified concepts rather than equilibrium aliases.
- Run the Bayesian interim-deviation scope probe.
- Implement the rational finite-table frontend and its first correctness
  theorem.

Deliverable: the four executable examples and proof-semantic equivalence tests.

Phase 3 starts only after the single equilibrium predicate has expressed Nash,
CCE, CE, and strong Nash without violating locality.

### Phase 3: Sequential vertical slice

- Implement the finite-first and general-state execution candidates and the
  separate information model.
- Compile the selected EFG and MAID examples.
- If Phase 0 provisionally selected the hybrid, build its smallest protocol-
  adequacy prototype and derive strategic facts. If it selected coordinated
  branches, build the direct bridges only. Do not rebuild a universal hub unless
  the measured the baseline evidence identified a specific, testable repair.
- Implement the selected bespoke direct-bridge baselines in either case.
- Test perfect recall, observation preservation, terminal execution, chance,
  information locality, history uniqueness, finite strategic extraction,
  conditional beliefs, sequential rationality, and the one-shot-deviation
  interface.

Deliverable: a written list of every language-specific workaround. Any such
workaround must be removed, generalized with evidence, or used to reject D6.
Finalize D0 here using the measured hub baseline, direct bridges, and the one
new architecture prototype; record the chosen architecture separately at each
semantic level.

Phase 4 starts only after D0 is final and D6 records whether the languages
share an execution base and what information interface survived the spike.

### Phase 4: Transform and analysis slice

- Implement the minimal transformation taxonomy.
- Complete D0's four named transfer slices through the selected architecture.
- Lift one transformation through mixed extension.
- Place one equilibrium-existence proof behind the Analysis boundary through
  the finite-law/simplex bridge.
- Run usability and performance tests.

Deliverable: accept/reject decisions for every remaining provisional item,
plus a frozen the baseline core API. D7 is adopted only if the measured hybrid beats its
direct bridge baselines on actual reuse or composition.

#### Post-architecture delivery

The checked-in `Phase4StaticHarvest.md` completed a narrower static-harvest
package than the transform-and-analysis list above. Subsequent delivery closed
T1-T4, EXP-043/D16 settled knowledge ownership in a separate stable epistemic
branch, EXP-044/D17 settled ESS/NSS in a separate stable evolutionary branch
with dynamics reserved for Analysis, and EXP-045/D8 promoted the minimal
concrete transformation surface. Every original Phase 4 architecture
obligation is now closed; later work is declaration recovery and explicitly
gated expansion rather than architecture completion.

EXP-049/D21 is such a post-architecture local gate: broad learning recovery
exposed a missing reusable MW proof spine, and the measured vector/adapter/
analytic-bridge split resolved it without reopening Core or the canonical law.

EXP-050/D22 is the corresponding mature-blind-spot gate. It admits a separate
stochastic root through canonical Protocol and approximate-equilibrium
surfaces. EXP-051/D23 completes that gate through the normalized discounted
two-player zero-sum Shapley contraction/value slice and a one-way Analysis
bridge, without admitting an infinite-path law or the open uniform-existence
claim.

The RFC continues to govern architecture and disproof conditions. Mutable
delivery order, obligation status, mature missing subfields, and the isolated
research portfolio are governed by
[`PostArchitectureDeliveryPlan.md`](PostArchitectureDeliveryPlan.md). Current
family status is recorded in [`DeliveryLedger.md`](DeliveryLedger.md). Neither document may silently
reopen an adopted decision; a conflicting result reserves an experiment and
amends the relevant decision record.

## 9. Escalation and kill criteria

Failures are classified by consequence rather than counted. Two expected
design narrowings do not add up to an invalid core.

### 9.1 Core-invalidating failures

Any one of these pauses breadth work and reopens the relevant core decisions:

1. Normal use requires more than one public logical definition of Nash or CE.
2. The equilibrium API cannot enforce both law-linearity and recommendation
   locality for standard Nash/CE/coalitional deviations.
3. The selected finite-law representation gives mathematically misleading
   expectation or requires the boundedness machinery finite support was meant
   to remove.
4. The executable frontend must duplicate solution concepts rather than prove
   its algorithms correct against the semantic definitions.
5. Importing Core pulls topology, fixed points, a language, Frontier, or
   Challenges.
6. The selected execution semantics cannot express terminal play and chance
   without an impossible total chooser, dummy probability data, or evaluation
   that silently stops at chance nodes.
7. The information strategy type exposes hidden execution state at an
   information set, relies only on a later locality proposition, or cannot
   support conditional beliefs and sequential rationality without reopening
   native information equivalence.
8. The Analysis layer requires a second public mixed-profile, expected-payoff,
   or equilibrium definition.
9. A trusted result depends, directly or transitively, on Challenges.

### 9.2 Design-narrowing outcomes

These reject or narrow one decision but do not pause unrelated core work:

- indexed signatures expose more transport than a stored bundled signature:
  choose the bundled-signature form of D1;
- neither finite-support representation clearly wins: hide a `PMF` subtype
  behind the API and record the compromise;
- a flagship theorem essentially needs countably supported probability but no
  path-space measure: add a separate countable layer and narrow D2;
- a flagship theorem needs the stochastic law of an entire infinite path:
  route it to D11's measurable layer rather than pretending a countable layer
  is sufficient;
- the finite-law/simplex bridge is too expensive: use a documented
  Analysis-facing simplex representation behind one logical API;
- EFG and MAID cannot share an execution protocol honestly: retain a smaller
  transition base or separate execution interfaces;
- general-state-first fails the hostile sequential tests: use finite-first for
  the baseline and retain the general protocol as a later experiment;
- D0's transfer inventory is too small to amortize certificates: retain shared
  static forms and use bespoke sequential bridges;
- coordinated branches duplicate solution concepts or evaluation proofs:
  select the stratified hybrid at the affected semantic level;
- recall or ownership does not cross strategic adequacy: require protocol
  adequacy, as designed;
- a transformation needs stronger deviation correspondence: extend incentive
  adequacy rather than weakening equilibrium semantics.

### 9.3 Local-remediation failures

These block the affected module until repaired but do not reopen the whole
design:

- an isolated cast escapes its designated transport module;
- an import-audit exception is requested;
- a compiler accumulates an unfocused `Facts` file;
- a downstream usability example needs internal namespace knowledge;
- performance regresses without a measured proof/API benefit.

An exception pattern that recurs across two or more modules promotes the issue
to the corresponding design decision; exceptions are evidence, not permanent
waivers.

## 10. Explicit non-goals for the initial rewrite

- continuous strategies or Giry/measure kernels;
- stochastic semantics for entire infinite realized-signal paths;
- a generic scalar hierarchy for all payoff theorems;
- category instances before ordinary composition has demonstrated a payoff;
- an exact mixed-equilibrium solver;
- a universal language IR capable of representing every syntax without loss;
- routing every bridge through FOSG or any other concrete language;
- admitting open-problem answers or proof holes anywhere in the trusted
  library, Frontier, examples, or tests;
- reproducing every theorem in the current repository before stabilizing the
  new foundations;
- compatibility aliases or automated migration tooling.

## 11. Decision record template

Every experiment-gated decision should end with a checked-in record:

```text
Decision:
Experiment IDs:
Hypothesis:
Competing designs:
Representative examples:
Measurements:
Evidence from existing libraries:
Unexpected costs:
Kill condition:
Result: accept / reject / narrow
Consequences for public API:
```

Raw runs and observations live in `docs/ExperimentLog.md`; a decision record
cites their stable IDs and interprets the evidence. Do not silently rewrite an
experiment's original hypothesis or kill condition after failure. Revise this
RFC only through a decision record that points back to the supporting,
refuting, narrowing, or inconclusive evidence.

The purpose is to make foundational decisions reversible while the codebase is
small. Once the dependency-gated spike passes, the accepted core becomes
deliberately boring: new language and theorem work must use its interfaces or
present new evidence strong enough to reopen a recorded decision.
