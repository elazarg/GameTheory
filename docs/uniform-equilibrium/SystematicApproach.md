# A balanced systematic approach to finite quitting games

**Status:** stable research guidance, not a theorem, certificate, or live
priority list.  
**Scope:** how the finite-quitting program should organize positive production,
negative search, formalization, and failure information.

The repository already has a strong back end. Supplied support paths, essential
APS data, face circulations, finite cycles, target-closed tails, and related
certificates can reach terminal approximate equilibrium and then a uniform
payoff. The weak part is the front end: starting from an arbitrary reward table,
produce suitable strategic data or a genuine nonexistence certificate.

This page organizes that front-end work. The classifications below are
**editorial and mathematical guidance**. They are not authenticated by phantom
Lean indices, generic wrappers, or a CI manifest. Lean should formalize actual
mathematical statements and compilers when those are useful; it should not be
asked to certify the provenance or research role of an arbitrary function.

## 1. Keep three distinctions separate

### Root route

A positive construction normally enters one of three broad routes:

1. **stationary/projective** — stationary roots, LCP or min-max data,
   analytic/projective packets, target acceptance or retargeting, and
   finite-dimensional semialgebraic structure;
2. **instant/punishment** — a sure first-stage quitter backed by a credible
   continuation punishment, including all outsider no-join inequalities; or
3. **proper absorption path** — finite or infinite absorbing plans, including
   support-witness paths, essential APS, face circulations, and cycles.

The **nonexistence lane** runs in parallel and must eventually produce one
fixed positive all-behavior terminal exploitability gap. The theorem in
`UniformNonexistenceCertificate.lean` shows that this is the exact negative
semantic target, not merely a sufficient format.

These routes are broad research categories. They are not asserted exhaustive as
strategy representations, and a theorem's route is not established by attaching
a label to its type.

### Artifact role

A result may be a:

- **producer**, constructing strategic data from more primitive game data;
- **adapter**, translating one data language into another;
- **verifier/compiler**, consuming supplied data to prove an equilibrium
  conclusion;
- **closure/transfer theorem**, moving a proved conclusion between nearby
  games, targets, or descriptions;
- **diagnostic**, exposing why a proposed route fails; or
- **separator**, proving an unrestricted positive exploitability gap.

A result may legitimately serve more than one role, but each claim must be
stated separately. In particular, a compiler is not a producer merely because
its input type is easy to name.

### Claim level

Keep distinct:

1. verification of one supplied object;
2. synthesis inside a bounded or structurally restricted class; and
3. coverage of arbitrary reward tables or unrestricted strategies.

No lower level receives automatic credit at a higher level.

## 2. The semantic meeting points

For finite quitting games, positive work should reach:

```text
for every epsilon > 0,
there exists a terminal epsilon-Nash behavioral profile.
```

`QuittingTerminalUniformPayoffSelection.lean` proves that this all-accuracy
terminal statement is equivalent to existence of a uniform-equilibrium payoff.

Negative work should reach:

```text
there exists gap > 0 such that every behavioral profile
has a terminal unilateral deviation improving by at least gap.
```

The fixed-gap theorem in `UniformNonexistenceCertificate.lean` proves that this
is exactly the negation of the positive terminal waist.

Intermediate constructions should therefore say which of these semantic targets
they reach, or what concrete datum blocks the next arrow.

## 3. Central producer principle: glue, enlarge, recur, or separate

The most useful common principle is not a new universal certificate grammar. It
is a disciplined alternative for failed local constructions.

Starting from a strategically meaningful local support or subgame object, aim
to obtain one of:

1. **glue** — reinsert excluded players while retaining unrestricted-deviation
   control;
2. **enlarge** — identify the outsider, joiner, or preemptor whose violated
   inequality determines a richer active support;
3. **recur** — enter one path-compatible recurrent component carrying positive
   absorption and controlled signed defect; or
4. **separate** — produce a normal, potential, or direct behavioral argument
   that reaches a typed boundary, rank descent, target rejection, or the fixed
   positive exploitability gap.

A second time scale, tiny occupation weight, compact projection, or approximate
cycle is not itself a repair. It matters only after a theorem shows that the
pointwise strategic inequalities and legal chronological path are preserved.

The conjecture-directed dependency program implementing this principle is in
[`ConjectureDirectedSpine.md`](ConjectureDirectedSpine.md).

## 4. Failure payloads are part of the result

A failed attempt should preserve the smallest useful witness, such as:

- the active support and failed owner or outsider inequality;
- the suffix or terminal atom responsible for failed subgame gluing;
- the rejected target and the profitable late quit-time family;
- the recurrent component in which zero-defect flow fails;
- a real-arc sign type with no physical lift;
- a dual normal with its exact sign restrictions; or
- an explicit strategy class that the argument excludes and no larger one.

This turns refutations into inputs for another route. “No object of this grammar
exists” is not a counterexample to the quitting-game conjecture.

## 5. Promotion fences

The following promotions require named mathematics:

- compiler to producer;
- local complementarity packet to credible strategic target;
- formal or Zariski tangent to positive real arc;
- global convex circulation to one legal recurrent path;
- bounded-template failure to unrestricted nonexistence;
- accuracy-indexed objects to one exact finite object; and
- pathwise or componentwise separators to a fixed all-behavior gap.

A new certificate language is justified only when an existing language provably
forgets a strategic variable needed by a downstream theorem, or when the new
language comes with a producer or decisive no-go result.

## 6. Balanced scheduling

Balanced does not mean equal effort. Priority should still follow dependency
distance, downstream leverage, falsification value, mathematical readiness, and
the risk of consuming a false premise.

Maintain, when useful:

- one upstream support/subgame/pivot question;
- one proper-path realization question;
- instant punishment as an exact boundary test rather than a repeated source of
  weaker criteria;
- one unrestricted negative lane; and
- one formalization lane for the strongest ready mathematical result.

Do not let another conditional back-end compiler displace the producer question
merely because the compiler is easier to formalize.

## 7. Handoff format

For route-facing mathematical work, record:

1. actual input data;
2. exact success output;
3. exact failure or pivot output;
4. strategy and observation class;
5. whether the claim is verification, restricted synthesis, or arbitrary-table
   coverage;
6. the next named consumer; and
7. dependencies on unmerged or unaudited work.

This is guidance for scientific coordination. It should be enforced by review
and source-of-truth maintenance, not by pretending that a generic Lean function
type authenticates its mathematical provenance.
