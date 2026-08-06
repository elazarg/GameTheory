# Strategic self-similarity and tangent holonomy

This note develops the self-similarity direction of the finite-quitting-game
program. Its purpose is twofold:

1. isolate exact algebraic consequences that can be proved now; and
2. state the missing producer theorem sharply enough that it can either be
   proved or falsified.

The word *self-similarity* is used only with an explicit semantic level. A
return to the same physical state is much weaker than a return to the same
strategic continuation packet.

## Status legend

- **Lean-checked in this PR** means that a declaration is present on the PR
  branch, subject to the PR's recorded CI result.
- **Lean-checked before this PR** means that the production branch already
  contains the cited theorem.
- **Mathematical theorem** means a complete derivation is given here, but no
  Lean declaration is claimed.
- **Conditional theorem** means the displayed conclusion is proved under an
  explicit repeatability, compactness, or semantic-closure hypothesis.
- **Open target** means no proof is claimed.
- **False strengthening** marks a tempting statement contradicted by an
  existing example or by the algebra below.

---

## 1. Four different return notions

Let a finite block begin at some live continuation object and end at another.
There are four increasingly strong notions of return.

### 1.1 Physical return

The endpoint has the same physical state as the entry.

This is insufficient. A behavior strategy may carry an unbounded public or
private account even when the physical state returns. The Big Match already
contains a two-stage live-state cycle with zero target debt, but the
Blackwell--Ferguson deficit phase need not return with the state.

### 1.2 Controller return

The endpoint has the same physical state and the same displayed controller
phase.

This is stronger, but it is sound only if the phase is semantically complete.
A displayed phase may omit a continuation promise, a marked terminal packet,
a quit-time witness, or entry-measured debt.

### 1.3 Target return

The block reproduces one selected target payoff and caps every unilateral
stopping deviation at that target.

This is the finite coefficient notion formalized by
`QuittingBoundaryHolonomy.IsSelfSimilarAt`. It is enough to concatenate
several already compatible blocks while preserving the same target.

### 1.4 Strategic packet return

The endpoint reproduces the complete continuation packet needed by the next
copy: physical state, target, all unilateral stopping obstacles, controller
state, entry/exit anchors, clocks, debt provenance, conditional terminal mark,
and chronological splice data.

Only this notion licenses a game-level pumping argument without an additional
adapter. The present PR formalizes the coefficient projection and its exact
algebra. It does not claim that coefficient return implies strategic packet
return.

---

## 2. Exact finite-block holonomy

**Status: base Lean plus Lean in this PR.**

For each player, an actual finite quitting block has two maps of a supplied
terminal continuation value.

The prescribed map is affine:

\[
P(w)=B+p w,
\qquad p\ge 0.
\tag{2.1}
\]

The unilateral stopping map is max-affine:

\[
D(w)=\max\{A,\;T+\chi w\},
\qquad \chi\ge 0.
\tag{2.2}
\]

The existing `QuittingBoundaryHolonomy` packages these maps for every player
from one common product-root block. It does not independently choose scalar
coefficients player by player.

For chronological composition, with the inner block played after the outer
block,

\[
(B_o,p_o)\circ(B_i,p_i)
=
(B_o+p_oB_i,\;p_op_i),
\tag{2.3}
\]

and

\[
(A_o,T_o,\chi_o)\circ(A_i,T_i,\chi_i)
=
\bigl(
\max\{A_o,T_o+\chi_oA_i\},
T_o+\chi_oT_i,
\chi_o\chi_i
\bigr).
\tag{2.4}
\]

These laws are associative and already linked to the actual finite policy and
finite stopping problem.

---

## 3. Target residuals and exact self-similarity

Fix a proposed target coordinate `v`.

For the prescribed map define absorbed mass and residual

\[
m:=1-p,
\qquad
r_v:=P(v)-v=B-mv.
\tag{3.1}
\]

For the deviation map define early and tail residuals

\[
a_v:=A-v,
\qquad
t_v:=T-(1-\chi)v.
\tag{3.2}
\]

Then

\[
D(v)-v=\max\{a_v,t_v\}.
\tag{3.3}
\]

Consequently a player coordinate is strategically self-similar at `v` exactly
when

\[
r_v=0,
\qquad
a_v\le0,
\qquad t_v\le0.
\tag{3.4}
\]

For a payoff vector, impose (3.4) for every player.

This gives a finite semialgebraic condition in the five coefficients per
player. In Lean it is stated both semantically and as the equivalent family
of one equation and two halfspaces.

### Composition closure

If both outer and inner blocks are self-similar at the same target, then their
composition is self-similar there. Prescribed fixedness follows from

\[
P_o(P_i(v))=P_o(v)=v,
\]

and deviation safety follows from monotonicity:

\[
D_o(D_i(v))\le D_o(v)\le v.
\]

This is exact and requires no compactness.

---

## 4. The residual cocycle

**Status: Lean-checked in this PR.**

The absorbed mass composes as

\[
m_{o\circ i}=m_o+p_om_i.
\tag{4.1}
\]

The target residual obeys the parallel cocycle

\[
r_{o\circ i}=r_o+p_or_i.
\tag{4.2}
\]

Thus the inner residual is transported back to the entry by the outer
survival. This is the exact finite-block analogue of transporting a late
local incentive comparison to the original root.

Away from zero masses, define the normalized residual

\[
\rho_v:=\frac{r_v}{m}.
\tag{4.3}
\]

Then

\[
\rho_{o\circ i}
=
\frac{m_o\rho_o+p_om_i\rho_i}
     {m_o+p_om_i}.
\tag{4.4}
\]

So normalized residuals average under composition, with weights equal to the
absorption mass as viewed from the outer entry. Formula (4.4) is the precise
renormalization law suggested by absorption-time compactification.

---

## 5. Repetition, contraction, and pumping

Let one affine block be repeated `n` times. Define

\[
G_n(p)=1+p+\cdots+p^{n-1}.
\]

Then

\[
r_v(P^n)=G_n(p)r_v(P).
\tag{5.1}
\]

The geometric identity

\[
(1-p)G_n(p)=1-p^n
\tag{5.2}
\]

holds even at `p=1` when `G_n` is defined recursively.

### Strictly contracting regime

When `p<1`,

\[
G_n(p)=\frac{1-p^n}{1-p}.
\tag{5.3}
\]

A raw seam error `r` may therefore be amplified by nearly
`1/(1-p)`. The stable condition near `p=1` is not merely

\[
r\to0,
\]

but

\[
\frac{r}{1-p}\to0.
\tag{5.4}
\]

Equivalently, the block's fixed point must approach the target.

### Neutral regime

When `p=1`,

\[
r_v(P^n)=n r_v(P).
\tag{5.5}
\]

Any positive residual defeats every finite residual budget after enough
repetitions. This coefficient pumping lemma is formalized.

A game-level contradiction additionally needs an exact strategic packet
return and a fixed finite implementation cost per copy. Physical return alone
does not supply those premises.

---

The idempotent classification, absorbed-mass blow-up, max-plus tangent, and
realized-block consequences continue in
[SelfSimilarityTangent.md](SelfSimilarityTangent.md).
