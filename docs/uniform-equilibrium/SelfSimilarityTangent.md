# Strategic self-similarity: normal forms and tangent holonomy

This document continues [SelfSimilarity.md](SelfSimilarity.md). The first part
defines strategic return, proves the residual cocycle, and derives contraction
and neutral pumping. Here the focus is idempotents and the blow-up of the
neutral face.

## 6. Fixed target is not idempotence

A target-fixed block need not be an idempotent map. For example,

\[
P(w)=m v+(1-m)w
\]

fixes `v` for every `m`, but for `0<m<1` one has `P\circ P\ne P`.

This distinction matters:

- **target self-similarity** is the operational property needed to concatenate
  compatible blocks at a selected continuation;
- **idempotence** is the recurrent algebraic object expected after passing to a
  compact semigroup closure.

Conflating them would incorrectly discard every genuine contracting block.

---

## 7. Classification of coefficient idempotents

**Status: Lean-checked in this PR.**

### 7.1 Affine idempotents

Suppose

\[
P(w)=B+p w
\]

and `P\circ P=P` coefficientwise. Then

\[
p^2=p,
\qquad
B+pB=B.
\]

Therefore exactly one of the following holds:

1. `p=0`, and `P` is the constant projector `P(w)=B`;
2. `p=1` and `B=0`, and `P` is the identity.

If the idempotent is also self-similar at target `v`, the constant projector
must be the constant `v`.

### 7.2 Max-affine idempotents

Suppose

\[
D(w)=\max\{A,T+\chi w\}
\]

and `D\circ D=D` coefficientwise. The coefficient equations are

\[
\chi^2=\chi,
\qquad
T+\chi T=T,
\qquad
\max\{A,T+\chi A\}=A.
\]

Hence exactly one of the following holds:

1. `\chi=0` and `T\le A`; then `D(w)=A` is constant;
2. `\chi=1` and `T=0`; then `D(w)=\max\{A,w\}` is a threshold closure.

If it is safe at `v`, then `A\le v` in both cases.

Thus complete strategically admissible coefficient idempotents have only
projector/identity prescribed coordinates and safe constant/threshold
deviation coordinates.

---

## 8. Absorbed-mass blow-up

**Status: Lean-checked in this PR.**

Write an affine block as

\[
P_{m,R}(w)=mR+(1-m)w.
\tag{8.1}
\]

Then

\[
P_{m,R}(w)=w+m(R-w),
\tag{8.2}
\]

and at a target `v`,

\[
P_{m,R}(v)-v=m(R-v).
\tag{8.3}
\]

For `m\ne0`, the normalized residual is exactly

\[
\frac{P_{m,R}(v)-v}{m}=R-v.
\tag{8.4}
\]

The raw coefficients converge to the identity as `m\to0`, whatever bounded
anchor `R` is chosen. The blow-up retains the direction erased by coefficient
convergence.

### Exact composition

For two mass-anchor blocks,

\[
m_{o\circ i}=m_o+(1-m_o)m_i,
\tag{8.5}
\]

and the absorbed payoff moment is

\[
m_oR_o+(1-m_o)m_iR_i.
\tag{8.6}
\]

Thus the composite anchor, when the total mass is positive, is the transported
mass-weighted average of `R_o` and `R_i`.

A useful additive clock is

\[
\ell=-\log(1-m),
\tag{8.7}
\]

whenever `0\le m<1`: survival multiplies, so `\ell` adds. This logarithmic
clock is a mathematical observation; it is not yet a production Lean
interface.

---

## 9. Max-plus tangent for unilateral stopping

**Status: Lean-checked in this PR for the finite-scale formulas.**

At target `v`, write a max-affine block at scale `m` as

\[
D_m(w)
=
\max\left\{
  v+m\alpha,
  mR+(1-m)w
\right\}.
\tag{9.1}
\]

Here `\alpha` is the early-obstacle drift per unit mass and `R` is the tail
anchor.

At the base target,

\[
D_m(v)
=
v+m\max\{\alpha,R-v\}.
\tag{9.2}
\]

For `m>0`, safety at the target is exactly

\[
\alpha\le0,
\qquad
R\le v.
\tag{9.3}
\]

Probe a perturbation `w=v+mx`. Then the exact finite-scale formula is

\[
D_m(v+mx)
=
v+m\max\{\alpha,R-v+x-mx\}.
\tag{9.4}
\]

After division by `m`, the tangent map is therefore

\[
\mathcal D(x)=\max\{\alpha,R-v+x\},
\tag{9.5}
\]

with the exact finite-scale correction `-mx` in the tail branch.

This is max-plus rather than linear. A tangent compactification which records
only affine prescribed generators will lose unilateral stopping geometry.

### Two important scale qualifications

First, prescribed survival and opponent-only survival are distinct playerwise
scales. A full block generally has masses

\[
m_i=1-p_i,
\qquad
n_i=1-\chi_i.
\]

Second, existing realized-block bounds control the tail intercept at scale
`n_i`, but do not by themselves prove that the early obstacle `A_i-v_i` is
`O(n_i)`. A finite signed early drift is therefore not inserted by assumption.
The positive early violation is instead compactified in `ℝ≥0∞`: a divergent
ratio remains visible as `+\infty`.

---

## 10. What realized finite blocks already guarantee

**Status: Lean-checked before and in this PR.**

Let `M` be the common absolute terminal reward bound. Existing weighted
holonomy theorems prove for every actual finite block

\[
|B_i|\le M(1-p_i),
\qquad
|T_i|\le M(1-\chi_i).
\tag{10.1}
\]

This PR derives:

\[
\left|\frac{B_i}{1-p_i}\right|\le M
\quad (p_i\ne1),
\tag{10.2}
\]

\[
\left|\frac{T_i}{1-\chi_i}\right|\le M
\quad (\chi_i\ne1),
\tag{10.3}
\]

and, for every target `v_i`,

\[
|B_i-(1-p_i)v_i|
\le (M+|v_i|)(1-p_i),
\tag{10.4}
\]

\[
|T_i-(1-\chi_i)v_i|
\le (M+|v_i|)(1-\chi_i).
\tag{10.5}
\]

Thus prescribed and tail residuals are automatically first-order in their own
absorption masses. Their normalized anchors live in a compact interval.

On the neutral faces the weighted bounds force

\[
p_i=1\Longrightarrow B_i=0,
\tag{10.6}
\]

\[
\chi_i=1\Longrightarrow T_i=0.
\tag{10.7}
\]

Therefore an actual neutral prescribed map is literally the identity, and an
actual neutral tail map is literally `w\mapsto\max\{A_i,w\}`.

This is stronger than raw coefficient compactness and is the main concrete new
input for an escaping-middle blow-up.

---

The extended positive early-obstacle coordinate and its exact max-plus
negative/zero/positive dynamics are developed in
[SelfSimilarityExtendedObstacle.md](SelfSimilarityExtendedObstacle.md). The
Puiseux rate stratification, Big-Match interpretation, producer theorem,
compact-semigroup boundary, enriched packet, and computational program continue
in [SelfSimilarityResearchProgram.md](SelfSimilarityResearchProgram.md).
