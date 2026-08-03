# Question 133: One-Seam Closing and Buffered Descent for Compact Relations

## Objective

Separate three ideas which are often conflated:

1. recurrence by an exact path with one small closing mismatch;
2. standard chain recurrence, which permits a small mismatch at every step;
3. strict descent of a prescribed continuous ranking.

Prove the strongest valid compactness theorem connecting these notions, give
explicit counterexamples to the invalid implications, and identify the extra
finite-dimensional duality needed for a separator to have strictly positive
coordinates and an actionwise Bellman representation.

The question is entirely about compact relations and finite controlled
transition systems. No game-theoretic interpretation may be assumed.

## 1. Compact relations and exact paths

Let \((X,d)\) be a compact metric space and let

\[
R\subseteq X\times X
\]

be a relation. It is **serial** if

\[
\forall x\in X\ \exists y\in X:\quad xRy.
\tag{1}
\]

For \(K\subseteq X\), say that \(R\) is **serial on \(K\)** if

\[
\forall x\in K\ \exists y\in K:\quad xRy.
\tag{2}
\]

An exact \(R\)-path of \(m\) edges is a sequence

\[
x_0Rx_1R\cdots Rx_m.
\tag{3}
\]

For \(\eta>0\), an exact path segment is an
**\(\eta\)-one-seam return** if

\[
d(x_0,x_m)<\eta.
\tag{4}
\]

All internal transitions in (4) are exact. The only mismatch is the
identification of \(x_m\) with \(x_0\).

For a totally bounded set \(K\), let \(N_\eta(K)\) be the least cardinality of
a cover of \(K\) by sets of diameter strictly less than \(\eta\).

### Part A: bounded downstream one-seam return

Prove:

> **Theorem A.** If \(R\) is serial on a nonempty compact set \(K\), then for
> every \(x_0\in K\) and every \(\eta>0\), there is an exact path
> \[
> x_0Rx_1R\cdots Rx_N,\qquad N\le N_\eta(K),
> \]
> and indices \(0\le p<q\le N\) such that
> \[
> d(x_p,x_q)<\eta.
> \tag{5}
> \]
> Thus \(x_pRx_{p+1}R\cdots Rx_q\) is a downstream one-seam return after a
> transient of at most \(N_\eta(K)-1\) edges.

Determine exactly which hypotheses are used. In particular:

1. Is total boundedness sufficient?
2. Is closedness of \(R\) needed?
3. Is the covering-number bound sharp, up to the convention of counting
   vertices versus edges?
4. Give a finite discrete example attaining the optimal bound.

Also show why Theorem A does not promise a return based at the prescribed
entry \(x_0\).

## 2. Standard chain recurrence is different

Give \(X\times X\) the maximum product metric. An
\(\eta\)-pseudo-edge from \(x\) to \(y\) means

\[
\operatorname{dist}((x,y),R)<\eta.
\tag{6}
\]

A point \(x\) is **chain recurrent** if for every \(\eta>0\) there is a finite
closed sequence

\[
x=x_0,x_1,\ldots,x_m=x
\]

such that every \((x_k,x_{k+1})\) is an \(\eta\)-pseudo-edge.

### Part B: separate many seams from one seam

Prove that arbitrarily small exact one-seam returns based at \(x\) imply
standard chain recurrence of \(x\). Refute the converse explicitly.

One proposed counterexample is the following. Let \(X=\mathbb R/\mathbb Z\)
and let \(f:X\to X\) be the time-one map of the flow

\[
\dot\theta=\sin^2(2\pi\theta).
\tag{7}
\]

Let \(R\) be the graph of \(f\).

Prove all of the following:

1. \(f\) is a homeomorphism and fixes exactly \(0\) and \(1/2\).
2. On each complementary open arc, every exact forward orbit moves
   monotonically toward the next fixed point.
3. Every point of \(X\) is chain recurrent: a pseudo-orbit may cross the two
   fixed points using two arbitrarily small jumps.
4. If \(x\in(0,1/2)\), then for some \(\eta_x>0\),
   \[
   d(f^n(x),x)\ge\eta_x\qquad(n\ge1).
   \tag{8}
   \]
   Hence \(x\) has no \(\eta_x\)-one-seam exact return based at \(x\).

State a correct sufficient hypothesis under which standard chain recurrence
can be converted to one-seam closing. A shadowing, periodic-shadowing,
specification, or explicit closing hypothesis is admissible, but define it
precisely and prove the claimed implication. Do not merely cite “Conley
theory”: ordinary chain recurrence itself permits an error at every step.

## 3. A prescribed ranking need not descend uniformly

Let

\[
f(x)=\frac{x}{1+x},\qquad
D(x)=1+x,\qquad x\in[0,1].
\tag{9}
\]

### Part C: positive plateau with vanishing finite-step decrement

Prove:

1. \(f\) is continuous and
   \[
   f^n(x)=\frac{x}{1+nx}.
   \tag{10}
   \]
2. The chain-recurrent set of \(f\) is \(\{0\}\).
3. Every \(x>0\) satisfies \(D(f(x))<D(x)\).
4. Along the orbit from \(1\),
   \[
   f^n(1)=\frac1{n+1},\qquad D(f^n(1))\downarrow1.
   \tag{11}
   \]
5. For every fixed \(L\ge1\),
   \[
   D(x)-D(f^L(x))
   =\frac{Lx^2}{1+Lx}\longrightarrow0
   \quad(x\downarrow0).
   \tag{12}
   \]

Deduce that there do not exist fixed \(L\ge1\) and \(c>0\) such that every
point on the forward orbit of \(1\) has some \(k\le L\) with

\[
D(f^k(x))\le D(x)-c.
\tag{13}
\]

This must be presented as a counterexample even though:

- the ambient space is compact;
- the dynamics is continuous, hence its graph is closed and serial;
- no chain-recurrent point is reached at any finite time from \(1\);
- the ranking is strictly decreasing at every finitely reached point; and
- the ranking has a strictly positive limiting plateau.

Then prove the following valid uniformization statement:

> **Theorem C.** Let \(R\) be closed on compact \(X\), let \(K\subseteq X\)
> be compact, and let \(D:X\to\mathbb R\) be continuous. If
> \[
> xRy,\ x\in K\quad\Longrightarrow\quad D(y)<D(x),
> \tag{14}
> \]
> then there is \(c_K>0\) such that
> \[
> xRy,\ x\in K\quad\Longrightarrow\quad D(y)\le D(x)-c_K.
> \tag{15}
> \]

Explain why the weaker condition

\[
\forall x\in K\ \exists y:\quad xRy\ \text{ and }\ D(y)<D(x)
\tag{16}
\]

does not give (15) for all admissible successors. Decide whether it gives a
uniform decrement for a selected successor under closed graph alone; if not,
give a compact counterexample and state an adequate additional continuity
hypothesis on the set-valued map \(x\mapsto R(x)\).

## 4. Buffered return or exit

Let \(R\) now be serial on all of compact \(X\), let
\(\Phi:X\to\mathbb R\) be continuous, and choose \(a>b\). Put

\[
K_b=\{x\in X:\Phi(x)\ge b\}.
\tag{17}
\]

### Part D: the strongest topology-only finite fork

Prove:

> **Theorem D.** From every \(x_0\) satisfying \(\Phi(x_0)\ge a\), and for
> every \(\eta>0\), one can construct an exact \(R\)-path of at most
> \(N_\eta(K_b)\) edges for which at least one of the following holds:
>
> 1. the path contains a downstream \(\eta\)-one-seam return lying in \(K_b\);
> 2. the path reaches \(y\notin K_b\), and hence
>    \[
>    \Phi(x_0)-\Phi(y)>a-b.
>    \tag{18}
>    \]

The intended construction chooses a successor in \(K_b\) whenever one exists
and exits only when the restricted relation ceases to be serial.

Prove the theorem carefully, including boundary cases. Explain why it is
incorrect to paraphrase it as “absence of chain recurrence produces a
Lyapunov function.” At fixed \(\eta\), downstream one-seam return is forced by
total boundedness whenever restricted seriality persists.

## 5. What a finite decoder must add

Theorem D counts relation edges and controls only the observable \(\Phi\).
Introduce the following abstract additional data:

- a positive integer cost \(\ell(x,y)\) for each exact edge \(xRy\);
- a bound \(B<\infty\) with \(\ell(x,y)\le B\);
- for each requested accuracy \(\varepsilon>0\), a scale
  \(\eta(\varepsilon)>0\);
- a predicate \(\operatorname{Repair}_\varepsilon\) on finite exact paths;
- a predicate \(\operatorname{Drop}_c\) on finite exact paths from an entry;
- an anchor space \(\Lambda\) and an anchor map \(\lambda:X\to\Lambda\).

### Part E: a bounded-cost decoder theorem

State and prove a theorem with the following exact interfaces:

1. every downstream exact segment in \(K_b\) whose endpoints are within
   \(\eta(\varepsilon)\), and whose anchor data satisfy a stated persistence
   condition, has \(\operatorname{Repair}_\varepsilon\);
2. every first-exit path from \(K_b\) has
   \(\operatorname{Drop}_{a-b}\);
3. exact concatenation preserves the entry and anchor data needed by the two
   predicates.

Deduce that every entry with \(\Phi\ge a\) produces, at total edge cost at most

\[
B\,N_{\eta(\varepsilon)}(K_b),
\tag{19}
\]

either a certified repair or a certified strict drop.

The statement must make clear that none of the following follows from compact
topology alone:

- a uniform bound on the cost of one relation edge;
- persistence of an anchor after discarding a transient prefix;
- continuity of the repair decoder in the seam metric;
- identification of the local observable drop with an objective measured at
  the original entry; or
- the existence of an exact completion after an exit.

Give a counterexample for at least two omitted interfaces. In particular,
show how a projection which forgets a discrete anchor can display a close
one-seam loop although no anchor-compatible loop exists, and how unbounded
edge costs destroy (19) despite a covering-number bound in relation edges.

## 6. Separation, positive normals, and Bellman duality

For a nonempty compact convex set \(C\subseteq\mathbb R^n\), define its support
function

\[
h_C(\alpha)=\sup_{c\in C}\alpha\cdot c.
\tag{20}
\]

A **strictly positive welfare ceiling at \(v\)** is a vector
\(\alpha\in\mathbb R^n\) with every \(\alpha_i>0\) and

\[
h_C(\alpha)\le\alpha\cdot v.
\tag{21}
\]

### Part F1: generic separation does not give positive weights

Let

\[
C=\operatorname{conv}\{(1,0),(0,1)\},
\qquad v=(0.4,0.4).
\tag{22}
\]

Prove that \(C\) and \(\{v\}\) are compact, convex, disjoint, and strongly
separable, but (21) fails for every \(\alpha\gg0\). Identify a separating
normal and explain its sign.

Give a necessary-and-sufficient convex-geometric condition for (21), stated
either through the support function, the normal cone of a suitable
downward-comprehensive hull, or proper Pareto support. Distinguish
\(\alpha\ge0\), \(\alpha\ne0\), from the stronger requirement
\(\alpha\gg0\).

### Part F2: the occupation-measure theorem

Let \(S\) be a finite nonempty state set. For each \(s\in S\), let \(A(s)\) be
a finite nonempty action set. Let

\[
P(t\mid s,a)\ge0,\qquad
\sum_{t\in S}P(t\mid s,a)=1,
\tag{23}
\]

and let \(r(s,a)\in\mathbb R^n\). Define the invariant
occupation-measure polytope \(\Omega\) by all arrays
\(\mu(s,a)\ge0\) satisfying

\[
\sum_{s,a}\mu(s,a)=1
\tag{24}
\]

and, for every \(t\in S\),

\[
\sum_{a\in A(t)}\mu(t,a)
=
\sum_{s\in S}\sum_{a\in A(s)}
\mu(s,a)P(t\mid s,a).
\tag{25}
\]

Fix \(v\in\mathbb R^n\) and fixed weights \(\alpha\gg0\). Prove the equivalence

\[
\sup_{\mu\in\Omega}
\sum_{s,a}\mu(s,a)\,
\alpha\cdot(r(s,a)-v)
\le0
\tag{26}
\]

if and only if there exists \(H:S\to\mathbb R\) such that, for every
\(s\in S\) and \(a\in A(s)\),

\[
\alpha\cdot r(s,a)
+\sum_{t\in S}P(t\mid s,a)H(t)
\le
\alpha\cdot v+H(s).
\tag{27}
\]

Supply a complete finite-dimensional linear-programming proof, including
feasibility and dual attainment. Then telescope (27) to derive the finite-time
bound

\[
\frac1N\,
\mathbb E\!\left[
\sum_{k=0}^{N-1}\alpha\cdot r(s_k,a_k)
\right]
\le
\alpha\cdot v+
\frac{\max H-\min H}{N}
\tag{28}
\]

for every history-dependent randomized control rule and every initial state.

Finally, explain precisely why strong separation of some other nonconvex
reachable set, a local cell, or a projected continuation set does not imply
(26), does not force \(\alpha\gg0\), and does not by itself provide any
coordinatewise lower or security bounds.

## 7. Required resolution

A complete answer must provide:

1. proofs of Theorems A, C, and D;
2. the heteroclinic-circle and positive-plateau counterexamples with every
   claimed recurrence and quantitative property checked;
3. one precise closing hypothesis converting standard chain recurrence into
   the form of one-seam closing it actually implies;
4. a minimal bounded-cost decoder theorem for Part E, together with
   counterexamples showing why its interfaces cannot be omitted;
5. the positive-normal counterexample and a correct convex-geometric
   characterization; and
6. the occupation-measure/Bellman-bias equivalence and telescope.

If any displayed theorem is false as stated, give an explicit compact
counterexample, identify the failed hypothesis, and replace it with the
strongest correct statement. Do not repair a false implication by silently
changing standard chain recurrence into exact one-seam recurrence, or by
renaming an unrelated Lyapunov function as the prescribed objective.

## Answer

# Logical structure

The valid implications are

[
\boxed{\text{arbitrarily small exact one-seam returns based at }x}
\Longrightarrow
\boxed{x\text{ is chain recurrent}},
]

but not conversely, and

[
\boxed{\text{strict decrease on every edge from a compact set}}
\Longrightarrow
\boxed{\text{a uniform one-edge decrease}},
]

but pointwise strict decrease along a nonclosed orbit, or existence of one decreasing successor at each state, does not suffice.

Independently, seriality on a totally bounded region gives a fixed-scale downstream one-seam return after a bounded transient. This is a pigeonhole statement, not a chain-recurrence or Lyapunov theorem.

---

# Part A. Bounded downstream one-seam return

Let

[
q=N_\eta(K).
]

Choose a cover

[
K=U_1\cup\cdots\cup U_q,
\qquad
\operatorname{diam}(U_j)<\eta.
]

Because (R) is serial on (K), starting from (x_0\in K) we may choose successively

[
x_0Rx_1R\cdots Rx_q,
\qquad x_j\in K.
]

There are (q+1) vertices and only (q) covering sets. Assign to each (x_j) one index (i(j)) such that (x_j\in U_{i(j)}). By pigeonhole, there are

[
0\le p<r\le q
]

with (i(p)=i(r)). Hence (x_p,x_r\in U_{i(p)}), so

[
d(x_p,x_r)<\eta.
]

Taking (N=q) proves Theorem A. Since (p<r\le q),

[
p\le q-1=N_\eta(K)-1.
]

Thus the transient before the downstream return has at most (N_\eta(K)-1) edges.

## Exact hypotheses used

Only the following were used:

1. (x_0\in K);
2. every (x\in K) has an (R)-successor in (K);
3. (K) admits a finite cover by sets of diameter (<\eta).

Consequently:

* Total boundedness of (K) is sufficient.
* Compactness is stronger than necessary.
* Closedness of (R) is not used.
* Completeness of (K) is not used.
* No limiting argument is involved.

## Sharpness

Fix (q\ge2), let

[
K={0,1,\ldots,q-1},
]

with the discrete metric

[
d(i,j)=
\begin{cases}
0,&i=j,\
1,&i\ne j,
\end{cases}
]

and choose (0<\eta\le1). Then every set of diameter (<\eta) is a singleton, so

[
N_\eta(K)=q.
]

Define the deterministic relation

[
0R1R2R\cdots R(q-1),
\qquad
(q-1)R(q-1).
]

Starting from (0), the path is forced:

[
0,1,\ldots,q-1,q-1,\ldots
]

The first (q) vertices

[
x_0,\ldots,x_{q-1}
]

are distinct, so no (\eta)-one-seam return occurs in fewer than (q) edges. The first one occurs after exactly (q) edges, between (x_{q-1}) and (x_q).

This also shows why Theorem A does not give a return based at (x_0): starting from (0), no positive-length exact path ever returns within distance (<\eta) of (0). The only return is based at the downstream fixed point (q-1).

---

# Part B. One seam versus many seams

## Based exact one-seam returns imply chain recurrence

Suppose that for every (\eta>0) there is an exact path

[
x=x_0Rx_1R\cdots Rx_m
]

with (m\ge1) and

[
d(x_m,x)<\eta.
]

Consider the closed sequence

[
z_0=x_0,\ z_1=x_1,\ldots,z_{m-1}=x_{m-1},\ z_m=x_0.
]

Every edge except the last is exact. For the last edge,

[
(x_{m-1},x_m)\in R,
]

and therefore, in the maximum product metric,

[
\operatorname{dist}\bigl((x_{m-1},x_0),R\bigr)
\le d(x_0,x_m)<\eta.
]

Thus (z_0,\ldots,z_m) is a closed (\eta)-pseudo-orbit based at (x). Hence (x) is chain recurrent.

The implication uses the exact final edge (x_{m-1}Rx_m); the seam replaces only its target (x_m) by the nearby point (x_0).

---

## The heteroclinic circle

Let

[
X=\mathbb R/\mathbb Z
]

with its circle metric, and consider

[
\dot\theta=\sin^2(2\pi\theta).
]

Write (\phi_t) for the flow and (f=\phi_1).

### 1. Homeomorphism and fixed points

The vector field is smooth on the compact circle, so its flow exists for all (t\in\mathbb R), and

[
\phi_t^{-1}=\phi_{-t}.
]

Thus (f) is a homeomorphism.

The vector field vanishes exactly at

[
0,\qquad \frac12.
]

These are fixed by the entire flow. On either complementary arc the vector field is strictly positive, so every nonconstant trajectory moves strictly forward and cannot be fixed by (f). Hence the fixed-point set of (f) is exactly

[
\operatorname{Fix}(f)=\left{0,\frac12\right}.
]

A useful exact identity on either complementary arc is

[
\frac{d}{dt}\cot(2\pi\theta(t))
===============================

-2\pi.
]

Thus

[
\cot(2\pi\theta(t))
===================

\cot(2\pi\theta(0))-2\pi t.
]

### 2. Exact forward dynamics

On the arc

[
A_0=\left(0,\frac12\right),
]

every forward orbit increases strictly and satisfies

[
f^n(x)\longrightarrow \frac12.
]

Its backward orbit satisfies

[
f^{-n}(x)\longrightarrow0.
]

On

[
A_1=\left(\frac12,1\right),
]

every forward orbit increases toward (1), which is the same circle point as (0):

[
f^n(x)\longrightarrow0
\quad\text{in }\mathbb R/\mathbb Z,
]

while

[
f^{-n}(x)\longrightarrow\frac12.
]

The equilibria cannot be crossed in finite continuous time, consistently with the uniqueness of solutions and the divergence of the integral of (\csc^2(2\pi\theta)) near either zero.

### 3. Every point is chain recurrent

The fixed points are chain recurrent by their exact self-loops.

Take first (x\in A_0), and fix (\eta>0). Let

[
p=\frac12,\qquad q=0.
]

Choose (M) such that

[
d(f^M(x),p)<\eta.
]

Choose (z\in A_1) with

[
d(z,p)<\eta.
]

Since ((p,p)) belongs to the graph of (f),

[
\operatorname{dist}\bigl((f^M(x),z),\operatorname{graph}(f)\bigr)
\le
\max{d(f^M(x),p),d(z,p)}<\eta.
]

Thus one (\eta)-pseudo-edge crosses the fixed point (p).

Next choose (L) so that

[
d(f^L(z),q)<\eta.
]

Since (f^{-N}(x)\to q), choose (N) such that

[
d(f^{-N}(x),q)<\eta.
]

Again ((q,q)\in\operatorname{graph}(f)), so

[
\bigl(f^L(z),f^{-N}(x)\bigr)
]

is an (\eta)-pseudo-edge. The sequence

[
x,f(x),\ldots,f^M(x),
z,f(z),\ldots,f^L(z),
f^{-N}(x),f^{-(N-1)}(x),\ldots,x
]

is a closed (\eta)-pseudo-orbit. Only the two transitions crossing (p) and (q) are inexact.

For (x\in A_1), use the same construction with the roles of (0) and (1/2) interchanged: follow the exact orbit toward (0), jump into (A_0), follow it toward (1/2), jump to a sufficiently remote backward iterate of (x), and then follow exactly back to (x).

Therefore every point of (X) is chain recurrent.

### 4. No based exact one-seam return in the first arc

Fix (x\in(0,1/2)). For every (n\ge1),

[
x<f^n(x)<\frac12.
]

Since the ordinary difference is (<1/2), it equals the circle distance. Thus

[
d(f^n(x),x)
===========

f^n(x)-x
\ge f(x)-x.
]

Set

[
\eta_x=f(x)-x>0.
]

Then

[
d(f^n(x),x)\ge\eta_x
\qquad(n\ge1).
]

So (x) has no (\eta_x)-one-seam exact return based at (x), despite being chain recurrent.

This is precisely the distinction between two small errors, one at each fixed point, and one single closing error after an otherwise exact orbit based at (x).

---

## A sufficient closing hypothesis

A relation (R) has the **base-preserving finite shadowing property at (x)** if, for every (\varepsilon>0), there is (\delta>0) such that every finite (\delta)-pseudo-path

[
z_0=x,z_1,\ldots,z_m
]

is shadowed by an exact path

[
y_0=xRy_1R\cdots Ry_m
]

with

[
d(y_k,z_k)<\varepsilon
\qquad(1\le k\le m).
]

This is stronger than ordinary shadowing because the exact shadowing path is required to start at the prescribed point (x), not merely near it.

If (x) is chain recurrent and (R) has this property at (x), then (x) has arbitrarily small exact one-seam returns based at (x). Indeed, given (\varepsilon>0), choose the corresponding (\delta). Chain recurrence supplies a closed (\delta)-pseudo-orbit

[
z_0=x,\ldots,z_m=x.
]

Its base-preserving shadow is an exact path

[
x=y_0Ry_1R\cdots Ry_m
]

with

[
d(y_m,x)=d(y_m,z_m)<\varepsilon.
]

Ordinary unanchored shadowing or periodic shadowing would generally produce a nearby exact or periodic orbit; it need not produce a return along the exact orbit starting at (x).

---

# Part C. Positive plateau with vanishing finite-step decrement

Let

[
f(x)=\frac{x}{1+x},
\qquad
D(x)=1+x.
]

## Iterates

Inductively,

[
f^{n+1}(x)
==========

# \frac{x/(1+nx)}{1+x/(1+nx)}

\frac{x}{1+(n+1)x}.
]

Thus

[
f^n(x)=\frac{x}{1+nx}.
]

In particular,

[
f^n(1)=\frac1{n+1}.
]

## Chain-recurrent set

Clearly (f(0)=0), so (0) is chain recurrent.

Fix (x>0), and put

[
q=\frac{x}{2}.
]

The one-step gap is

[
g(u)=u-f(u)=\frac{u^2}{1+u}.
]

Let

[
\gamma=\min_{u\in[q/2,1]}g(u)>0.
]

Choose (\eta>0) sufficiently small that

[
\eta<\frac q2,\qquad
2\eta<\frac\gamma2,
\qquad
f(q+\eta)+\eta<q.
]

If ((u,v)) is an (\eta)-pseudo-edge, there is (z\in[0,1]) with

[
|u-z|<\eta,
\qquad
|v-f(z)|<\eta.
]

If (u\ge q), then (z\ge q/2), and hence

[
\begin{aligned}
v
&<f(z)+\eta\
&=z-g(z)+\eta\
&\le u+\eta-\gamma+\eta\
&<u-\frac\gamma2.
\end{aligned}
]

If (u\le q), then (z<q+\eta), so, using monotonicity of (f),

[
v<f(q+\eta)+\eta<q.
]

Therefore:

* every pseudo-edge whose source is at least (q) decreases the state by at least (\gamma/2);
* the interval ([0,q]) is forward invariant under (\eta)-pseudo-edges.

A closed (\eta)-pseudo-orbit based at (x>q) is impossible. If it never enters ([0,q]), its entries strictly decrease by at least (\gamma/2). If it enters ([0,q]), it can never return to (x).

Hence

[
\operatorname{CR}(f)={0}.
]

## Strict decrease and plateau

For (x>0),

[
D(f(x))=1+\frac{x}{1+x}<1+x=D(x).
]

Along the orbit from (1),

[
D(f^n(1))
=========

1+\frac1{n+1}
\downarrow1.
]

The limiting plateau is strictly positive.

For fixed (L),

[
\begin{aligned}
D(x)-D(f^L(x))
&=
x-\frac{x}{1+Lx}\
&=
\frac{Lx^2}{1+Lx}
\longrightarrow0
\end{aligned}
]

as (x\downarrow0).

More generally, for (1\le k\le L),

[
D(x)-D(f^k(x))
==============

\frac{kx^2}{1+kx}
\le Lx^2.
]

Taking (x=f^n(1)=1/(n+1)), the right-hand side tends to zero uniformly over (k\le L). Consequently, for every fixed (L) and (c>0), some sufficiently late point (x) on the orbit satisfies

[
D(f^k(x))>D(x)-c
\qquad(1\le k\le L).
]

Thus no (L,c) satisfying (13) exist.

This counterexample has all the advertised properties:

* (X=[0,1]) is compact.
* (f) is continuous, so its graph is closed and serial.
* The only chain-recurrent point is (0), which is not reached in finite time from (1).
* (D) strictly decreases at every finitely reached point.
* (D) converges to the positive plateau (1).
* Nevertheless, every fixed-window decrement vanishes near the limiting point.

There is no contradiction with Theorem C below: the forward orbit without its limit is not compact, while its compact closure contains (0), where strict descent fails.

---

## Theorem C

Let

[
E=R\cap(K\times X).
]

Since (R) is closed and (K\times X) is compact, (E) is compact.

Define

[
\Delta(x,y)=D(x)-D(y).
]

The hypothesis says

[
\Delta(x,y)>0
\qquad((x,y)\in E).
]

If (E=\varnothing), the conclusion is vacuous and any (c_K>0) works. Otherwise, continuity of (\Delta) and compactness of (E) give

[
c_K=\min_{(x,y)\in E}\Delta(x,y)>0.
]

Therefore

[
D(y)\le D(x)-c_K
]

for every (xRy) with (x\in K).

Seriality is not needed for this theorem.

---

## Existentially decreasing successors

The condition

[
\forall x\in K\ \exists y\in R(x):
\quad D(y)<D(x)
]

does not imply decrease along every admissible successor. It does not even imply a uniform decrement after choosing one successor at each (x), under closed graph alone.

Let

[
X={-1,0}\cup\left{\frac1n:n\ge1\right}
\subset\mathbb R,
\qquad
K={0}\cup\left{\frac1n:n\ge1\right},
]

and let (D(x)=x). Define

[
R=
\left{
\left(\frac1n,\frac1{n+1}\right):n\ge1
\right}
\cup
{(0,0),(0,-1),(-1,-1)}.
]

The graph is closed: the only nontrivial limiting sequence of edges is

[
\left(\frac1n,\frac1{n+1}\right)\longrightarrow(0,0),
]

and ((0,0)\in R).

At (x=1/n), the unique successor (1/(n+1)) decreases (D). At (x=0), the successor (-1) decreases (D). Thus the existential condition holds.

But:

* the admissible edge (0R0) does not decrease (D);
* at (1/n), every selected successor must be (1/(n+1)), whose decrement is

[
\frac1n-\frac1{n+1}
===================

\frac1{n(n+1)}
\longrightarrow0.
]

Hence no uniform selected decrement exists.

### An adequate additional condition

Let (F(x)=R(x)). Assume, in addition to compact nonempty values, that (F) is **lower hemicontinuous on (K)**:

for every (x\in K), every (y\in F(x)), and every neighborhood (U) of (y), there is a neighborhood (V) of (x) such that

[
F(x')\cap U\ne\varnothing
\qquad(x'\in V\cap K).
]

Define

[
m(x)=\min_{y\in F(x)}D(y).
]

The minimum exists because the fibers are compact. Lower hemicontinuity of (F) implies upper semicontinuity of (m): if (y) minimizes (D) on (F(x)), nearby fibers contain points near (y), so their minima cannot jump upward.

Therefore

[
\delta(x)=D(x)-m(x)
]

is lower semicontinuous. Under the existential strict-decrease condition,

[
\delta(x)>0
\qquad(x\in K).
]

A positive lower-semicontinuous function on compact (K) attains a positive minimum:

[
c_K=\min_{x\in K}\delta(x)>0.
]

Choosing at each (x) a minimizer (y_x\in F(x)) gives

[
D(y_x)\le D(x)-c_K.
]

Closed graph supplies upper hemicontinuity in this compact setting; the missing direction in the counterexample is lower hemicontinuity. No continuous selector is asserted or needed.

---

# Part D. Buffered return or exit

Let

[
q=N_\eta(K_b),
\qquad
K_b={x:\Phi(x)\ge b}.
]

Since (\Phi(x_0)\ge a>b), we have (x_0\in K_b).

Fix a cover

[
K_b=U_1\cup\cdots\cup U_q,
\qquad
\operatorname{diam}(U_j)<\eta.
]

Construct a path recursively.

At a current state (x_j\in K_b):

* if (R(x_j)\cap K_b\ne\varnothing), choose (x_{j+1}\in R(x_j)\cap K_b);
* if (R(x_j)\cap K_b=\varnothing), global seriality supplies (y\in R(x_j)), and necessarily (y\notin K_b). Set (x_{j+1}=y) and stop.

If an exit occurs at stage (j), before a repeated covering set has appeared, then (j\le q-1). Thus the exit path has at most

[
j+1\le q
]

edges. Since (x_{j+1}\notin K_b),

[
\Phi(x_{j+1})<b.
]

Therefore

[
\Phi(x_0)-\Phi(x_{j+1})

>

a-b.
]

If no exit occurs in the first (q) edges, then

[
x_0,\ldots,x_q\in K_b.
]

Assign each vertex one cover index containing it. Two of the (q+1) vertices have the same index, so for some

[
0\le p<r\le q
]

we have

[
d(x_p,x_r)<\eta.
]

All vertices of the exact segment

[
x_pRx_{p+1}R\cdots Rx_r
]

lie in (K_b).

This proves Theorem D, including the boundary cases:

* (x_0) may satisfy (\Phi(x_0)=a);
* an exit point always satisfies the strict inequality (\Phi(y)<b);
* (K_b) is nonempty because it contains (x_0);
* if (N_\eta(K_b)=1), either the first edge exits or one in-(K_b) edge already closes within (\eta).

As in Theorem A, closedness of (R) is not used. In fact, compactness and continuity can be weakened to the requirement that (K_b) be totally bounded. Since every subset of a totally bounded space is totally bounded, compactness of (X) already gives that property even without continuity of (\Phi).

## Why this is not a Lyapunov theorem

The construction does not show that (\Phi) decreases along any internal edge. It gives only:

* a fixed-scale downstream one-seam return if restricted seriality persists; or
* a threshold-crossing endpoint if restricted seriality fails along the constructed path.

The return may be based at a downstream point depending on (\eta), and different scales may produce entirely different points. Standard chain recurrence requires closed pseudo-orbits based at one prescribed point for every scale. Conversely, absence of chain recurrence does not make a prescribed (\Phi) decrease, as the positive-plateau example shows.

---

# Part E. A bounded-cost decoder theorem

For a finite exact path

[
\gamma=(x_0,\ldots,x_m),
]

define its cost by

[
L(\gamma)=\sum_{j=0}^{m-1}\ell(x_j,x_{j+1}).
]

If

[
\rho=(x_0,\ldots,x_p),
\qquad
\sigma=(x_p,\ldots,x_q),
]

write (\rho\star\sigma=(x_0,\ldots,x_q)).

Call a path **anchor-persistent** if

[
\lambda(x_0)=\lambda(x_1)=\cdots=\lambda(x_m).
]

Call (\gamma=(x_0,\ldots,x_m)) a **first-exit path from (K_b)** if

[
x_0,\ldots,x_{m-1}\in K_b,
\qquad
x_m\notin K_b.
]

## Buffered bounded-cost decoder theorem

Assume:

### Anchor-preserving restricted choice

For every (x\in K_b),

[
R(x)\cap K_b\ne\varnothing
]

implies that there is some

[
y\in R(x)\cap K_b
]

with

[
\lambda(y)=\lambda(x).
]

### Local seam decoder

For every (\varepsilon>0), every nontrivial anchor-persistent exact segment

[
\sigma=(z_0,\ldots,z_r),
\qquad r\ge1,
]

lying in (K_b) and satisfying

[
d(z_0,z_r)<\eta(\varepsilon),
]

has

[
\operatorname{Repair}_\varepsilon(\sigma).
]

### Prefix lifting

If

[
\gamma=\rho\star\sigma
]

is an anchor-persistent exact path lying in (K_b), and

[
\operatorname{Repair}_\varepsilon(\sigma),
]

then

[
\operatorname{Repair}_\varepsilon(\gamma).
]

This is the interface that transports a repair found after discarding a transient back to the original entry.

### Exit decoder

Every first-exit path

[
\gamma=(x_0,\ldots,x_m)
]

with

[
\Phi(x_0)\ge a
]

has

[
\operatorname{Drop}_{a-b}(\gamma).
]

### Bounded edge cost

For every exact edge,

[
1\le \ell(x,y)\le B.
]

Then every entry (x_0) with (\Phi(x_0)\ge a) admits a finite exact path (\gamma) such that

[
L(\gamma)
\le
B,N_{\eta(\varepsilon)}(K_b),
]

and either

[
\operatorname{Repair}_\varepsilon(\gamma)
]

or

[
\operatorname{Drop}_{a-b}(\gamma)
]

holds.

## Proof

Run the construction from Theorem D, but whenever an in-(K_b) successor exists, choose an anchor-preserving one. By induction, every pre-exit path is anchor-persistent.

Let

[
q=N_{\eta(\varepsilon)}(K_b).
]

If the construction exits, it produces a first-exit path of at most (q) edges. The exit-decoder assumption gives

[
\operatorname{Drop}_{a-b}(\gamma).
]

If the construction does not exit, it produces a path of at most (q) edges containing a downstream exact segment

[
\sigma=(x_p,\ldots,x_r)
]

with all vertices in (K_b) and

[
d(x_p,x_r)<\eta(\varepsilon).
]

The segment is anchor-persistent, so the local decoder gives

[
\operatorname{Repair}_\varepsilon(\sigma).
]

Writing the whole path as (\gamma=\rho\star\sigma), prefix lifting gives

[
\operatorname{Repair}_\varepsilon(\gamma).
]

Finally, if (\gamma) has (m\le q) edges,

[
L(\gamma)
=========

\sum_{j=0}^{m-1}\ell(x_j,x_{j+1})
\le Bm
\le Bq.
]

---

## Why the additional interfaces are genuine

### 1. A projection may forget the anchor

Let the full state space be

[
\widetilde X={u_0,u_1},
]

with anchors

[
\lambda(u_0)=0,\qquad \lambda(u_1)=1.
]

Let

[
u_0\widetilde R u_1,
\qquad
u_1\widetilde R u_1.
]

Project both states to one observable point:

[
\pi(u_0)=\pi(u_1)=z.
]

The projected relation on (X={z}) contains the exact loop

[
zRz.
]

Its seam mismatch is zero. But every positive-length full path starting from (u_0) ends at anchor (1). There is no anchor-compatible return to anchor (0).

Thus a close loop in a quotient that forgets a discrete anchor need not lift to an anchor-compatible loop.

### 2. Compactness does not bound arbitrary edge costs

Let

[
X={0}\cup\left{\frac1n:n\ge1\right},
]

and let (R) be the identity relation. Every point has an exact one-edge zero-seam loop.

For example, with (\eta=2),

[
N_\eta(X)=1.
]

Define

[
\ell\left(\frac1n,\frac1n\right)=n,
\qquad
\ell(0,0)=1.
]

Starting from (1/n), the one-edge return costs (n). Hence no bound depending only on the number of relation edges can hold. An arbitrary integer-valued cost on a compact graph need not be bounded; continuity or an explicit bound is additional data.

### 3. Seam closeness does not imply repair continuity

On (X=[0,1]) with the identity relation, every one-edge segment has zero seam. Define the repair predicate to hold only for the loop at (0). Nothing in compact topology forces repair at the loops based at (1/n), despite their convergence to the loop at (0).

### 4. Observable drop need not equal the intended entry objective

Let (X={u,v}), (uRv), (vRv), and

[
\Phi(u)=1,\qquad \Phi(v)=0.
]

An exit from ({u}) has a unit (\Phi)-drop. But another objective may satisfy

[
J(u)=0,\qquad J(v)=1.
]

The same path worsens (J). Identifying a (\Phi)-threshold exit with a drop in another entry-based objective is a decoder assumption, not a topological consequence.

### 5. Exit does not give a designated completion

In the same two-state system, if the designated completion set is ({u}), then after exiting to (v) no exact path reaches the completion set. Seriality supplies further exact edges, but not a finite terminal or otherwise certified completion.

---

# Part F1. Generic separation and positive normals

Let

[
C=\operatorname{conv}{(1,0),(0,1)}.
]

Every (c\in C) satisfies

[
c_1+c_2=1,
]

whereas

[
v_1+v_2=0.8.
]

Thus (v\notin C). Both sets are compact and convex, and they are strongly separated by the affine hyperplane

[
x_1+x_2=0.9.
]

For (\alpha=(\alpha_1,\alpha_2)),

[
h_C(\alpha)=\max{\alpha_1,\alpha_2}.
]

If (\alpha_1,\alpha_2>0), then

[
h_C(\alpha)
\ge
\frac{\alpha_1+\alpha_2}{2}

>

# 0.4(\alpha_1+\alpha_2)

\alpha\cdot v.
]

Therefore no (\alpha\gg0) satisfies the welfare ceiling.

The normal ((1,1)) separates the sets, but with (C) above (v):

[
(1,1)\cdot c=1>0.8=(1,1)\cdot v.
]

With the ceiling orientation, one may use

[
\alpha=(-1,-1),
]

for which

[
h_C(\alpha)=-1<-0.8=\alpha\cdot v.
]

The correctly oriented separator has strictly negative, not positive, coordinates.

---

## Convex-geometric characterization

Let

[
D_C=C-\mathbb R_+^n
]

be the downward-comprehensive hull, and define

[
Q_v=
\overline{\operatorname{conv}}\bigl(D_C\cup{v}\bigr).
]

Use the normal-cone convention

[
N_{Q_v}(v)
==========

{\alpha:
\alpha\cdot(z-v)\le0
\text{ for all }z\in Q_v}.
]

Then

[
\alpha\in N_{Q_v}(v)
]

if and only if

[
\alpha\ge0
\quad\text{and}\quad
h_C(\alpha)\le\alpha\cdot v.
]

Indeed, if (\alpha\in N_{Q_v}(v)), then for any (c\in C), any coordinate (i), and any (t\ge0),

[
c-te_i\in D_C
]

and hence

[
\alpha\cdot(c-te_i-v)\le0.
]

If (\alpha_i<0), the left side tends to (+\infty) as (t\to\infty), a contradiction. Thus (\alpha\ge0). Taking (t=0) gives

[
\alpha\cdot c\le\alpha\cdot v
]

for every (c\in C).

Conversely, if (\alpha\ge0) and (h_C(\alpha)\le\alpha\cdot v), then for (c-u\in D_C),

[
\alpha\cdot(c-u)
\le
\alpha\cdot c
\le
\alpha\cdot v.
]

The inequality extends to the closed convex hull (Q_v).

Consequently,

[
\boxed{
\exists,\alpha\gg0:
h_C(\alpha)\le\alpha\cdot v
}
]

if and only if

[
\boxed{
N_{Q_v}(v)\cap\operatorname{int}\mathbb R_+^n
\ne\varnothing.
}
]

Equivalently, after normalizing (\sum_i\alpha_i=1), the feasible support-normal set must meet the relative interior of the simplex.

For merely nonnegative, nonzero weights, the condition is

[
N_{Q_v}(v)\cap
\bigl(\mathbb R_+^n\setminus{0}\bigr)
\ne\varnothing.
]

This weaker condition is equivalent to

[
C\cap\bigl(v+\operatorname{int}\mathbb R_+^n\bigr)
==================================================

\varnothing:
]

no point of (C) strictly improves every coordinate of (v). Strictly positive support is stronger; it requires a properly Pareto-supporting normal that gives positive weight to every coordinate.

For example,

[
C={(0,1)},
\qquad
v=(0,0)
]

admits the weak normal ((1,0)), but no strictly positive normal.

---

# Part F2. Occupation measures and Bellman bias

Set

[
E={(s,a):s\in S,\ a\in A(s)}.
]

For (e=(s,a)), define

[
g_e
===

\alpha\cdot(r(s,a)-v).
]

Define the flow matrix (B\in\mathbb R^{S\times E}) by

[
B_{t,(s,a)}
===========

\mathbf 1_{{t=s}}-P(t\mid s,a).
]

Then the balance equations are exactly

[
B\mu=0,
]

and normalization is

[
\mathbf 1^\top\mu=1.
]

Thus

[
\Omega
======

{\mu\ge0:B\mu=0,\ \mathbf1^\top\mu=1}.
]

## Feasibility and compactness of (\Omega)

Choose one action (a(s)\in A(s)) at each state and form the stochastic matrix

[
P_0(t\mid s)=P(t\mid s,a(s)).
]

Every finite stochastic matrix has an invariant distribution. One direct proof is to take an arbitrary distribution (q_0) and the Cesàro averages

[
\bar q_N
========

\frac1N\sum_{k=0}^{N-1}q_0P_0^k.
]

A subsequence converges in the compact probability simplex, and

[
\bar q_NP_0-\bar q_N
====================

\frac{q_0P_0^N-q_0}{N}
\longrightarrow0.
]

Any subsequential limit (\pi) satisfies (\pi P_0=\pi). Defining

[
\mu(s,a)=
\begin{cases}
\pi(s),&a=a(s),\
0,&a\ne a(s),
\end{cases}
]

gives an element of (\Omega).

The polytope (\Omega) is a closed subset of the finite-dimensional simplex, hence compact. Therefore the primal optimum

[
\rho
====

\max_{\mu\in\Omega}g^\top\mu
]

is finite and attained.

---

## The finite circulation Farkas lemma

For any vector (q\in\mathbb R^E),

[
\exists H\in\mathbb R^S:
\quad B^\top H\ge q
]

if and only if

[
q^\top\nu\le0
]

for every

[
\nu\ge0,\qquad B\nu=0.
]

The forward direction follows by multiplication:

[
q^\top\nu
\le
H^\top B\nu
===========

0.

]

For the converse, consider the closed polyhedral cone

[
\mathcal K
==========

{B^\top H-z:H\in\mathbb R^S,\ z\ge0}.
]

The desired inequality is equivalent to (q\in\mathcal K). If (q\notin\mathcal K), strong separation of a point from a closed convex cone gives a vector (\nu) such that

[
\nu^\top q>0
]

and

[
\nu^\top(B^\top H-z)\le0
]

for every (H) and (z\ge0). Varying (H) with both signs gives

[
B\nu=0.
]

Taking arbitrary (z\ge0) gives

[
\nu\ge0.
]

This contradicts the assumed circulation inequality.

---

## Primal-dual pair and attainment

The primal LP is

[
\begin{aligned}
\text{maximize }& g^\top\mu\
\text{subject to }&
B\mu=0,\
&\mathbf1^\top\mu=1,\
&\mu\ge0.
\end{aligned}
]

Its dual is

[
\begin{aligned}
\text{minimize }&\beta\
\text{subject to }&
B^\top H+\beta\mathbf1\ge g,
\end{aligned}
]

where (H\in\mathbb R^S) and (\beta\in\mathbb R) are unrestricted.

In state-action notation, dual feasibility is

[
g(s,a)
+
\sum_tP(t\mid s,a)H(t)
\le
\beta+H(s).
]

Weak duality follows immediately: if (\mu\in\Omega), then

[
\begin{aligned}
g^\top\mu
&\le
\mu^\top B^\top H+\beta,\mathbf1^\top\mu\
&=
H^\top B\mu+\beta\
&=\beta.
\end{aligned}
]

To prove dual attainment at (\rho), apply the circulation Farkas lemma to

[
q=g-\rho\mathbf1.
]

For every nonzero (\nu\ge0) satisfying (B\nu=0), put

[
\tau=\mathbf1^\top\nu>0,
\qquad
\mu=\frac{\nu}{\tau}.
]

Then (\mu\in\Omega), so

[
q^\top\nu
=========

\tau(g^\top\mu-\rho)
\le0.
]

The Farkas lemma therefore supplies (H) with

[
B^\top H\ge g-\rho\mathbf1.
]

Thus ((\beta,H)=(\rho,H)) is dual feasible. Weak duality gives equality of the primal and dual optima, and both optima are attained.

This is the finite-dimensional duality needed for an actionwise Bellman representation.

---

## Equivalence of (26) and (27)

Condition (26) is exactly

[
\rho\le0.
]

If (\rho\le0), dual attainment gives (H) satisfying

[
g(s,a)
+
\sum_tP(t\mid s,a)H(t)
\le
\rho+H(s)
\le H(s).
]

Substituting

[
g(s,a)=\alpha\cdot r(s,a)-\alpha\cdot v
]

gives

[
\alpha\cdot r(s,a)
+
\sum_tP(t\mid s,a)H(t)
\le
\alpha\cdot v+H(s),
]

which is (27).

Conversely, suppose (27) holds. Multiply it by (\mu(s,a)) and sum. The flow equations give

[
\sum_{s,a}\mu(s,a)\sum_tP(t\mid s,a)H(t)
========================================

\sum_{s,a}\mu(s,a)H(s).
]

The bias terms cancel, and normalization gives

[
\sum_{s,a}\mu(s,a)\alpha\cdot r(s,a)
\le
\alpha\cdot v.
]

Equivalently,

[
\sum_{s,a}\mu(s,a)
\alpha\cdot(r(s,a)-v)
\le0.
]

Taking the supremum over (\Omega) proves (26).

The positivity of (\alpha) is not needed for the LP duality itself. It is an independent welfare-normal requirement supplied by Part F1.

---

## Finite-time telescope

Consider any history-dependent randomized control rule. Conditional on the history up to state (s_k), the rule chooses a distribution over (A(s_k)), and then (s_{k+1}) is drawn according to the corresponding transition kernel.

Because (27) holds actionwise, averaging first over the randomized action and then over the transition gives

[
\mathbb E!\left[
\alpha\cdot r(s_k,a_k)+H(s_{k+1})
\mid\mathcal F_k
\right]
\le
\alpha\cdot v+H(s_k).
]

Taking expectations and summing from (k=0) to (N-1),

[
\mathbb E!\left[
\sum_{k=0}^{N-1}\alpha\cdot r(s_k,a_k)
\right]
\le
N\alpha\cdot v
+
\mathbb E[H(s_0)-H(s_N)].
]

Since

[
H(s_0)-H(s_N)
\le
\max H-\min H,
]

we obtain

[
\frac1N
\mathbb E!\left[
\sum_{k=0}^{N-1}\alpha\cdot r(s_k,a_k)
\right]
\le
\alpha\cdot v
+
\frac{\max H-\min H}{N}.
]

No stationarity or Markov property of the control rule is used.

---

## Why other separators are insufficient

The relevant convex set is the occupation-payoff polytope

[
C_\Omega
========

\left{
\sum_{s,a}\mu(s,a)r(s,a):
\mu\in\Omega
\right}.
]

Condition (26) is exactly

[
h_{C_\Omega}(\alpha)\le\alpha\cdot v.
]

Separating a different set does not imply this.

For example, take one state, two actions (a,b), self-loop transitions, scalar rewards

[
r(a)=-1,\qquad r(b)=1,
\qquad v=0.
]

The local set containing only action (a) lies strictly below (v). But (\Omega) also contains the occupation concentrated on (b), so

[
\sup_{\mu\in\Omega}\sum\mu r=1>0.
]

There is no Bellman bias: since (P) is the identity, the inequality for (b) would be

[
1+H(s)\le H(s),
]

which is impossible.

Likewise:

* a nonconvex reachable set may omit convex mixtures or invariant circulations;
* a local cell may cover only some actions or states;
* a projected continuation set may forget flow constraints or payoff coordinates;
* generic separation determines neither the sign nor the orientation of the normal;
* even a ceiling with (\alpha\gg0) is only a scalar trade-off bound.

For instance, with

[
\alpha=(1,1),\qquad v=(0,0),
]

the payoff vector

[
(1,-1)
]

satisfies

[
\alpha\cdot(1,-1)=0=\alpha\cdot v,
]

although its first coordinate exceeds (v_1). A weighted upper bound therefore gives neither coordinatewise upper bounds nor coordinatewise lower or security guarantees.

---

# Final separation of the three mechanisms

The strongest topology-only conclusions are:

[
\boxed{
\text{restricted seriality}+\text{total boundedness}
\Rightarrow
\text{bounded downstream one-seam return}
}
]

and the buffered variant

[
\boxed{
\text{downstream one-seam return in }K_b
\quad\text{or}\quad
\text{threshold exit from }K_b.
}
]

They do not provide recurrence based at the prescribed entry, anchor persistence, repair continuity, bounded implementation cost, or an objective-compatible completion.

Standard chain recurrence is weaker than based exact one-seam recurrence because it permits a fresh discrepancy at every pseudo-edge. Converting it to based one-seam closing requires an additional base-preserving closing or shadowing property.

Uniform strict descent of a prescribed ranking follows from compactness only when strict decrease holds on the entire compact edge set under consideration. Strict decrease merely along a nonclosed orbit, or existential availability of decreasing successors under a closed graph, permits vanishing decrements.

Finally, a positive actionwise Bellman certificate requires two separate finite-dimensional facts:

[
N_{Q_v}(v)\cap\operatorname{int}\mathbb R_+^n\ne\varnothing
]

for a strictly positive welfare normal, and

[
h_{C_\Omega}(\alpha)\le\alpha\cdot v
]

for the full invariant occupation-payoff polytope. The latter, and only the latter, is equivalent by the circulation LP duality to an actionwise Bellman-bias inequality.

---

# Audit correction: exact coverage and the two-ended gap

The abstract conclusions above are valid, but one coverage distinction must
be made explicit.

## 1. Part E is a conditional decoder theorem

The bounded-cost conclusion in Part E does **not** follow from compactness,
closedness, seriality, the cover bound, or the existence of a continuous
observable. It assumes all of the application-specific content:

1. restricted successors can be selected while preserving the anchor;
2. a close downstream exact segment with that anchor decodes as a repair;
3. the repair can be lifted across the discarded transient to the original
   entry;
4. a first exit decodes as a drop of the intended entry-based objective; and
5. relation-edge count controls implementation cost.

Thus Theorem D is unconditional topology, whereas the repair/drop statement is
the result of applying Theorem D **after** those five interfaces have been
proved. Part E does not construct any of them.

In particular, the strict inequality
\[
  \Phi(x_0)-\Phi(y)>a-b
\]
at a first exit is only a drop in the displayed observable \(\Phi\). It is
not a drop in another optimized objective unless the exit decoder proves that
identification and supplies any exact completion required by the objective.

## 2. Two compactified ends do not supply the missing anchor

The following finite example isolates the remaining non-composition.
Let
\[
  X=\{a,b\}
\]
with the discrete metric, and let
\[
  R=\{(a,a),(a,b),(b,b)\}.
\]
Give the two points different anchors:
\[
  \lambda(a)=0,\qquad \lambda(b)=1.
\]
For every \(m\ge1\), the word
\[
  \gamma_m=
  (\underbrace{a,\ldots,a}_{m+1},
   \underbrace{b,\ldots,b}_{m+1})
\]
is an exact finite \(R\)-path. Every fixed forward window converges
trivially to the exact ray \(a,a,\ldots\), while every fixed reverse window
converges to the exact reverse-end ray \(b,b,\ldots\). The forward ray has a
zero-mismatch one-seam return, and an arbitrary marked datum may be retained
at the reverse \(b\)-end.

Nevertheless no anchor-persistent segment contains both the forward
\(\lambda=0\) seam and the reverse \(\lambda=1\) datum. There is no edge
\(bRa\). The \(aRa\) loop preserves the entry anchor but discards the reverse
datum; the \(bRb\) loop retains the reverse datum but its prefix from the
entry changes anchor, so Part E's prefix-lifting premise fails. This remains
true with unit edge costs. Hence:

> common provenance of a forward exact ray and a reverse marked ray, plus a
> downstream one-seam return on the forward ray, does not imply a
> marked-anchor repair.

One needs an augmented relation which transports the marked datum through the
intervening block, or a separate holonomy/decoder theorem proving that the
datum needed by the repair is preserved. Neither Theorem A nor Theorem D
provides this.

## 3. What Parts F1 and F2 do and do not produce

Part F1 gives a necessary-and-sufficient condition for a strictly positive
normal:
\[
  N_{Q_v}(v)\cap\operatorname{int}\mathbb R_+^n\ne\varnothing.
\]
It does not prove that this intersection is nonempty for a supplied reachable
or continuation set. Generic strong separation is insufficient, as the
answer's two-dimensional example shows.

Part F2 starts with a **fixed** vector \(\alpha\) and the full invariant
occupation-measure polytope. It proves that the occupation ceiling for that
same \(\alpha\) is equivalent to an actionwise Bellman-bias inequality. It
does not:

- create a positive \(\alpha\);
- replace the full occupation polytope by a local, projected, or nonconvex
  set;
- provide coordinatewise security inequalities; or
- turn an observable exit into a repair or an optimized-objective descent.

## 4. Correct consumption rule

The answer therefore establishes four independent packets:

1. a topology-only downstream return-or-exit theorem;
2. counterexamples separating chain recurrence, exact one-seam closing, and
   uniform ranking descent;
3. a conditional bounded-cost decoder schema; and
4. a positive-normal criterion plus a finite occupation-LP duality theorem.

It does **not** establish an unconditional packet-anchored repair, an exact
completion after an exit, or a uniform descent of an optimized objective at
the original entry. Any use claiming one of those consequences must first
instantiate the anchor-persistence, seam-decoder, exit-decoder, and
cost-control hypotheses of Part E.
