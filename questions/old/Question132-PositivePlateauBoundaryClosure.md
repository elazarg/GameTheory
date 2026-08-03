# Question 132: Positive-Plateau Boundary Closure in Finite Quitting Games

## Objective

Resolve the only exceptional branch left by optimized exact finite
Nash--Bellman chains.

The input to this question is not an arbitrary quitting game with no further
structure.  It is a game for which the optimized exact zero-boundary debt has
a positive limiting plateau, together with a calibrated projective limit in
which every player's total Quit clock is summable.  That input carries two
different ends:

- a forward infinite Nash--Bellman/debt path rooted at the initial live
  history; and
- a reverse infinite tail rooted at the moving zero boundary, including a
  full simultaneous-quitter atom whose transported probability stays
  uniformly positive.

The missing operation is to couple those ends to an actual strategically
credible continuation.  The desired resolution is a finite
**repair-or-debt-descent** theorem.  A repair must be one of the explicit
table certificates below, a genuine standard-proper absorption path, or an
attainable tail meeting the acceptance polyhedron of a **positive-length
prefix from the supplied minimizing chains**.  A length-zero prefix is
forbidden: at length zero, saying that an attainable tail has small debt is
just the terminal-equilibrium existence statement itself.

The question is deliberately theorem-or-counterexample.  If the proposed
finite fork is false, identify whether its failure only refutes this boundary
architecture or gives a robust positive exploitability gap over every
behavior profile.

## 1. Finite quitting games

Let $I$ be a finite nonempty player set and put $n=|I|$.  At every live
stage, player $i$ chooses Continue, denoted $C_i$, or Quit, denoted $Q_i$.
Write

$$
A=\prod_{i\in I}\{C_i,Q_i\},\qquad
\mathbf C=(C_i)_{i\in I},\qquad
A^*=A\setminus\{\mathbf C\}.
$$

The first action profile $a\in A^*$ absorbs the game and gives the terminal
payoff $r(a)\in\mathbb R^I$.  A play which never absorbs has payoff $0$.
Fix $M<\infty$ such that

$$
|r_i(a)|\le M
\qquad(i\in I,\ a\in A^*).
\tag{1}
$$

It is often convenient to identify $a$ with its nonempty quitter set
$S(a)\subseteq I$ and to write $r(S)$.  For boundary comparisons only, put

$$
r_i(\varnothing)=0.
\tag{2}
$$

A product action is a vector $x=(x_i)_{i\in I}\in[0,1]^I$, where $x_i$ is
the probability that $i$ Quits.  Its product probability is

$$
\xi_x(a)=
\prod_{i:a_i=Q_i}x_i
\prod_{i:a_i=C_i}(1-x_i).
\tag{3}
$$

For a continuation payoff $w\in\mathbb R^I$, define

$$
g_i(x;w)=
\sum_{a\in A^*}\xi_x(a)r_i(a)+\xi_x(\mathbf C)w_i.
\tag{4}
$$

The pure-action endpoints for player $i$ are

$$
Q_i(x_{-i};w)=g_i((Q_i,x_{-i});w),\qquad
C_i(x_{-i};w)=g_i((C_i,x_{-i});w).
\tag{5}
$$

The first endpoint is independent of $w_i$.  Define also

$$
a(x)=\xi_x(\mathbf C)=\prod_j(1-x_j),\qquad
c_i(x)=\prod_{j\ne i}(1-x_j).
\tag{6}
$$

Thus $a(x)$ is full-profile survival and $c_i(x)$ is opponent-only survival
for player $i$.

Call $x$ an **exact Nash root at $w$** if, for every player $i$,

$$
g_i(x;w)=\max\{Q_i(x_{-i};w),C_i(x_{-i};w)\}.
\tag{7}
$$

Equivalently, every pure action to which $x_i$ assigns positive probability
is a best response in the one-stage game whose all-Continue outcome pays
$w$.

For a behavior profile $\sigma$, let $U_i(\sigma)$ be the expected terminal
payoff, with payoff $0$ on Never.  Its exact relative deviation debt is

$$
\beta_i(\sigma)=
\sup_{\tau_i}U_i(\tau_i,\sigma_{-i})-U_i(\sigma)\ge0,
\tag{8}
$$

where the supremum ranges over arbitrary behavioral deviations.  The
profile is a terminal $\varepsilon$-equilibrium when
$\beta_i(\sigma)\le\varepsilon$ for every $i$.

## 2. Exact zero-boundary chains and optimized debt

For $K\in\mathbb N$, an exact zero-boundary Nash--Bellman chain of length
$K$ is

$$
\mathcal C=(x^0,\ldots,x^{K-1};v^0,\ldots,v^K)
$$

such that

$$
v^K=0,
\tag{9}
$$

and, for every $t<K$,

$$
x^t\text{ is an exact Nash root at }v^{t+1},\qquad
v^t=g(x^t;v^{t+1}).
\tag{10}
$$

Write $\mathcal N_K(r)$ for the set of these chains.  Backward mixed-Nash
existence makes it nonempty, and every displayed value lies in
$[-M,M]^I$.

Put

$$
q_i=r_i(\{i\}),\qquad q_i^+=\max\{0,q_i\}.
\tag{11}
$$

The exact dynamic debt of a chain is defined backward by

$$
D_i^K=q_i^+
\tag{12}
$$

and

$$
D_i^t=
\max\left\{
Q_i(x_{-i}^t;v^{t+1}),
C_i(x_{-i}^t;v^{t+1})+c_i(x^t)D_i^{t+1}
\right\}-v_i^t
\qquad(t<K).
\tag{13}
$$

This is the exact optimal-stopping debt against the displayed opponents.
Indeed, if $B_i^t$ is the supremal terminal payoff obtainable by player $i$
from the live history at date $t$, then

$$
B_i^t=v_i^t+D_i^t.
\tag{14}
$$

No optimizer need attain the supremum.  Formula (13) remains valid because
arbitrarily near-optimal tail deviations suffice.

The exact root inequalities imply

$$
0\le D_i^t\le c_i(x^t)D_i^{t+1}\le D_i^{t+1}.
\tag{15}
$$

Define the sum optimum

$$
S_K(r)=
\min_{\mathcal C\in\mathcal N_K(r)}
\sum_{i\in I}D_i^0(\mathcal C).
\tag{16}
$$

As preliminary obligations, prove or carefully rederive the following
facts rather than treating them as compactness folklore:

1. $\mathcal N_K(r)$ is compact and the minimum in (16) is attained.
2. $S_{K+1}(r)\le S_K(r)$.
3. If $\inf_KS_K(r)=0$, the all-Continue extensions of suitable chains are
   terminal approximate equilibria of arbitrarily small error.
4. Since the debts are nonnegative, minimizing their maximum and minimizing
   their sum have the same zero-versus-positive limiting dichotomy:
   if
   $$
   E_K=\min_{\mathcal C\in\mathcal N_K(r)}\max_iD_i^0(\mathcal C),
   $$
   then
   $$
   E_K\le S_K\le nE_K.
   \tag{17}
   $$

The branch studied below is

$$
s_\infty:=\lim_{K\to\infty}S_K(r)>0.
\tag{18}
$$

This branch is impossible when $n=1$: Never is exact if $q_1\le0$, while a
sure-Quit cutoff-one root has zero initial debt if $q_1>0$.  Hence the
decisive part may assume $n\ge2$.

## 3. Calibrated projective provenance

Choose integers $K_m\to\infty$ and exact sum-minimizers
$\mathcal C_m\in\mathcal N_{K_m}(r)$.  By finite pigeonhole and compact
diagonal extraction, pass to a common subsequence and choose a fixed player
$i_*$ such that

$$
D_{m,i_*}^0\ge \frac{S_{K_m}}n\ge \frac{s_\infty}n=:d_0>0
\tag{19}
$$

and, for every fixed $t$,

$$
(x_m^t,v_m^t,D_m^t)\longrightarrow(x^t,v^t,D^t).
\tag{20}
$$

The limiting forward path satisfies the exact root, value, and debt
recursions at every finite date.  In particular,

$$
D_{i_*}^t\ge d_0,
\qquad
D_{i_*}^t\le c_{i_*}(x^t)D_{i_*}^{t+1}.
\tag{21}
$$

It follows that $q_{i_*}>0$ and that the opponent-only clock of $i_*$ is
summable:

$$
H_{-i_*}:=
\sum_{t=0}^{\infty}-\log c_{i_*}(x^t)<\infty.
\tag{22}
$$

This conclusion is rooted at the same date as the positive debt.  A zero
factor at an earlier, discarded date may not be used to infer anything about
a later suffix.

There are now two own-clock branches.  If

$$
\sum_t-\log(1-x_{i_*}^t)=\infty,
\tag{23}
$$

then every other player's opponent clock diverges because it includes
$i_*$.  Prove directly from the infinite Bellman inequalities that the
displayed product profile absorbs almost surely and is an exact terminal
Nash equilibrium.  This is the easy positive branch.

The decisive branch of this question is therefore

$$
\boxed{
\sum_{t=0}^{\infty}\sum_{j\in I}-\log(1-x_j^t)<\infty.
}
\tag{FS}
$$

Under (FS), the displayed infinite product profile has positive Never
probability.  Prove that $v^t$ converges to some $L\in[-M,M]^I$ and that,
from every date $s$,

$$
v^s=U^s+\alpha_sL,
\qquad
\alpha_s=\prod_{t=s}^{\infty}a(x^t)>0,
\tag{24}
$$

where $U^s$ is the actual terminal payoff of the displayed infinite profile
with value $0$ on Never.  The vector $L$ is a relative boundary term.  It is
not, merely by (24), an attainable or credible continuation payoff.

### 3.1 A nonvanishing marked atom at the moving boundary

Let

$$
C_A=|A|=2^n.
$$

For each $m$, inspect the last live root $x_m^{K_m-1}$ with player $i_*$
forced to Continue.  For
$T\subseteq I\setminus\{i_*\}$, let

$$
p_{m,-i_*}(T)=
\prod_{j\in T}x_{m,j}^{K_m-1}
\prod_{j\notin T\cup\{i_*\}}(1-x_{m,j}^{K_m-1}),
\tag{25}
$$

and put

$$
\Delta_{i_*}(T)=
r_{i_*}(T)-r_{i_*}(T\cup\{i_*\}).
\tag{26}
$$

Define root-to-last opponent survival

$$
\Pi_m=
\prod_{t=0}^{K_m-2}c_{i_*}(x_m^t).
\tag{27}
$$

Prove the following linear, not quadratic, terminal-packet estimate.  After
another common subsequence, one nonempty set
$T_*\subseteq I\setminus\{i_*\}$ is fixed and

$$
\Delta_{i_*}(T_*)>0,
\tag{28}
$$

$$
D_{m,i_*}^0
\le C_A\Pi_mp_{m,-i_*}(T_*)\Delta_{i_*}(T_*)
\le2MC_A\Pi_mp_{m,-i_*}(T_*),
\tag{29}
$$

so in particular

$$
\boxed{
\Pi_mp_{m,-i_*}(T_*)
\ge\frac{d_0}{2MC_A}>0.
}
\tag{30}
$$

This is an actual product-action cylinder, with the full simultaneous set
$T_*$ retained.  No member of $T_*$ is thereby promoted to a new debt owner.

### 3.2 Required two-ended compactification

The marked cylinder in (30) moves to chronological time $K_m-1$.  It may
vanish from every fixed forward window without losing any transported mass.
Any compactness argument used below must therefore take one common
subsequence carrying all of the following data:

1. the forward limits in (20);
2. for every fixed reverse depth $d\ge0$, the limits of
   $$
   \check x_m^d=x_m^{K_m-1-d},\quad
   \check v_m^d=v_m^{K_m-1-d},\quad
   \check D_m^d=D_m^{K_m-1-d};
   \tag{31}
   $$
3. the fixed owner $i_*$, fixed set $T_*$, and marked weight
   $$
   \omega_m=\Pi_mp_{m,-i_*}(T_*)
   \longrightarrow\omega\ge\frac{d_0}{2MC_A};
   \tag{32}
   $$
4. for every fixed pair of forward and reverse depths $(r,s)$, the bridge
   survival products
   $$
   Z_m^{r,s}=
   \prod_{t=r}^{K_m-1-s}c_{i_*}(x_m^t),\qquad
   Y_m^{r,s}=
   \prod_{t=r}^{K_m-1-s}a(x_m^t),
   \tag{33}
   $$
   whenever the index interval is nonempty, together with their exact
   factorization identities against the retained forward and reverse
   pieces.

The reverse windows form an exact zero-boundary tail, while the forward
windows form the positive-debt projective path.  Equations (32)--(33) are
the coupling between them.  Independently extracting a forward path, a
reverse path, and a normalized mark, without their common raw scale and
bridge products, does not meet this requirement.

## 4. Explicit finite table certificates

Before attempting a compactified boundary construction, remove the following
exactly checkable positive branches.  They are genuine producers, not merely
necessary local conditions.

### 4.1 Cutoff-one safety

Let $x$ be an exact Nash root at continuation $0$ and put

$$
V_i(x)=g_i(x;0).
\tag{34}
$$

Let $C_i^+(x)$ be player $i$'s pure-Continue endpoint when the
all-Continue outcome after this root pays $q_i^+$:

$$
C_i^+(x)=
\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
p_{-i}^x(T)r_i(T)
+c_i(x)q_i^+.
\tag{35}
$$

Here $p_{-i}^x$ is the opponents' product law.  Prove the exact cutoff-one
identity

$$
D_i(x)=
\max\{Q_i(x_{-i};0),C_i^+(x)\}-V_i(x),
\tag{36}
$$

and hence, using exact root Nash,

$$
\boxed{
D_i(x)=0
\quad\Longleftrightarrow\quad
C_i^+(x)\le V_i(x).
}
\tag{37}
$$

Consequently, one zero-tail Nash root satisfying (37) for every player is an
exact terminal Nash profile when followed by Never.  Conversely, every
zero-debt cutoff-one certificate has this form.  For rational payoff tables,
this is a compact semialgebraic feasibility problem.

As a useful sufficient class, prove that (37) holds for every zero-tail Nash
root whenever

$$
q_i>0,quad
\varnothing\ne T\subseteq I\setminus\{i\}
\quad\Longrightarrow\quad
r_i(T)\le r_i(T\cup\{i\}).
\tag{38}
$$

Thus a game satisfying (38) has $S_1=0$.  The contrapositive is only a
necessary obstruction: a strict joining loss for some positive-solo player
does not imply nonexistence of equilibrium.

### 4.2 Direct pure First

For a nonempty quitter set $S\subseteq I$, define

$$
\rho(S)=
\max\left\{
0,
\max_{j\in S}\bigl(r_j(S\setminus\{j\})-r_j(S)\bigr),
\max_{j\notin S}\bigl(r_j(S\cup\{j\})-r_j(S)\bigr)
\right\},
\tag{39}
$$

where a maximum over an empty index set is omitted and (2) applies when
$S$ is a singleton.

Prove that

$$
\boxed{\rho(S)=0}
\tag{40}
$$

is necessary and sufficient for the following direct pure certificate:
at the first stage exactly the players in $S$ Quit, and after the unreached
all-Continue outcome everyone prescribes Never.  The resulting profile is an
exact terminal Nash equilibrium.  In the singleton case, the quitter may
delay and then quit alone; this gives the same payoff $q_i$, while Never gives
$0$, so the convention $r_i(\varnothing)=0$ correctly includes both options.

An atom with $\rho(S)>0$ is not a First certificate, even if it has positive
probability in a finite chain.

### 4.3 Exact one-owner stationary repair

Fix a player $k$ and $h\in(0,1]$.  At every live history let only player $k$
Quit with positive probability:

$$
x_k=h,\qquad x_j=0\quad(j\ne k).
\tag{41}
$$

This profile absorbs almost surely at $\{k\}$ and has payoff $r(\{k\})$.
Prove the following necessity-and-sufficiency statement for the entire class
(41):

$$
\boxed{
\begin{aligned}
&\text{the repeated profile (41) is an exact terminal Nash equilibrium}
\\[1mm]
&\quad\Longleftrightarrow\quad
q_k\ge0
\ \text{ and }\
(1-h)q_j+h\,r_j(\{k,j\})\le r_j(\{k\})
\quad(j\ne k).
\end{aligned}
}
\tag{42}
$$

The proof must cover arbitrary behavioral deviations.  For $k$, the only
extreme alternatives are quitting alone and Never.  For $j\ne k$, every
finite quit time is a convex combination of

$$
r_j(\{k\})
\quad\text{and}\quad
(1-h)q_j+h\,r_j(\{k,j\}),
\tag{43}
$$

and Never realizes the first endpoint.  This observation should be proved,
not merely asserted from a one-stage Nash calculation.

The case $h=1$ overlaps a singleton First certificate.  The cases $0<h<1$
are genuine stationary repairs and may exist even when no payoff appearing
on a positive zero-boundary suffix equals $r(\{k\})$.

For a positive-solo owner $k$, failure of (42) at every rate has an exact
finite witness structure.  Define the universal joining obstruction

$$
\forall h\in(0,1]\ \exists j\ne k:\quad
r_j(\{k\})<
(1-h)q_j+h\,r_j(\{k,j\}).
\tag{42a}
$$

Prove that exactly one of the following holds:

1. some $h\in(0,1]$ satisfies (42), and the owner's solo payoff vector is
   certified by an exact stationary profile; or
2. (42a) holds.

Then extract from (42a):

- a **strict sure-joiner** $j$ satisfying
  $$
  r_j(\{k,j\})>r_j(\{k\});
  \tag{42b}
  $$
- a **weak preemptor** $j'$ (possibly a different player) satisfying
  $$
  q_{j'}\ge r_{j'}(\{k\}).
  \tag{42c}
  $$

The second extraction must use finiteness as $h\downarrow0$; one may not
silently assume that the sure-joiner and weak preemptor are the same player.
Neither witness is automatically a new dynamic-debt owner.

#### Two-player closure of the universal-joining branch

When $I=\{k,j\}$, the terminal packet and the universal joining obstruction
do align.  Indeed, the nonempty set $T_*$ in (28) must be $\{j\}$, so the
packet gives the owner's strict joining loss

$$
r_k(\{k,j\})<r_k(\{j\}).
\tag{42d}
$$

If the exact one-owner certificate (42) fails at every rate, the weak
preemptor in (42c) must be the same unique opponent $j$, and therefore

$$
r_j(\{k\})\le q_j.
\tag{42e}
$$

For $p\in(0,1]$, consider the stationary product profile in which $j$ Quits
surely and $k$ Quits with hazard $p$.  Its terminal payoff is

$$
W_k(p)=(1-p)r_k(\{j\})+p\,r_k(\{k,j\}),
\qquad
W_j(p)=(1-p)q_j+p\,r_j(\{k,j\}).
\tag{42f}
$$

Prove against arbitrary behavioral deviations, not only one-stage
deviations, that the exact caps are

$$
\operatorname{Cap}_k(p)=r_k(\{j\}),
\qquad
\operatorname{Cap}_j(p)=
\max\{W_j(p),r_j(\{k\})\}.
\tag{42g}
$$

Consequently,

$$
\operatorname{Reg}_k(p)
=p\bigl(r_k(\{j\})-r_k(\{k,j\})\bigr),
$$

$$
\operatorname{Reg}_j(p)
=\max\{0,r_j(\{k\})-W_j(p)\}
\le p\,|r_j(\{k,j\})-q_j|,
\tag{42h}
$$

and hence

$$
\max_{a\in\{k,j\}}\operatorname{Reg}_a(p)
\le
p\left(
r_k(\{j\})-r_k(\{k,j\})
+|r_j(\{k,j\})-q_j|
\right)\longrightarrow0.
\tag{42i}
$$

Thus the universal-joining branch is resolved for two players: positive
debt yields either the exact owner-solo repair (42), or the
accuracy-indexed pair repair (42f)--(42i), which is an (R1) certificate.
This does not assert that an exact stationary equilibrium exists.

For $n\ge3$, this argument stops for a precise reason.  The marked object is
a simultaneous quitting set $T_*\subseteq I\setminus\{k\}$, not a selected
new owner.  Making every member of $T_*$ Quit surely and letting $k$ use a
small hazard controls $k$'s joining loss, but it can create order-one
deviations by a member of $T_*$ who leaves the quitting set, and by an
outsider who joins it.  Moreover, the weak preemptor supplied by (42c) may
lie outside $T_*$ and need not control either family of deviations.  The
remaining set-repair obligation is therefore to establish internal-leaver
credibility for the whole set $T_*$ together with every outsider-joining
inequality, or to replace $T_*$ by another explicitly certified quitting
set without losing the positive packet's role in the repair-or-descent
argument.

### 4.4 Accuracy-indexed stationary repair

Exact stationary equilibrium is too strong a universal repair target.  For an
arbitrary stationary product action $x$ with $a(x)<1$, its prescribed
terminal payoff is

$$
W_i(x)=
\frac{\sum_{a\in A^*}\xi_x(a)r_i(a)}{1-a(x)}.
\tag{43a}
$$

Its exact stationary best-response cap is also elementary.  Let

$$
J_i(x)=\sum_{T\subseteq I\setminus\{i\}}p_{-i}^x(T)
r_i(T\cup\{i\}).
\tag{43b}
$$

If $c_i(x)<1$, put

$$
N_i(x)=
\frac{
\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
p_{-i}^x(T)r_i(T)
}{1-c_i(x)}.
\tag{43c}
$$

This is the payoff when $i$ uses Never and waits for opponent absorption.
Prove that

$$
\operatorname{Cap}_i(x)=\max\{J_i(x),N_i(x)\}
\qquad(c_i(x)<1).
\tag{43d}
$$

If $c_i(x)=1$, all opponents use Never and

$$
\operatorname{Cap}_i(x)=q_i^+.
\tag{43e}
$$

Therefore

$$
\operatorname{Reg}_i(x)=
\operatorname{Cap}_i(x)-W_i(x)
\tag{43f}
$$

is the exact terminal exploitability against arbitrary behavioral
deviations.  An explicit family $x(\eta)$ with

$$
\max_i\operatorname{Reg}_i(x(\eta))\longrightarrow0
\tag{43g}
$$

is an accepted accuracy-indexed table repair, even if no member of the family
is an exact stationary equilibrium and the limiting stationary profile has a
profitable Never deviation.

### 4.5 Finite cyclic product-jump certificate

The preceding branches are not proposed as exhaustive.  In particular, a
nonstationary product-jump loop is a valid output.

Let $L\ge2$ and suppose there are product actions
$z^0,\ldots,z^{L-1}$ and vectors $w^0,\ldots,w^{L-1}$, cyclically indexed,
such that

$$
z^\ell\text{ is an exact Nash root at }w^{\ell+1},
\qquad
w^\ell=g(z^\ell;w^{\ell+1}),
\tag{44}
$$

and, for every player,

$$
\prod_{\ell=0}^{L-1}c_i(z^\ell)<1.
\tag{45}
$$

Prove that periodic repetition of the block is an exact terminal Nash
equilibrium with continuation values $w^\ell$.  The playerwise products in
(45), rather than joint absorption alone, eliminate every deviator's terminal
Snell remainder.  This certificate is included to prevent a proposed proof
from silently assuming that First, stationarity, or singleton flow is
complete.

### 4.6 Certified continuation cycles

An accuracy-indexed repair cycle need not consist of one-stage exact roots.
Let $k=0,\ldots,L-1$ index finitely many phases cyclically.  Phase $k$ is an
actual positive-length finite product block with five-scalar summary

$$
(A_i^k,T_i^k,\chi_i^k,B_i^k,P^k)
\qquad(i\in I)
\tag{45a}
$$

as defined in Section 5.  Let $(w^k,\beta^k)$ be proposed phase-entry
payoff/cap pairs with $\beta_i^k\ge0$.  They must be realized by the cyclic
profile, or proved as valid upper bounds on its exact relative caps; free
slack variables do not count.  The exact compatibility and credibility
inequalities are

$$
w_i^k=B_i^k+P^k w_i^{k+1},
\tag{45b}
$$

$$
\max\left\{
A_i^k,
T_i^k+\chi_i^k(w_i^{k+1}+\beta_i^{k+1})
\right\}
\le w_i^k+\beta_i^k,
\tag{45c}
$$

with cyclic indices.  Prove the corresponding finite-block compiler.  In
particular:

- if $\max_{i,k}\beta_i^k\le\varepsilon$ and every player's opponent-only
  survival contracts around the cycle, periodic repetition is a terminal
  $\varepsilon$-equilibrium;
- if an opponent clock does not contract, the cycle must include an explicit
  Never, First, or stationary exceptional-owner closure rather than discard
  the terminal Snell remainder;
- a cycle claimed to arise from the positive-debt boundary must retain the
  full set $T_*$ and nonvanishing scale $\omega$ from (28)--(32), or prove a
  different explicit progress/anchor condition linking it to the supplied
  chains.

A cycle of owner names, incentive signs, or separately normalized packets is
not a certified continuation cycle.  Equations (45b)--(45c), chronological
block concatenation, common product realization, and playerwise terminal
closure are all mandatory.

## 5. Every finite prefix has a five-scalar acceptance calculus

Fix a positive length $\ell\ge1$ and a finite product prefix

$$
p=(x^0,\ldots,x^{\ell-1}).
$$

In the decisive application, $p$ must be the first $\ell$ roots of one of
the selected minimizing chains $\mathcal C_m$.  The formulas below do not
require the payoff of the attached tail to equal the displayed value
$v_m^\ell$.

For player $i$, define the opponents' product law at date $t$ by

$$
p_{-i}^t(T)=
\prod_{j\in T}x_j^t
\prod_{j\notin T\cup\{i\}}(1-x_j^t),
\qquad T\subseteq I\setminus\{i\}.
\tag{46}
$$

Let

$$
\Gamma_{i,0}=1,qquad
\Gamma_{i,t}=\prod_{u=0}^{t-1}c_i(x^u),qquad
\chi_i=\Gamma_{i,\ell},
\tag{47}
$$

and

$$
H_i^t=
\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
p_{-i}^t(T)r_i(T),
\tag{48}
$$

$$
J_i^t=
\sum_{T\subseteq I\setminus\{i\}}
p_{-i}^t(T)r_i(T\cup\{i\}).
\tag{49}
$$

Thus $H_i^t$ is the current opponent-absorption reward when $i$ Continues,
and $J_i^t$ is its current pure-Quit payoff.  Put

$$
T_i(p)=\sum_{t=0}^{\ell-1}\Gamma_{i,t}H_i^t,
\tag{50}
$$

$$
A_{i,t}(p)=
\sum_{u=0}^{t-1}\Gamma_{i,u}H_i^u
+\Gamma_{i,t}J_i^t,
\qquad
A_i(p)=\max_{0\le t<\ell}A_{i,t}(p).
\tag{51}
$$

The scalar $A_i$ is the best payoff from a deterministic Quit time strictly
before the tail, while $T_i+\chi_i z$ is the payoff from Continuing through
the prefix and then receiving value $z$.

For prescribed play, set

$$
S_0=1,qquad
S_t=\prod_{u=0}^{t-1}a(x^u),qquad
P=S_\ell,
\tag{52}
$$

and

$$
B_i(p)=
\sum_{t=0}^{\ell-1}S_t
\sum_{a\in A^*}\xi_{x^t}(a)r_i(a).
\tag{53}
$$

The five scalars for player $i$ are

$$
(A_i,T_i,\chi_i,B_i,P),
\tag{54}
$$

where $P$ is common to all players and $0\le P\le\chi_i\le1$.

### 5.1 Attainable tail certificates

An **attainable tail certificate** is a pair $(w,\beta)\in\mathbb R^I
\times\mathbb R_+^I$ for which there is an actual behavior profile $\tau$
such that

$$
w_i=U_i(\tau),
\qquad
w_i+\beta_i=\sup_{\tau_i'}U_i(\tau_i',\tau_{-i})
\quad(i\in I).
\tag{55}
$$

Let $\mathscr A(r)$ be the set of all such pairs.  The supremum in (55) need
not be attained.  A claimed certificate must give the behavior profile and
prove both equalities; a payoff vector alone is not an attainable
certificate.

Splice $\tau$ after prefix $p$.  Prove the exact formulas

$$
U_i(p\star\tau)=B_i+Pw_i,
\tag{56}
$$

$$
\sup_{\sigma_i}U_i(\sigma_i,(p\star\tau)_{-i})
=\max\{A_i,T_i+\chi_i(w_i+\beta_i)\}.
\tag{57}
$$

The reduction in (57) is over arbitrary behavioral deviations.  It follows
because the live public history is unique: before reaching the tail, every
deviation is a randomization over deterministic Quit dates and the option of
reaching the tail.  Near-optimal tail deviations establish equality even if
the supremum in (55) is not attained.

Thus the exact initial exploitability is

$$
R_i^p(w_i,\beta_i)=
\max\{A_i,T_i+\chi_i(w_i+\beta_i)\}-(B_i+Pw_i).
\tag{58}
$$

For $\varepsilon\ge0$, define the **prefix acceptance polyhedron**

$$
\mathscr P_\varepsilon(p)=
\left\{(w,\beta):
\begin{array}{l}
A_i-B_i-Pw_i\le\varepsilon,\\
T_i-B_i+(\chi_i-P)w_i+\chi_i\beta_i\le\varepsilon
\quad(i\in I)
\end{array}
\right\}.
\tag{59}
$$

Prove the exact equivalence

$$
(w,\beta)\in\mathscr P_\varepsilon(p)
\quad\Longleftrightarrow\quad
R_i^p(w_i,\beta_i)\le\varepsilon
\quad(i\in I).
\tag{60}
$$

In the strict scalar case $0<P<\chi_i$, the acceptable values of $w_i$ for
fixed $\beta_i$ form the interval

$$
\frac{A_i-B_i-\varepsilon}{P}
\le w_i\le
\frac{B_i+\varepsilon-T_i-\chi_i\beta_i}{\chi_i-P}.
\tag{61}
$$

The two endpoints must be ordered.  The unique minimizer of
$R_i^p(\,cdot\,,\beta_i)$ is the balance point

$$
w_i^*=\frac{A_i-T_i-\chi_i\beta_i}{\chi_i}.
\tag{62}
$$

State the correct half-line or flat alternatives when $P=0$, $P=\chi_i$, or
$\chi_i=0$; do not divide by a vanishing survival factor.

### 5.2 Prefix composition

If two consecutive prefix summaries are

$$
(A_1,T_1,\chi_1,B_1,P_1),qquad
(A_2,T_2,\chi_2,B_2,P_2),
$$

prove that their concatenation has summary

$$
\begin{aligned}
A'&=\max\{A_1,T_1+\chi_1A_2\},\\
T'&=T_1+\chi_1T_2,\\
\chi'&=\chi_1\chi_2,\\
B'&=B_1+P_1B_2,\\
P'&=P_1P_2.
\end{aligned}
\tag{63}
$$

Thus arbitrary positive-length finite prefixes form a fixed five-scalar
max-affine composition semigroup.  With all five scalars real this is not
literally a monoid: a global identity would require the extended floor
\(A=-\infty\), or a restricted terminal domain.
The boundary producer is an intersection problem between the generally
nonconvex attainable set $\mathscr A(r)$ and explicit polyhedra
$\mathscr P_\varepsilon(p)$.

No finite-dimensional separation theorem may be applied until the relevant
closure of $\mathscr A(r)$ has been proved.  Weak limits of behavior profiles
can lose terminal payoff, Never mass, product realization, or unilateral
caps.

## 6. Standard-proper sequentially perfect absorption paths

The boundary-intersection route may fail for the particular minimizing
prefixes even though the table has a nonstationary equilibrium construction.
The exhaustive structural fallback in this question is therefore an actual
standard-proper absorption path, not a finite-period or stationary ansatz.

An absorption path is a cadlag map

$$
\pi:[0,1]\longrightarrow[0,1]^{A^*}
$$

whose coordinates are nondecreasing.  Put

$$
\pi_{0-}=0,
\qquad
\widehat\pi_t=\sum_{a\in A^*}\pi_t(a),
\qquad
\Delta\pi_t=\pi_t-\pi_{t-},
\tag{64}
$$

$$
S(\pi)=\{t:\Delta\pi_t\ne0\},
\qquad
T(\pi)=\{t:\widehat\pi_t=t\}.
\tag{65}
$$

For $t<1$, let $\dot\pi_t(a)\in[0,+\infty]$ be the coordinatewise lower
right Dini derivative

$$
\dot\pi_t(a)=
\liminf_{s\downarrow t}
\frac{\pi_s(a)-\pi_t(a)}{s-t}.
\tag{66}
$$

Require the following standard path axioms.

1. For every $t$,
   $$
   t\le\widehat\pi_t\le1,
   \qquad \widehat\pi_1=1.
   \tag{67}
   $$
2. On every connected component $(u,v)$ of
   $$
   [0,1]\setminus\bigl(S(\pi)\cup T(\pi)\bigr),
   $$
   the function $\widehat\pi$ is constant and equal to $v$.  Removing the
   jump set before taking components is essential.
3. At each jump $t\in S(\pi)$, there is a product action $x(t)$ such that
   $$
   \frac{\Delta\pi_t(a)}{1-t}=\xi_{x(t)}(a)
   \qquad(a\in A^*).
   \tag{68}
   $$
4. At every $t\in T(\pi)\setminus\{1\}$, continuous flow is supported on
   singleton quitter sets:
   $$
   \dot\pi_t(a)=0
   \quad\text{when }|S(a)|\ge2.
   \tag{69}
   $$

The path is **proper** if

$$
\widehat\pi_t<1
\qquad(t\in S(\pi)).
\tag{70}
$$

For $t<1$, its residual payoff is

$$
\gamma_t(\pi)=
\begin{cases}
\displaystyle
\frac{
\sum_{a\in A^*}(\pi_1(a)-\pi_t(a))r(a)
}{1-\widehat\pi_t},
&\widehat\pi_t<1,\\[3mm]
0,&\widehat\pi_t=1.
\end{cases}
\tag{71}
$$

A proper path is **sequentially perfect** if:

1. for every jump $t$, $x(t)$ is an exact Nash root at
   $\gamma_t(\pi)$;
2. for every $t\in T(\pi)\setminus\{1\}$ and every player $i$,
   $$
   \gamma_{t,i}(\pi)\ge q_i;
   \tag{72}
   $$
3. equality holds in (72) whenever
   $$
   \dot\pi_t(Q_i,C_{-i})>0.
   \tag{73}
   $$

The positivity test in (73) includes an infinite Dini derivative.  A proof
may impose absolute continuity or finite rates only if it derives an
approximation theorem covering the omitted extended-Dini paths.

### 6.1 Strategic bridge required of a path output

A path is not accepted merely because it satisfies local indifference
equations.  Prove the following path-to-profile statement as part of any
solution that uses this branch:

> From a standard-proper sequentially perfect absorption path, construct
> terminal $\varepsilon$-equilibria for every $\varepsilon>0$.

The discretization must use strong one-stage perfection.  Namely, for every
pure action $b_i$,

$$
g_i((b_i,x_{-i});y)\le g_i(x;y)+\eta,
\tag{74}
$$

and every pure action used with positive probability must also satisfy

$$
g_i((b_i,x_{-i});y)\ge g_i(x;y)-\eta.
\tag{75}
$$

Most importantly, local sequential perfection does not by itself defeat a
deviation to Never when a selected singleton payoff is negative.  The proof
must establish the corrected global alternative: either the discretized
absorbing profiles have vanishing global terminal regret, or their failure
produces stationary approximate equilibria with vanishing regret.  A bound
only on one-stage deviations is incomplete.

Conversely, if a negative answer claims that no standard-proper path exists,
it must exclude jumps, continuous singleton flow, accumulating jumps, and
their corrected plateau geometry.  Excluding stationary profiles or finite
periods is not enough.

### 6.2 Exhaustive structural role

For clarity, distinguish the direct pure certificate (40) from the general
First branch.  Say that **First** holds if there are terminal
$\varepsilon_m$-equilibria with $\varepsilon_m\downarrow0$ which absorb with
probability one at the first stage; the continuation prescribed after a
unilateral attempt to prevent first-stage absorption is part of each
certificate.  Say that **Never** holds if all-Continue is a terminal exact
equilibrium, equivalently $q_i\le0$ for every player.

The corrected structural bridge relevant to this question is

$$
\begin{aligned}
&\text{terminal $\varepsilon$-equilibria exist for every $\varepsilon>0$}
\\
&\quad\Longleftrightarrow\quad
\text{Never}\ \lor\ \text{First}\ \lor\
\text{a standard-proper sequentially perfect absorption path exists}.
\end{aligned}
\tag{75a}
$$

A solution may reprove (75a) as part of its argument or isolate its use as a
separate lemma, but it may not use an uncorrected plateau axiom or omit the
stationary fallback in the path-to-profile direction.  The positive plateau
rules out Never.  A fully certified general First family is therefore also
an admissible explicit output, even when it is not of the direct pure form
(40).

## 7. Decisive boundary-closure question

Assume the positive plateau (18), choose calibrated exact sum-minimizers as
in (19)--(20), and assume the fully summable branch (FS).  Is the following
statement true?

$$
\boxed{
\begin{array}{l}
\text{For every }\varepsilon>0,\text{ at least one of the outputs}\
\text{(R1)--(R3) below can be produced.}
\end{array}
}
\tag{PPBC}
$$

### (R1) Explicit table repair

Produce one of the following and prove its all-behavior terminal cap:

- a cutoff-one safe root satisfying (37);
- a direct pure First set satisfying (40);
- a general accuracy-indexed First family in the sense of Section 6.2, with
  its off-path continuation and caps explicitly certified;
- an exact one-owner stationary repair satisfying (42);
- an accuracy-indexed stationary family satisfying (43g);
- an exact product-jump loop satisfying (44)--(45); or
- an accuracy-indexed certified continuation cycle satisfying
  (45a)--(45c), including its playerwise terminal closure.

The first item is incompatible with a genuinely positive plateau, but is
retained as a calibration and as a possible output after correcting a false
plateau calculation.  The list is not claimed to exhaust all finite
architectures; a different explicit finite table certificate is admissible
only if it is specified by finitely many product blocks and explicit table or
max-affine inequalities, and its actual payoff and exact arbitrary-behavior
caps are derived in the answer.  An unnamed behavior profile already assumed
to have debt at most $\varepsilon$ is not an (R1) certificate.

### (R2) Nonzero-prefix boundary intersection

There exist an index $m$, a prefix length

$$
1\le\ell\le K_m,
\tag{76}
$$

and an actual tail profile $\tau$ with attainable certificate
$(w,\beta)\in\mathscr A(r)$ such that, for the prefix

$$
p_{m,\ell}=(x_m^0,\ldots,x_m^{\ell-1}),
\tag{77}
$$

one has

$$
(w,\beta)\in\mathscr P_\varepsilon(p_{m,\ell}).
\tag{78}
$$

Equations (56)--(60) then make $p_{m,\ell}\star\tau$ a terminal
$\varepsilon$-equilibrium.  Exact matching with the displayed suffix value
$v_m^\ell$ is not required.  The acceptance inequalities, rather than
chain-value equality, are the interface.

The prefix in (77) must come from the supplied minimizing chain and must have
positive length.  Taking an arbitrary all-Continue stage in front of an
already known equilibrium, or taking $\ell=0$, does not answer (R2).

### (R3) Genuine standard-proper path

Construct the full path $\pi$ of Section 6 and verify every path,
product-jump, continuous-flow, properness, and sequential-perfection axiom.
Then prove the strategic bridge in Section 6.1.  It is not enough to invoke
the abstract existence of a terminal approximate equilibrium.

This output is deliberately broader than periodicity.  It permits continuous
singleton flow, unbounded periods, accumulating jumps, and the stationary
fallback forced by a negative-solo Never deviation.

### 7.1 The finite repair-or-debt-descent lemma

The preferred route to (PPBC) is the following uniform finite fork.  State
and prove it with all dependencies explicit.

For every fixed $\varepsilon>0$, there exist

$$
L=L(r,d_0,\varepsilon)\in\mathbb N_{>0},
\qquad
c=c(r,d_0,\varepsilon)>0,
\qquad
m_0\in\mathbb N,
\tag{79}
$$

such that at least one of the following holds:

1. an output of type (R1), (R2), or (R3) is produced at accuracy
   $\varepsilon$; or
2. for every $m\ge m_0$, one can construct an exact zero-boundary chain
   $$
   \mathcal C_m'\in\mathcal N_{K_m+L}(r)
   \tag{80}
   $$
   satisfying the strict total-debt improvement
   $$
   \sum_{j\in I}D_j^0(\mathcal C_m')
   \le S_{K_m}(r)-c.
   \tag{81}
   $$

The constants $L$ and $c$ may depend on the table, the plateau lower bound,
and the requested accuracy, but not on $m$.  The construction in (80) must
specify the new Nash roots and preserve the zero boundary; it may not replace
an exact chain by a favorable continuation value without solving the
corresponding one-stage games.

Alternative 2 contradicts minimality and convergence, because

$$
S_{K_m+L}(r)
\le\sum_jD_j^0(\mathcal C_m')
\le S_{K_m}(r)-c,
\tag{82}
$$

while both outer terms tend to $s_\infty$.  Thus the finite fork implies
(PPBC).

If a fixed positive decrement $c$ is false because the relevant
compactification is not closed, give an explicit counterexample to this
quantified lemma and replace it by a precise scale-sensitive statement that
still either produces (R1)--(R3) or contradicts the plateau.  Merely saying
that the marks chatter or escape is not a corrected theorem.

### 7.2 Boundary intersection or robust separation

For a prefix $p$, define

$$
\mathcal R(p,\tau)=
\max_{i\in I}R_i^p
\bigl(U_i(\tau),\beta_i(\tau)\bigr).
\tag{83}
$$

Failure of (R2) at accuracy $\varepsilon$ is the concrete separation

$$
\inf_{m}\ \min_{1\le\ell\le K_m}\
\inf_{\tau}\mathcal R(p_{m,\ell},\tau)>\varepsilon
\tag{84}
$$

or the corresponding non-strict statement with every candidate exceeding
$\varepsilon$.  Determine the correct closure convention and whether the
infimum is attained.

The substantive task is to turn this separation into either the finite debt
descent (81), an explicit table repair, or a genuine all-profile obstruction.
A hyperplane separating a relaxed convex hull is insufficient unless it is
shown to survive product realization, chronological coupling, Never mass,
and arbitrary unilateral behavior.

A **global negative certificate** must prove a number
$\varepsilon_0>0$ such that

$$
\inf_{\sigma}max_i\beta_i(\sigma)\ge\varepsilon_0,
\tag{85}
$$

where $\sigma$ ranges over every behavior profile.  A positive lower bound
only for the prefixes in (77), stationary profiles, bounded periods, or one
chosen compactification refutes only that architecture.

## 8. Mandatory regressions

Every proposed proof, compactification, or counterexample must calculate the
following examples in its own notation.

### 8.1 Positive plateau with an off-chain stationary repair

Consider the two-player table

$$
r(\{1\})=(1,0),\qquad
r(\{2\})=(3,-1),\qquad
r(\{1,2\})=(2,1).
\tag{86}
$$

Verify all of the following.

1. At continuation $0$, the unique exact Nash root is
   $x=(1/2,1/2)$ and its value is
   $$
   L=(3/2,0).
   $$
2. At continuation $L$, the unique exact Nash root is all-Continue and its
   value remains $L$.
3. Hence every positive-length zero-boundary chain is forced: all roots are
   all-Continue except the last root $(1/2,1/2)$, every live value is $L$,
   and
   $$
   D^0=(1/2,0),\qquad S_K=1/2\quad(K\ge1).
   \tag{87}
   $$
4. Nevertheless, for every $0<h\le1/2$, the one-owner profile
   $$
   x=(h,0)
   \tag{88}
   $$
   is an exact terminal Nash equilibrium with payoff $(1,0)$, because
   player $2$'s Quit endpoint is $2h-1\le0$.

The payoff $(1,0)$ is neither $0$ nor $L$.  Therefore a producer restricted
to values occurring on zero-boundary suffixes is false.  The first
all-Continue root of a minimizing chain can, however, accept the attainable
tail $(w,\beta)=((1,0),0)$ through (59).  This is the basic regression for
the nonzero-prefix acceptance formulation.

### 8.2 A projective boundary value can be separated from every equilibrium payoff

Consider

$$
r(\{1\})=(1,0),\qquad
r(\{2\})=(3,-1),\qquad
r(\{1,2\})=(2,0).
\tag{89}
$$

Finite zero-boundary chains can have arbitrarily long all-Continue prefixes
with projective boundary term

$$
L=(3/2,0).
\tag{90}
$$

Prove that no terminal $\varepsilon$-equilibrium has a payoff within
$\varepsilon$ of $L$ when $\varepsilon<1/8$.  The proof must retain Never
mass.  If

$$
a,b,c,z
$$

are respectively the probabilities of terminal sets $\{1\}$, $\{2\}$,
$\{1,2\}$, and Never, then $a+b+c+z=1$ and

$$
u_1=a+3b+2c=(a+b+c)+2b+c,
\qquad
u_2=-b.
\tag{91}
$$

Player $2$'s Never deviation gives $b\le\varepsilon$.  A deviation by
player $1$ which removes its early Quit actions, waits for player $2$, and
otherwise Quits alone at a late deterministic date gives $c\le\varepsilon$.
Deduce

$$
u_1\le1+3\varepsilon,
\tag{92}
$$

and hence $|u_1-3/2|\le\varepsilon$ implies
$\varepsilon\ge1/8$.

The game is not a counterexample: $\{1\}$ is a direct pure First certificate,
and every one-owner rate $h\in(0,1]$ also satisfies (42).  The lesson is that
$L$ itself must not be inserted as a tail merely because it is a barycenter
or projective limit.

### 8.3 A relative joiner need not inherit debt

For $\eta>0$, consider

$$
r(\{1\})=(1,0),\qquad
r(\{2\})=(1,-\eta),\qquad
r(\{1,2\})=(0,\eta).
\tag{93}
$$

At continuation $0$, verify that $x=(1/2,1/2)$ is an exact Nash root with
value $(1/2,0)$ and one-step exact debt

$$
D=(1/2,0).
\tag{94}
$$

The terminal solo set $\{1\}$ has the inactive-joiner defect

$$
r_2(\{1,2\})-r_2(\{1\})=\eta>0,
\tag{95}
$$

but player $2$ has zero debt.  Simultaneous-action cancellation in player
$2$'s own Bellman equation is exact.  No proof may transfer ownership from
(95).

Again the game closes by the one-owner repair $x=(h,0)$ for
$0<h\le1/2$.  This repair must be found by solving (42), not by inventing a
positive-debt coordinate for player $2$.

### 8.4 Summable-clock terminal-fence escape

Consider the symmetric table

$$
r(\{1\})=(1,2),\qquad
r(\{2\})=(2,1),\qquad
r(\{1,2\})=(-1,-1).
\tag{96}
$$

For $K\ge1$, define

$$
p_t^{(K)}=
\frac1{6(3/2)^{K-1-t}-2},
\qquad 0\le t<K,
\tag{97}
$$

$$
x^t=(p_t^{(K)},p_t^{(K)}),
\qquad
v_i^t=1-2p_t^{(K)},
\qquad
v^K=0.
\tag{98}
$$

Verify that these are exact zero-boundary Nash--Bellman chains and that

$$
D_i^t=
\prod_{s=t}^{K-1}(1-p_s^{(K)})
=
\frac{3(3/2)^{K-1-t}}{6(3/2)^{K-1-t}-2}
>\frac12.
\tag{99}
$$

For each fixed $t$,

$$
p_t^{(K)}\to0,
\qquad v_i^t\to1,
\tag{100}
$$

so the forward projective profile is all-Continue with displayed value
$(1,1)$ and actual payoff $0$.  The total hazard is summable and fixed-time
raw marks vanish.  Nevertheless, the terminal packet moves to time $K-1$
and retains positive transported scale, exactly as (30) requires.

The table has the direct pure First certificate $S=\{1\}$ and also a
one-owner stationary repair.  Thus strict temporal owner repeats and
vanishing fixed-time marks do not establish nonexistence; the correct proof
must couple the moving terminal boundary or use the explicit fallback.

### 8.5 No exact stationary equilibrium, but stationary errors tend to zero

Consider

$$
r(\{1\})=(1,-1),\qquad
r(\{2\})=(-1,-1),\qquad
r(\{1,2\})=(-2,0).
\tag{101}
$$

Prove that this game has no exact stationary terminal Nash equilibrium.  It
also has no one-owner repair for the only positive-solo owner $1$: for every
$h>0$,

$$
(1-h)q_2+h\,r_2(\{1,2\})=-1+h>-1=r_2(\{1\}).
\tag{102}
$$

However, for $a\in(0,1]$, take stationary hazards

$$
x(a)=(a,2/3).
\tag{103}
$$

Using (43a)--(43f), verify

$$
W_1(x(a))=-1,
\qquad
W_2(x(a))=\frac{a-2}{a+2},
\tag{104}
$$

and

$$
\operatorname{Reg}_1(x(a))=0,
\qquad
\operatorname{Reg}_2(x(a))=\frac{a^2}{a+2}.
\tag{105}
$$

Thus stationary terminal exploitability tends to zero as $a\downarrow0$,
although the limiting profile $x=(0,2/3)$ has a profitable Never deviation.
Any proposed repair theorem requiring an exact stationary repair, a closed
stationary-equilibrium set, or uniform opponent contraction at the limit is
false.  Accuracy-indexed repair is essential.

### 8.6 Generic product-jump regression

Suppose a table has no cutoff-one safe root, direct pure First set, or
one-owner stationary repair, but data satisfying (44)--(45) exist with a
nonconstant support word.  The periodic compiler must accept this as an exact
positive resolution.  No negative argument based only on failure of the
three simple table tests is valid.

Conversely, failure to find a loop below some period, in one support atlas,
or under strict contraction margins does not refute (PPBC).  The valid
fallback class includes accuracy-indexed cycles of unbounded period and the
standard-proper paths of Section 6.

### 8.7 Three-player sure-set scope regression

Let player $0$ be the positive-debt owner and consider the table

$$
\begin{array}{c|c}
S&r(S)\\ \hline
\{0\}&(1,0,0)\\
\{1\}&(0,0,0)\\
\{2\}&(0,1,0)\\
\{0,1\}&(1,1,0)\\
\{0,2\}&(1,0,0)\\
\{1,2\}&(4,0,0)\\
\{0,1,2\}&(1,0,0).
\end{array}
\tag{R7.1}
$$

At the zero-tail root where all three players Quit with probability $1/2$,
verify that every player is indifferent between Quit and Continue, the root
value is

$$
v=(1,1/4,0),
\tag{R7.2}
$$

and the exact cutoff-one debt is

$$
D=(1/4,0,0).
\tag{R7.3}
$$

With player $0$ forced to Continue, the four opponent atoms
$\varnothing,\{1\},\{2\},\{1,2\}$ have owner advantages

$$
0,-1,-1,3,
\tag{R7.4}
$$

so the full-set atom $T_*=\{1,2\}$ carries the positive packet.  Moreover,
every positive owner-solo rate $p$ is obstructed by player $1$, since

$$
r_1(\{0\})=0< p
=(1-p)q_1+p,r_1(\{0,1\}).
\tag{R7.5}
$$

Nevertheless the packet and universal obstruction do not force a
vanishing-owner/sure-opponent-set repair.  For $T=\{1\}$ and $T=\{2\}$,
the owner's necessary zero-hazard joining-loss inequality fails:

$$
r_0(T\cup\{0\})=1>0=r_0(T).
\tag{R7.6}
$$

For $T=\{1,2\}$, the owner inequality holds, but player $1$ has the strict
internal-leaver deviation

$$
r_1(\{2\})=1>0=r_1(\{1,2\}).
\tag{R7.7}
$$

This conclusion is deliberately local to the $p\downarrow0$ repair rung.
The table has the exact direct First certificate $S=\{0,1\}$, with payoff
$(1,1,0)$: each quitter loses by leaving the set, while player $2$ is
indifferent to joining it.  Equivalently, it is the endpoint $p=1$ of the
$T=\{1\}$ owner-hazard family.  Thus (R7.1) is not a counterexample to all
static $(p,T)$ repairs, to (PPBC), or to equilibrium existence.  It is a
regression against promoting the marked set or the weak preemptor into a
small-hazard repair without checking every internal leaver and outsider.

## 9. Anti-tautology and soundness audit

A claimed solution must pass every item below.

1. **No length-zero repair.**  In (R2), $\ell\ge1$ and the prefix is an
   initial segment of a calibrated minimizing chain.  Prefixing an already
   known equilibrium by an arbitrary all-Continue stage is not admissible.
2. **No bare supplied tail.**  An attainable tail includes the actual
   behavior profile, its terminal payoff, and the exact supremal cap (55).
   The statement “choose a credible continuation” has no mathematical
   content without these data.
3. **No forced suffix match.**  The tail payoff need not equal
   $v_m^\ell$.  The correct condition is the acceptance polyhedron (59).
   Requiring equality is refuted by (86).
4. **No projective-boundary substitution.**  The vector $L$ in (24) is not
   automatically attainable.  Table (89) gives a quantitative separation.
5. **No debt-owner transfer.**  A full-set active-leaver or inactive-joiner
   defect does not imply positive debt for that player.  The owner, complete
   set, date, raw mass, and relative comparison remain distinct fields.
6. **No loss of the moving mark.**  Ordinary fixed-time occupation measures
   may see zero raw mass.  The common two-ended extraction and the positive
   weight (32) are mandatory.
7. **No exact-repair requirement.**  Table (101) has stationary errors
   tending to zero but no exact stationary equilibrium.  All universal
   producer statements must be accuracy-indexed.
8. **No clock shortcut.**  Joint absorption does not control a unilateral
   deviator.  Use playerwise opponent survival, and retain the Never endpoint
   when that survival does not contract.
9. **No local-to-global shortcut.**  Exact or strongly approximate one-stage
   inequalities do not by themselves control a deviation which removes
   absorption forever.  This applies both to infinite Bellman paths and to
   discretized absorption paths.
10. **No finite-atlas negative conclusion.**  Failure of stationary roots,
    bounded periods, one support grammar, or a chosen compactification is not
    the all-profile lower bound (85).

The standard-proper path remains the broadest clean positive target in this
question because it includes jumps and continuous flow without assuming
bounded memory or bounded period.  It is not used as a name for an unknown
equilibrium: the complete path data and the corrected strategic bridge are
required.  The more concrete boundary-intersection route is preferable when
available, because (56)--(60) verify the resulting profile directly.

## 10. Required resolution

A complete answer must take one of the following forms.

### 10.1 Positive resolution

Prove the finite repair-or-debt-descent lemma (79)--(81), including the
two-ended compactness needed to make its alternatives closed.  Deduce
(PPBC), construct terminal approximate equilibria at every accuracy, and
state which of (R1)--(R3) is produced in each clock/scale branch.

If the proof uses a standard-proper path, supply the path-to-profile bridge
of Section 6.1.  If it uses boundary intersection, prove the exact
all-behavior formulas (56)--(60).  If it uses a certified continuation cycle,
verify (45b)--(45c), its full-set anchor or other progress certificate, and
every exceptional clock.

Finally, prove the terminal-to-long-horizon passage with the correct order of
quantifiers.  Against fixed opponents, arbitrary behavioral deviations are
mixtures of deterministic planned Quit dates and Never.  If $V_{i,N}$ is the
best $N$-stage average payoff and $V_{i,\infty}$ the terminal cap, prove

$$
\limsup_{N\to\infty}V_{i,N}\le V_{i,\infty}.
\tag{106}
$$

The unbounded-quit-date case must retain the limiting mixture between a late
solo Quit and Never.  Deduce that a terminal $\delta$-equilibrium is an
$\eta$-equilibrium in every sufficiently long finite-horizon game whenever
$\eta>\delta$.  Compactness of $[-M,M]^I$ then selects one accumulation
payoff if a single uniform-equilibrium payoff is desired.

### 10.2 Architecture counterexample and corrected theorem

Give an explicit finite payoff table satisfying the positive plateau and
(FS), and prove that the quantified finite fork is false.  Identify exactly
which closedness, scale, prefix-accessibility, or purification claim fails.
Then state and prove a corrected repair-or-descent theorem, or explain why a
new compactification datum is unavoidable.

If the game nevertheless has an explicit First, stationary, cyclic, prefix-
intersection, or standard-proper resolution, say so prominently.  Such an
example refutes only the proposed fork, not terminal-equilibrium existence.

### 10.3 Genuine negative resolution

Give an explicit finite payoff table and prove the all-profile positive gap
(85).  The proof must quantify over arbitrary time-inhomogeneous behavioral
profiles, positive Never mass, unbounded stopping times, chattering hazards,
and every support pattern.  It must also prove the positive-plateau and
fully-summable provenance assumptions rather than infer them from a bounded
search.

Computational failure, nonexistence of an exact stationary equilibrium,
failure of every tested lasso, or separation from one prefix family is not a
genuine negative resolution.

## Answer

# Resolution

The finite algebraic part of the proposal is sound: compactness and attainment, horizon monotonicity, exact-debt interpretation, the marked terminal packet, the two-ended diagonal extraction, all table certificates in Section 4, and the five-scalar prefix calculus can all be proved.

The decisive implication is different. Neither the coupled compactification nor failure of a prefix intersection currently yields an exact root extension with a uniform debt decrement. In fact:

[
\boxed{\text{PPBC is an additional global existence conjecture, not a consequence of the stated compactness data.}}
]

A proof of PPBC for all finite quitting games would prove that every finite quitting game admits terminal (\varepsilon)-equilibria for every (\varepsilon>0). That problem remains open for four or more players; a 2026 paper explicitly states that the two- and three-player cases are known and the case of at least four players is not. ([Springer][1])

I do not know a counterexample to PPBC or a game satisfying the global gap (85). What can be given exactly is:

1. proofs of all finite claims;
2. the correct closure and nonattainment statement for (\mathscr A(r));
3. a concrete example showing that attainable payoff–cap pairs are not closed;
4. the precise reduction showing why the proposed finite fork contains the open step;
5. the exact kind of scale-sensitive descent that would be sufficient.

---

## 1. Compact exact chains and optimized debt

### 1.1 Compactness and attainment

For fixed (K), work in

[
[0,1]^{IK}\times[-M,M]^{I(K+1)}.
]

If (w\in[-M,M]^I), every pure endpoint (Q_i(x_{-i};w)) and
(C_i(x_{-i};w)) lies in ([-M,M]), since it is a convex combination of entries of (r) and (w_i). Thus backward induction keeps all (v^t) in ([-M,M]^I).

The conditions

[
v^K=0,\qquad
v^t=g(x^t;v^{t+1}),
]

and

[
g_i(x^t;v^{t+1})
-\max{Q_i(x^t_{-i};v^{t+1}),
C_i(x^t_{-i};v^{t+1})}=0
]

are closed conditions because all involved functions are continuous. Hence
(\mathcal N_K(r)) is closed in a compact set.

It is nonempty: starting at (v^K=0), choose a mixed Nash equilibrium of each finite one-stage game with continuation (v^{t+1}), and let (v^t) be its payoff.

Finally, (D^t) is obtained from ((x^t,v^{t+1},D^{t+1})) by continuous max-affine operations. Therefore

[
\mathcal C\longmapsto\sum_iD_i^0(\mathcal C)
]

is continuous on (\mathcal N_K(r)), and (S_K(r)) is attained.

### 1.2 The basic debt inequality

At an exact root, abbreviate

[
J_i^t=Q_i(x^t_{-i};v^{t+1}),\qquad
K_i^t=C_i(x^t_{-i};v^{t+1}).
]

Then (v_i^t=\max{J_i^t,K_i^t}), so

[
D_i^t
=====

\max{J_i^t,K_i^t+c_i(x^t)D_i^{t+1}}
-\max{J_i^t,K_i^t}.
]

Consequently,

[
0\le D_i^t\le c_i(x^t)D_i^{t+1}\le D_i^{t+1}.
]

Since (D_i^K=q_i^+),

[
0\le D_i^t\le q_i^+\le M.
\tag{88}
]

### 1.3 Horizon monotonicity

Take (\mathcal C\in\mathcal N_K(r)). Choose any exact Nash root (y) at continuation (v^0), prepend it, and shift the old chain by one date. At the new first date,

[
\widetilde v_i^0
================

\max{Q_i(y_{-i};v^0),C_i(y_{-i};v^0)}.
]

The shifted debt at date (1) is (D_i^0(\mathcal C)), hence

[
\begin{aligned}
\widetilde D_i^0
&=
\max{Q_i,C_i+c_i(y)D_i^0(\mathcal C)}
-\max{Q_i,C_i}\
&\le c_i(y)D_i^0(\mathcal C)
\le D_i^0(\mathcal C).
\end{aligned}
]

Summing and minimizing gives

[
S_{K+1}(r)\le S_K(r).
]

### 1.4 Exact debt equals terminal exploitability

Follow a length-(K) chain and then prescribe Never. At date (K), against opponents who always Continue, player (i)'s optimal payoff is

[
B_i^K=q_i^+.
]

If (B_i^{t+1}=v_i^{t+1}+D_i^{t+1}), the optimal-stopping recursion gives

[
\begin{aligned}
B_i^t
&=
\max\left{
Q_i(x^t_{-i};v^{t+1}),
H_i^t+c_i(x^t)B_i^{t+1}
\right}\
&=
\max\left{
Q_i(x^t_{-i};v^{t+1}),
C_i(x^t_{-i};v^{t+1})+c_i(x^t)D_i^{t+1}
\right}\
&=v_i^t+D_i^t.
\end{aligned}
]

Thus the all-Continue extension has

[
\beta_i=D_i^0.
]

Therefore (\inf_KS_K=0) produces terminal approximate equilibria of arbitrarily small error.

### 1.5 Sum versus maximum

Pointwise,

[
\max_iD_i^0\le\sum_iD_i^0\le n\max_iD_i^0.
]

Taking minima gives

[
E_K\le S_K\le nE_K.
]

---

## 2. The positive owner and the two clock branches

From (19), (21), and (88), for every (T),

[
d_0
\le D_{i_*}^0
\le
\left(\prod_{t=0}^{T-1}c_{i_*}(x^t)\right)D_{i_*}^T
\le
q_{i_*}^+
\prod_{t=0}^{T-1}c_{i_*}(x^t).
]

Hence (q_{i_*}>0) and

[
\prod_{t=0}^\infty c_{i_*}(x^t)
\ge \frac{d_0}{q_{i_*}}>0,
]

which is equivalent to

[
\sum_t-\log c_{i_*}(x^t)<\infty.
]

### 2.1 Divergent own clock

Suppose

[
\sum_t-\log(1-x_{i_*}^t)=\infty.
]

Then joint survival vanishes. Moreover, for every (j\ne i_*),

[
c_j(x^t)\le 1-x_{i_*}^t,
]

so player (j)'s opponent-survival product vanishes.

For every player and every date, the exact root property gives

[
v_i^t\ge J_i^t,
\qquad
v_i^t\ge H_i^t+c_i(x^t)v_i^{t+1}.
\tag{89}
]

For (j\ne i_*), iterating (89) along any deviating stopping rule produces a terminal remainder bounded by

[
M\prod_{u=t}^{N-1}c_j(x^u)\longrightarrow0.
]

Thus no deviation gains over (v_j^t).

For (i_*), all opponents' quit probabilities tend to zero, so

[
J_{i_*}^t\longrightarrow q_{i_*}>0.
]

Since (v_{i_*}^t\ge J_{i_*}^t),

[
\liminf_{t\to\infty}v_{i_*}^t\ge q_{i_*}>0.
]

Apply the finite-horizon supermartingale inequality generated by (89) to a deviation stopped at (N). On the event that neither the deviator nor an opponent ever quits, the true payoff is (0), while the residual (\liminf v_{i_*}^N) is nonnegative. Fatou's lemma therefore permits the residual to be retained and then discarded in the correct direction. Hence the arbitrary-deviation payoff is at most (v_{i_*}^t).

The prescribed profile absorbs almost surely, so its actual payoff is (v^t). It is therefore an exact terminal Nash equilibrium.

### 2.2 Fully summable branch

Under (FS), write

[
b_i^t=\sum_{a\in A^*}\xi_{x^t}(a)r_i(a),
\qquad
v_i^t=b_i^t+a(x^t)v_i^{t+1}.
]

Since

[
|b_i^t|\le M(1-a(x^t)),
]

we have

[
|v_i^t-v_i^{t+1}|
\le 2M(1-a(x^t)).
]

Also,

[
1-a(x^t)
\le\sum_j-\log(1-x_j^t),
]

so (\sum_t(1-a(x^t))<\infty). Thus (v^t) is Cauchy and converges to some (L).

Iterating the Bellman equation to date (N),

[
v^s
===

\sum_{t=s}^{N-1}
\left(\prod_{u=s}^{t-1}a(x^u)\right)b^t
+
\left(\prod_{u=s}^{N-1}a(x^u)\right)v^N.
]

Passing to the limit gives

[
v^s=U^s+\alpha_sL,
\qquad
\alpha_s=\prod_{t=s}^\infty a(x^t)>0.
]

The term (\alpha_sL) is therefore exactly a surviving Bellman boundary term, not an attained payoff.

---

## 3. The marked terminal packet

At the final root, abbreviate (i=i_*), (p(T)=p_{m,-i}(T)), and (c=p(\varnothing)). Then

[
J
=

cq_i+\sum_{\varnothing\ne T}p(T)r_i(T\cup{i}),
]

[
H
=

\sum_{\varnothing\ne T}p(T)r_i(T),
]

and

[
C^+=H+cq_i.
]

Because (q_i>0), (C^+\ge H), and

[
C^+-J
=====

\sum_{\varnothing\ne T}p(T)
\bigl(r_i(T)-r_i(T\cup{i})\bigr)
================================

\sum_{\varnothing\ne T}p(T)\Delta_i(T).
]

The last debt satisfies

[
\begin{aligned}
D_i^{K_m-1}
&=
\max{J,C^+}-\max{J,H}\
&\le [C^+-J]*+\
&\le
\sum*{\Delta_i(T)>0}p(T)\Delta_i(T).
\end{aligned}
]

Iteration of (15) gives

[
D_{m,i}^0\le \Pi_mD_{m,i}^{K_m-1}.
]

There are fewer than (C_A=2^n) nonempty opponent subsets. Select a term maximizing
(p(T)\Delta_i(T)), and then pass to a subsequence on which its set is fixed. This yields a nonempty (T_*) with (\Delta_i(T_*)>0) and

[
D_{m,i}^0
\le
C_A\Pi_mp_{m,-i}(T_*)\Delta_i(T_*)
\le
2MC_A\Pi_mp_{m,-i}(T_*).
]

Therefore

[
\Pi_mp_{m,-i}(T_*)
\ge
\frac{d_0}{2MC_A}.
]

This also implies the stronger global opponent-clock bound

[
\Pi_m\ge \frac{d_0}{2MC_A}.
\tag{90}
]

In particular, the total opponent clock of (i_*) is uniformly bounded over the whole finite chains, not merely on fixed forward windows.

Nothing here selects an owner from (T_*). It remains a simultaneous product atom.

### 3.1 Coupled two-ended extraction

All relevant coordinates lie in compact metrizable spaces. A single diagonal subsequence can simultaneously retain:

* every fixed forward window;
* every fixed reverse window;
* the fixed (i_*,T_*);
* (\omega_m\to\omega>0);
* every (Z_m^{r,s}) and (Y_m^{r,s}).

The reverse limits satisfy, with continuation directed toward decreasing reverse depth,

[
\check x^0\text{ is a root at }0,
\qquad
\check v^0=g(\check x^0;0),
]

and, for (d\ge1),

[
\check x^d\text{ is a root at }\check v^{d-1},
\qquad
\check v^d=g(\check x^d;\check v^{d-1}),
]

with the analogous debt recursions.

The limiting bridge products retain the exact factorizations

\[
Z^{r,s}
=c_{i_*}(x^r)Z^{r+1,s}
=Z^{r,s+1}c_{i_*}(\check x^s),
\tag{91}
\]

and

\[
Y^{r,s}
=a(x^r)Y^{r+1,s}
=Y^{r,s+1}a(\check x^s).
\tag{92}
\]

Moreover,

[
\omega
======

Z^{0,1}p_{-i_*}^{\check x^0}(T_*).
\tag{93}
]

Thus the required coupled compactification exists. What it does not supply is an attainable continuation or an exact new Nash root.

---

## 4. Finite table certificates

### 4.1 Cutoff one

At a zero-tail root,

[
V_i=\max{Q_i,H_i},
]

and the terminal best-response continuation after playing Continue is

[
H_i+c_iq_i^+=C_i^+(x).
]

Therefore

[
D_i(x)=\max{Q_i,C_i^+(x)}-V_i(x).
]

Since (V_i\ge Q_i),

[
D_i(x)=0
\iff
C_i^+(x)\le V_i(x).
]

If (q_i\le0), then (C_i^+=H_i\le V_i). If (q_i>0), condition (38) gives

[
C_i^+-Q_i
=========

\sum_{\varnothing\ne T}p_{-i}^x(T)
\bigl(r_i(T)-r_i(T\cup{i})\bigr)
\le0.
]

Thus every zero-tail root is safe under (38), and (S_1=0).

### 4.2 Pure First

Suppose exactly (S) quits at date (0).

For (j\notin S), the only relevant unilateral change is to Quit as well, giving (r_j(S\cup{j})).

For (j\in S) and (|S|\ge2), changing to Continue gives (r_j(S\setminus{j})).

For (S={j}), changing to Continue reaches the Never tail. Player (j) can then either quit alone later, receiving (q_j), or Never, receiving (0). The prescribed payoff is (q_j), so the condition is (q_j\ge0), exactly

[
r_j(\varnothing)-r_j({j})\le0.
]

Hence (\rho(S)=0) is necessary and sufficient.

### 4.3 One-owner stationary repair

Let only (k) quit with rate (h>0). Player (k)'s finite stopping alternatives all pay (q_k), and Never pays (0), so its cap is (\max{q_k,0}).

For (j\ne k), quitting after (t) previous live stages gives

[
\begin{aligned}
u_j(t)
={}&
\bigl(1-(1-h)^t\bigr)r_j({k})\
&+
(1-h)^t
\bigl((1-h)q_j+h,r_j({k,j})\bigr).
\end{aligned}
\tag{94}
]

Thus every deterministic stopping payoff lies on the segment joining the two values in (43). An arbitrary behavioral stopping rule is a mixture of deterministic stopping times and Never, and therefore cannot exceed their maximum.

Consequently, the repeated profile is an exact terminal equilibrium exactly when

[
q_k\ge0
]

and

[
(1-h)q_j+h,r_j({k,j})
\le r_j({k})
\quad(j\ne k).
]

For (q_k>0), failure for every (h) is exactly (42a). Setting (h=1) gives a strict sure-joiner. Taking (h_m\downarrow0), choosing a violating (j_m), and using finiteness to pass to a constant subsequence gives

[
r_{j'}({k})
\le q_{j'}.
]

The two selected players need not agree.

### 4.4 Stationary cap

Suppose (c_i(x)<1). If player (i) quits after (t) previous Continue stages, its payoff is

[
(1-c_i(x)^t)N_i(x)+c_i(x)^tJ_i(x).
\tag{95}
]

Therefore all deterministic quit times lie between (N_i) and (J_i). Behavioral randomization adds only convex combinations. Both endpoints are attainable: Quit immediately gives (J_i), and Never gives (N_i). Hence

[
\operatorname{Cap}_i(x)=\max{J_i(x),N_i(x)}.
]

If (c_i(x)=1), the opponents always Continue, and the cap is (q_i^+).

Thus (\operatorname{Reg}_i=\operatorname{Cap}_i-W_i) is the exact arbitrary-behavior regret.

### 4.5 Exact cycles

For a product-jump loop, (45) implies joint survival around a cycle is strictly below one, because

[
\prod_\ell a(z^\ell)
\le
\prod_\ell c_i(z^\ell)<1.
]

Iterating (44) therefore identifies (w^\ell) with the actual payoff of the periodically repeated profile.

For a deviating player (i), the one-stage Nash inequalities make (w_i^\ell) a Snell supersolution. After (N) cycles the terminal remainder is bounded by

[
2M\left(\prod_{\ell=0}^{L-1}c_i(z^\ell)\right)^N,
]

which tends to zero. Hence the periodic profile is an exact terminal Nash equilibrium.

For a block cycle, define the cap operator

[
\Phi_i^k(z)=
\max{A_i^k,T_i^k+\chi_i^kz}.
]

Condition (45c) is

[
\Phi_i^k(w_i^{k+1}+\beta_i^{k+1})
\le w_i^k+\beta_i^k.
]

Iteration around cycles, followed by playerwise contraction, gives

[
\operatorname{Cap}_i^k\le w_i^k+\beta_i^k.
]

Together with (45b), the actual regret is at most (\beta_i^k). Without playerwise contraction, this iteration leaves a terminal Snell remainder; it cannot simply be removed.

---

## 5. Prefix acceptance calculus

The prescribed payoff formula follows by conditioning on the first absorbing date:

[
U_i(p\star\tau)=B_i+Pw_i.
]

Against the opponents' prefix, a deviator's pure possibilities are:

* Quit at a deterministic date (t<\ell), obtaining (A_{i,t});
* Continue through the entire prefix, obtaining
  [
  T_i+\chi_i(w_i+\beta_i).
  ]

There is only one live public history. Any behavioral deviation before the tail is a randomization over these deterministic stopping plans, together with the option of reaching the tail. Conversely, near-optimal tail deviations realize the second value arbitrarily closely. Hence

[
\sup_{\sigma_i}U_i(\sigma_i,(p\star\tau)_{-i})
==============================================

\max{A_i,T_i+\chi_i(w_i+\beta_i)}.
]

Therefore

[
R_i^p(w_i,\beta_i)
==================

\max{A_i,T_i+\chi_i(w_i+\beta_i)}
-(B_i+Pw_i),
]

and (59) is exactly equivalent to (R_i^p\le\varepsilon).

### 5.1 Degenerate scalar cases

Write

[
f_1(w)=A-B-Pw,
\qquad
f_2(w)=T-B+(\chi-P)w+\chi\beta.
]

Then (R=\max(f_1,f_2)).

When (0<P<\chi), the interval and balance point in (61)–(62) are correct.

When (P=0<\chi), acceptance requires

[
A-B\le\varepsilon
]

and

[
w\le
\frac{B+\varepsilon-T-\chi\beta}{\chi}.
]

The minimum value is (A-B), attained on the half-line

[
w\le \frac{A-T-\chi\beta}{\chi}.
]

When (0<P=\chi), acceptance requires

[
T-B+\chi\beta\le\varepsilon
]

and

[
w\ge\frac{A-B-\varepsilon}{P}.
]

The minimum is (T-B+\chi\beta), attained on

[
w\ge\frac{A-T-\chi\beta}{\chi}.
]

When (\chi=0), necessarily (P=0), and

[
R=\max{A,T}-B
]

is independent of (w,\beta). The acceptable set is either all values of (w) or empty.

### 5.2 Composition

A deterministic deviation in the concatenated prefix either stops in block (1), or reaches block (2). This gives

[
A'=\max{A_1,T_1+\chi_1A_2}.
]

The other identities follow by ordinary conditioning:

[
T'=T_1+\chi_1T_2,\qquad
\chi'=\chi_1\chi_2,
]

[
B'=B_1+P_1B_2,\qquad
P'=P_1P_2.
]

Thus (63) is exact.

---

## 6. The correct closure convention

Every attainable certificate satisfies

[
w_i\in[-M,M],\qquad
w_i+\beta_i\in[-M,M],
\qquad
0\le\beta_i\le2M.
]

Thus the Euclidean closure

[
\overline{\mathscr A(r)}
\subseteq[-M,M]^I\times[0,2M]^I
]

is compact.

For fixed (p), (R_i^p) is continuous, so

[
\inf_\tau \mathcal R(p,\tau)
============================

\min_{(w,\beta)\in\overline{\mathscr A(r)}}
\max_iR_i^p(w_i,\beta_i).
\tag{96}
]

The minimum on the right need not belong to (\mathscr A(r)).

More globally, let (\Sigma) be the set of five-scalar summaries of all positive-length prefixes (p_{m,\ell}). Its closure is compact. Then

[
\inf_{m,\ell,\tau}\mathcal R(p_{m,\ell},\tau)
=============================================

\min_{\substack{s\in\overline\Sigma\
(w,\beta)\in\overline{\mathscr A(r)}}}
F(s,w,\beta),
\tag{97}
]

where (F) is the continuous max-regret function.

Neither component of a minimizing pair in (97) need be executable:

* (s) may be only a limit of longer prefixes, possibly the identity summary;
* ((w,\beta)) may be a nonattainable cap/payoff pair.

Thus failure of R2 means

[
\mathcal R(p_{m,\ell},\tau)>\varepsilon
\quad\text{for every actual candidate}.
]

It implies that the relaxed minimum in (97) is at least (\varepsilon), but equality may occur without an actual minimizing candidate. The robust form is the strict inequality in (84).

### 6.1 Explicit nonclosedness of (\mathscr A(r))

Regression 8.5 gives a particularly direct example. For

[
r({1})=(1,-1),\quad
r({2})=(-1,-1),\quad
r({1,2})=(-2,0),
]

the stationary profiles (x(a)=(a,2/3)) have certificates

[
w(a)=
\left(-1,\frac{a-2}{a+2}\right),
\qquad
\beta(a)=
\left(0,\frac{a^2}{a+2}\right).
]

Hence

[
(w(a),\beta(a))
\longrightarrow((-1,-1),(0,0)).
\tag{98}
]

But the game has no exact behavior equilibrium.

To see this, represent each player's behavior strategy by the distribution of its stopping time in
(\mathbb N\cup{\infty}). Let (\alpha,\beta) be the distributions of players (1,2).

Given (\alpha), player (2)'s payoff from choosing time (t), including (t=\infty), is

[
-1+\alpha_t.
]

A probability distribution on a countable set has a largest atom, say (\delta>0), and the set of atoms equal to (\delta) is finite. Therefore, in equilibrium, (\beta) must be supported on this finite argmax set.

If (\beta_\infty>0), then (\alpha_\infty=\delta>0). Player (1)'s payoff from Never is

[
-1+\beta_\infty.
]

Choosing a finite date later than every finite point in the support of (\beta) gives

[
-1+2\beta_\infty,
]

a strict improvement. This contradicts (\alpha_\infty>0).

If (\beta_\infty=0), let (t_*) be the largest point in the support of (\beta). Then (\alpha_{t_*}=\delta>0). Player (1)'s payoff from stopping at (t_*) is

[
-1-\beta_{t_*},
]

whereas stopping after (t_*) gives (-1). Again an action in the support of (\alpha) is not a best response.

Thus the limit pair in (98) is not attainable. In particular,

[
\boxed{\mathscr A(r)\text{ is not closed.}}
]

There is also nonattainment after a positive prefix. Take the one-stage prefix (p=(0,2/3)). Its summaries are

[
(A_1,T_1,\chi_1,B_1,P)
======================

\left(-1,-\frac23,\frac13,-\frac23,\frac13\right),
]

[
(A_2,T_2,\chi_2,B_2,P)
======================

\left(-1,0,1,-\frac23,\frac13\right).
]

For the tails (x(a)),

[
R_1^p=0,
]

and

[
R_2^p
=====

\frac{a^2+\frac43a}{a+2}
\longrightarrow0.
]

The infimum is zero. It cannot be attained, because attainment at zero would make the spliced profile an exact equilibrium, which the preceding argument excludes.

---

## 7. Standard-proper paths: the conditional compiler

A standard-proper sequentially perfect path does yield approximate equilibria.

The discretization proceeds by retaining all jumps whose conditional absorption mass exceeds a mesh (\delta), and partitioning the remaining continuous portions into packets of conditional mass at most (\delta). At retained jumps, use the exact product action from (68). On a small continuous packet, only singleton flow has first-order mass; a product action matching the singleton masses has simultaneous-quitter mass (O(\delta^2)).

Consequently there is an error (\eta(\delta)\to0) such that every discretized stage satisfies both

[
g_i((b_i,x_{-i});y)\le g_i(x;y)+\eta(\delta)
]

for every pure (b_i), and

[
g_i((b_i,x_{-i});y)\ge g_i(x;y)-\eta(\delta)
]

for every pure action used with positive probability. Exact jump perfection gives this directly at retained jumps; (72)–(73), together with the (O(\delta^2)) simultaneous mass estimate, gives it on flow packets.

This constructs absorbing, sequentially (\eta(\delta))-perfect discrete profiles whose absorption paths converge to (\pi). The established absorption-path theorem identifies such paths with limits of approximate equilibria, after accounting for the simple-equilibrium alternatives. ([Springer][2])

The global Never issue cannot be settled by the local inequalities alone. The correct block argument has two cases:

* opponent-side blocks recur often enough, and the Snell remainders vanish, making the discretized profile globally approximately optimal;
* some player has arbitrarily long blocks with negligible opponent hazard, from which a one-owner stationary approximate equilibrium is extracted.

This stationary fallback appears explicitly in the original Solan–Vieille local-to-global proposition. ([Tel Aviv University Math Department][3])

Thus R3 is a valid conditional output. The missing task is constructing such a path from the positive-debt two-ended limit.

---

## 8. Mandatory regressions

### 8.1 Off-chain stationary repair

At continuation (0), player (1)'s endpoints are

[
Q_1=1+x_2,\qquad C_1=3x_2,
]

and player (2)'s are

[
Q_2=-1+2x_1,\qquad C_2=0.
]

The unique mutual best response is

[
x_1=x_2=\frac12,
]

with value

[
L=\left(\frac32,0\right).
]

At continuation (L),

\[
C_1-Q_1
=\left(\frac32+\frac32x_2\right)-(1+x_2)
=\frac12+\frac12x_2>0.
\]

so (x_1=0). Then player (2) strictly prefers Continue, so (x_2=0). Thus all earlier roots are all-Continue.

At the final root,

[
D_1=\max\left{\frac32,\frac32+\frac12\right}-\frac32
=\frac12,
\qquad D_2=0.
]

All-Continue roots propagate this debt unchanged, proving (87).

For the one-owner profile ((h,0)), player (2)'s alternative endpoint is

[
(1-h)(-1)+h(1)=-1+2h.
]

It is at most (r_2({1})=0) exactly when (h\le1/2).

For the first all-Continue root of a minimizing chain,

[
P=\chi_i=1,\qquad B_i=T_i=0,\qquad A_i=q_i.
]

The attainable tail (((1,0),0)) gives

[
R_1=\max{1,1}-1=0,\qquad
R_2=\max{-1,0}-0=0.
]

So R2 accepts the off-chain repair through a positive prefix.

### 8.2 Boundary value separated from equilibrium payoffs

At continuation (0), (x=(1,1/2)) is an exact root with value (L=(3/2,0)). At continuation (L), all-Continue is an exact root, so arbitrarily long prefixes occur.

For an (\varepsilon)-equilibrium, let (a,b,c,z) denote the probabilities of ({1},{2},{1,2}), and Never.

Player (2)'s prescribed payoff is (-b), while Never gives (0), hence

[
b\le\varepsilon.
]

For player (1), consider a deviation that suppresses its Quit actions through date (N-1) and Quits at (N). Couple this with the original randomizations. On every original joint-quit event before (N), its payoff changes from (2) to (3). On original solo-(1) events it loses nothing, since the deviation ultimately quits and receives at least (1). Letting (N\to\infty) gives a gain of at least (c), so

[
c\le\varepsilon.
]

Therefore

[
u_1
===

(a+b+c)+2b+c
\le1+3\varepsilon.
]

If (|u_1-3/2|\le\varepsilon), then

[
\frac32-\varepsilon\le1+3\varepsilon,
]

so

[
\varepsilon\ge\frac18.
]

Nevertheless, ({1}) is a pure First certificate, and every one-owner rate (h>0) satisfies (42).

### 8.3 Joiner defect without debt transfer

At continuation zero,

[
Q_1=1-x_2,\qquad C_1=x_2,
]

and

[
Q_2=\eta(2x_1-1),\qquad C_2=0.
]

Thus (x=(1/2,1/2)) is an exact root with value ((1/2,0)).

For player (1),

[
C_1^+
=====

\frac12r_1({2})+\frac12q_1=1,
]

so (D_1=1-1/2=1/2). Player (2) has (q_2^+=0), hence (D_2=0).

The joining defect

[
r_2({1,2})-r_2({1})=\eta
]

does not create player (2) debt. The one-owner condition for player (1) is

[
(1-h)(-\eta)+h\eta
==================

-\eta+2\eta h\le0,
]

which holds for (h\le1/2).

### 8.4 Moving terminal fence

For a symmetric action (p), each player's endpoints are

[
Q=1-2p,
\qquad
C=2p+(1-p)w.
]

Indifference is equivalent to

[
w=\frac{1-4p}{1-p}.
]

The sequence in (97) satisfies precisely this relation with
(w=v^{t+1}), and (p_{K-1}=1/4), so the chains are exact.

At every root both actions are best replies, hence

[
D_i^t=(1-p_t^{(K)})D_i^{t+1}.
]

Starting from (D_i^K=1) and telescoping gives

[
D_i^t
=====

\frac{3(3/2)^{K-1-t}}
{6(3/2)^{K-1-t}-2}

> \frac12.
> ]

For fixed (t), (p_t^{(K)}\to0) and (v_i^t\to1).

At the last stage, for owner (1) and (T_*={2}),

[
\Delta_1({2})=2-(-1)=3.
]

Since (p_{K-1}=1/4),

[
\omega_m
========

# \Pi_m\frac14

\frac13D_{m,1}^0

> \frac16.
> ]

Thus the fixed-time raw actions vanish but the transported full atom does not.

### 8.5 Vanishing stationary errors without an exact stationary equilibrium

The calculations give

[
W_1=-1,\qquad
W_2=\frac{a-2}{a+2}.
]

Player (1)'s immediate-Quit and Never endpoints are both (-1), so

[
\operatorname{Reg}_1=0.
]

For player (2),

[
J_2=-1+a,\qquad N_2=-1,
]

hence

[
\operatorname{Reg}_2
====================

# (-1+a)-\frac{a-2}{a+2}

\frac{a^2}{a+2}.
]

For completeness, there is no exact stationary equilibrium. Let a stationary action be ((u,v)).

If (u=0), player (2) can improve to Never unless (v=0); at ((0,0)), player (1) can quit for payoff (1).

If (u>0), zero regret for player (2) requires

[
W_2(u,v)=u-1.
]

After clearing denominators, this condition becomes

[
u^2(v-1)=0,
]

so (v=1). But then player (1)'s actual payoff is (-1-u), while Never yields (-1), a strict improvement.

The one-owner condition fails because

[
(1-h)q_2+h,r_2({1,2})
=-1+h>-1.
]

### 8.6 Product-jump loops

The compiler in Section 4.5 accepts any actual data satisfying (44)–(45), independently of whether the three elementary repairs fail. Searching only bounded periods or one support chart cannot exclude this branch, much less an unbounded-period approximation or an absorption path.

---

## 9. Why PPBC is the unresolved theorem

Assume PPBC for every finite quitting game. Given an arbitrary game:

1. (S_K) decreases to some (s_\infty\ge0).
2. If (s_\infty=0), Section 1.4 gives terminal approximate equilibria.
3. If (s_\infty>0), extract (i_*) as in (19).
4. Its opponent clock is summable.
5. If its own clock diverges, Section 2.1 gives an exact equilibrium.
6. Otherwise its own clock is summable, so (FS) holds.
7. PPBC then supplies R1, R2, or R3, each of which compiles to a terminal (\varepsilon)-equilibrium.

Thus

[
\boxed{
\text{universal PPBC}
\Longrightarrow
\text{every finite quitting game has terminal }\varepsilon\text{-equilibria}.
}
\tag{99}
]

Existence for arbitrary four-or-more-player quitting games is precisely the currently unresolved case. The absorption-path literature likewise states that general (\varepsilon)-equilibrium existence is open and that, after the simple branches are removed, it is equivalent to producing a sequentially perfect absorption path. ([Springer][2])

The two-ended packet does not bridge that gap. It gives:

* an owner (i_*);
* a positive joining loss (\Delta_{i_*}(T_*));
* a nonvanishing raw product cylinder;
* exact chronological survival factorizations.

It does not give:

* an attainable payoff–cap pair;
* a credible punishment tail;
* a new debt owner;
* an exact Nash root at a modified continuation;
* a finite block whose insertion strictly lowers total initial debt.

Regression 8.3 specifically rules out the most tempting owner-transfer inference.

---

## 10. The finite fork and the required descent scale

Under the positive plateau, alternative 2 of the proposed finite fork is already incompatible with convergence. Indeed,

[
s_\infty
\le S_{K_m+L}
\le S_{K_m}-c.
]

For sufficiently large (m),

[
S_{K_m}<s_\infty+\frac c2,
]

giving (s_\infty<s_\infty-c/2), a contradiction.

Therefore, within the plateau branch,

[
\boxed{
\text{the finite repair-or-fixed-descent lemma is logically equivalent to producing R1--R3.}
}
]

It is not a weaker compactness lemma: all the substantive work is hidden in constructing the exact extension in (80).

If a scale-dependent decrement (c_m) replaces (c), positivity alone is insufficient. Since

[
S_{K_m+L_m}\ge s_\infty,
]

a one-step descent contradicts the plateau only when

[
c_m>S_{K_m}-s_\infty.
\tag{100}
]

An iterative version is sufficient if exact extensions produce

[
S_{K^{r+1}}\le S_{K^r}-c_r
]

and, for some finite (R),

[
\sum_{r=0}^{R-1}c_r>S_{K^0}-s_\infty.
\tag{101}
]

A condition such as merely (c_m>0), (c_m\to0), or even infinitely many strict improvements does not contradict convergence.

The nonclosedness example in Section 6 does not itself refute the fixed-(c) fork, because that example has an R1 stationary approximation. It shows instead why a relaxed boundary minimizer cannot be used as the continuation in an exact chain.

---

## 11. Failure classification

Failure to convert the coupled boundary into R1–R3 would refute this boundary architecture only. In particular:

* separation from the selected minimizing prefixes does not quantify over all behavior profiles;
* a relaxed closure minimizer may be nonattainable;
* R1–R3 do not include every conceivable punishment-based finite construction;
* failure of bounded periods or standard support atlases says nothing about arbitrary paths.

A global negative result requires the independent estimate

[
\inf_\sigma\max_i\beta_i(\sigma)\ge\varepsilon_0>0.
]

No such estimate follows from the positive plateau, the marked atom, or prefix separation.

The sharp current conclusion is therefore

[
\boxed{
\begin{array}{l}
\text{All finite identities, certificates, prefix formulas, regressions, and the}\
\text{two-ended compactification are valid. The missing repair-or-debt-descent}\
\text{implication is not proved by them and is at least as strong as the}\
\text{open general }\varepsilon\text{-equilibrium problem for finite quitting games.}\
\text{No robust all-profile counterexample is presently obtained.}
\end{array}
}
]

[1]: https://link.springer.com/10.1007/s00182-026-00982-6 "https://link.springer.com/10.1007/s00182-026-00982-6"
[2]: https://link.springer.com/content/pdf/10.1007/s10107-022-01807-6.pdf "https://link.springer.com/content/pdf/10.1007/s10107-022-01807-6.pdf"
[3]: https://www.math.tau.ac.il/~eilons/quitting19.pdf "Quitting Games"

---

## Audit correction (3 August 2026)

This correction preserves the answer above but narrows several of its status
claims.  The answer is **not** a positive resolution, an architecture
counterexample, or a genuine negative resolution in the sense of Section 10.
In particular, it does not prove PPBC and it does not prove the quantified
repair-or-fixed-descent alternative (79)--(81).  Its main valid conclusion is
that the finite algebra and the two-ended provenance data do not, by
compactness alone, produce the missing strategically credible continuation.

### A. Exact correction to the terminal-clock statement

The sentence following (90) overstates the consequence of the packet bound.
By definition,

\[
\Pi_m=\prod_{t=0}^{K_m-2}c_{i_*}(x_m^t)
\]

does **not** include the marked final root $x_m^{K_m-1}$.  Therefore (90)
uniformly bounds the opponent clock only through the prefix ending immediately
before that final root.  It does not bound the clock over the whole finite
chain.  Indeed, a member of $T_*$ may Quit surely at the final root, making
$c_{i_*}(x_m^{K_m-1})=0$, while
$p_{m,-i_*}(T_*)>0$.  The correct coupled object is precisely the pair

\[
\left(\Pi_m,\ p_{m,-i_*}(T_*)\right),
\]

whose product has the positive lower bound (30).  The terminal factor may not
be folded into the prefix clock.

### B. Proof-status correction

The following parts are established by the calculations in the answer:

1. finite-chain compactness and attainment, horizon monotonicity, exact-debt
   semantics, and the sum-versus-maximum comparison;
2. the positive-owner clock split, the fully summable relative-boundary
   identity, the terminal packet estimate, and the common two-ended diagonal
   extraction, subject to the clock correction above;
3. cutoff-one safety, direct pure First, the one-owner stationary criterion,
   the generic stationary cap, and the finite-prefix max-affine calculus;
4. the exact contracting product-jump compiler and its finite-block analogue;
   and
5. the nonclosedness example for attainable payoff--cap pairs.

The following requested parts were not proved in the original answer and must
not be counted as established there:

1. the repair-or-debt-descent implication with fixed $L,c,m_0$, an exact
   zero-boundary extension, and the retained full-set anchor;
2. construction of any R1--R3 output from the positive-plateau two-ended
   limit;
3. the complete path-to-profile theorem for R3--the paragraph in Section 7 is
   a literature-dependent proof sketch, not the requested derivation for all
   the displayed path axioms;
4. the terminal-to-long-horizon estimate (106) and its payoff-selection
   corollary; and
5. the general accuracy-indexed First producer.

The original answer also omitted the two-player repair calculation and
mandatory Regression 8.7.  They are supplied next.

### C. The omitted two-player pair repair

Use the notation

\[
B=r_k(\{j\}),\quad C=r_k(\{k,j\}),\quad
D=r_j(\{k\}),\quad E=r_j(\{j\}),\quad
F=r_j(\{k,j\}).
\]

The marked packet gives $B>C$, and the weak-preemptor conclusion gives
$D\le E$.  Let $j$ Quit surely and let $k$ Quit with probability
$p\in(0,1]$.  Absorption occurs at the first stage.  Player $k$'s two
pure endpoints are $B$ and $C$, so

\[
\operatorname{Cap}_k(p)=B,
\qquad
\operatorname{Reg}_k(p)=p(B-C).
\]

Player $j$'s prescribed payoff is

\[
W_j(p)=(1-p)E+pF.
\]

Against the stationary owner hazard, every deterministic Quit time gives a
value between $W_j(p)$ and $D$; Never gives $D$.  Randomized behavioral
stopping adds only convex combinations.  Hence

\[
\operatorname{Cap}_j(p)=\max\{W_j(p),D\}.
\]

Since $D\le E$,

\[
\operatorname{Reg}_j(p)
=\max\{0,D-W_j(p)\}
\le p|F-E|.
\]

Consequently,

\[
\max\{\operatorname{Reg}_k(p),\operatorname{Reg}_j(p)\}
\le p\bigl((B-C)+|F-E|\bigr)\longrightarrow0.
\]

This proves the two-player accuracy-indexed pair repair against arbitrary
behavioral deviations.  It does not assert existence of an exact stationary
equilibrium.

### D. The omitted sure-set regression and the full-rate warning

For the three-player table (R7.1), the half--half--half zero-tail root has
both endpoints equal for every player and value

\[
v=(1,1/4,0).
\]

Its exact cutoff-one debt is

\[
D=(1/4,0,0).
\]

For owner \(0\), the effective contributions to the final joining comparison
from the opponent atoms
\(\varnothing,\{1\},\{2\},\{1,2\}\) are respectively

\[
0,-1,-1,3.
\]

Thus the positive marked atom is the full set \(T_*=\{1,2\}\).  Every
positive owner-solo rate is obstructed by player \(1\), since

\[
r_1(\{0\})=0<(1-p)r_1(\{1\})+p\,r_1(\{0,1\})=p.
\]

The natural small-owner-hazard sure-set repairs nevertheless all fail:
for \(T=\{1\}\) and \(T=\{2\}\), owner \(0\) prefers joining \(T\), while
for \(T=\{1,2\}\), player \(1\) prefers leaving because

\[
r_1(\{2\})=1>0=r_1(\{1,2\}).
\]

This is only a zero-hazard or small-hazard obstruction.  It is not a
full-rate exclusion.  At \(p=1\) with \(T=\{1\}\), the terminal set is
\(\{0,1\}\), which is an exact direct pure First certificate.  Thus any
static sure-set analysis must test the exact cap inequalities over the whole
interval \(p\in(0,1]\); limiting inequalities as \(p\downarrow0\) cannot
exclude a repair at a positive or full-rate endpoint.

There is a second calibration showing that even a genuine full-rate
exclusion of this grammar does not force a dynamic repair.  Consider

\[
\begin{array}{c|ccc}
S&r_0(S)&r_1(S)&r_2(S)\\ \hline
\{0\}&1&-1&0\\
\{1\}&0&0&1\\
\{2\}&0&5&0\\
\{0,1\}&1&1&0\\
\{0,2\}&1&0&0\\
\{1,2\}&4&0&0\\
\{0,1,2\}&1&3&1.
\end{array}
\tag{A1}
\]

For every \(p\in(0,1]\) and every sure set
\(T\subseteq\{1,2\}\), the stationary profile in which owner \(0\) uses
hazard \(p\), every member of \(T\) Quits surely, and all other players
Continue has exploitability at least \(1/3\).  A direct exhaustive check uses
the following witnesses:

\[
\begin{array}{c|c|c}
T&\text{range}&\text{player with gain at least }1/3\\ \hline
\varnothing&0<p\le1&1\\
\{1\}&p\le2/3&0\\
\{1\}&p>2/3&2\\
\{2\}&p\le2/3&0\\
\{2\}&p>2/3&1\\
\{1,2\}&p\ge1/9&0\\
\{1,2\}&p<1/9&1.
\end{array}
\tag{A2}
\]

Every direct pure First set also has exploitability at least \(1\).  For the
seven nonempty sets in the order

\[
\{0\},\{1\},\{2\},\{0,1\},\{0,2\},\{1,2\},\{0,1,2\},
\]

one may use, respectively, a Quit-now deviation by players
\(1,0,0,2,1\), a Never deviation by player \(1\), and a Never deviation by
player \(0\).

Nevertheless (A1) has an exact stationary terminal equilibrium with hazards

\[
x=(1/2,1,1/4)
\]

and payoff

\[
W=(1,3/4,1/2).
\]

Players \(0\) and \(2\) are exactly indifferent between their two endpoints,
at values \(1\) and \(1/2\), respectively.  Player \(1\)'s immediate-Quit
value is \(3/4\); if player \(1\) Never Quits, the opponents' per-stage
absorbing contribution is \(1/4\), their survival probability is \(3/8\),
and its eventual payoff is

\[
\frac{1/4}{1-3/8}=\frac25<\frac34.
\]

Thus its exact cap is also \(3/4\).  This example excludes the whole
owner-\(0\)/sure-opponent grammar and all direct pure First sets, yet closes
by a different stationary product root.  Failure of a selected static
grammar therefore does not imply that an equilibrium must be periodic,
time-inhomogeneous, or described by a dynamic lasso.

### E. Standalone nonclosedness theorem

The no-exact-behavior-equilibrium argument in Section 6.1 is sound and may be
isolated as the following theorem.

> For the two-player table
> \[
> r(\{1\})=(1,-1),\qquad r(\{2\})=(-1,-1),\qquad
> r(\{1,2\})=(-2,0),
> \]
> there is no exact behavioral terminal Nash equilibrium, although stationary
> profiles have terminal exploitability tending to zero.  Consequently the
> set of attainable payoff--exact-cap pairs is not closed.

To justify the only implicit step in the original proof, before absorption
the public history is uniquely a string of all-Continue outcomes.  Hence each
behavior strategy induces a probability distribution on
\(\mathbb N\cup\{\infty\}\), its planned Quit time, and the two players' private
randomizations induce independent stopping times.  Conversely every such
distribution is realized by a hazard sequence.

If player \(1\)'s stopping distribution is \(\alpha\), player \(2\)'s payoff
from the pure stopping time \(t\), including \(t=\infty\), is
\(-1+\alpha_t\).  A probability distribution on a countable set has a
positive largest atom, and only finitely many atoms attain that maximum.
Thus an equilibrium distribution of player \(2\) must have finite support
inside this argmax set.  If it puts positive mass on \(\infty\), player \(1\)
strictly improves by stopping after all of its finite support.  If it puts no
mass on \(\infty\), player \(1\) strictly improves from stopping at the largest
supported time to stopping immediately after it.  Both cases contradict
best-response support.  The stationary certificates in (98) converge to an
exact-cap pair which therefore cannot be attainable.

### F. Final corrected verdict

The original quantifiers and anchors of the decisive alternative remain
unmet: no uniform \(L\) or \(c\) is produced, no chain
\(\mathcal C'_m\in\mathcal N_{K_m+L}(r)\) is constructed, and no repair
consumes the retained tuple \((i_*,T_*,\omega,Z,Y)\).  The fixed-decrement
argument only proves that, **if** such an extension theorem existed, its
descent branch would contradict the plateau.

Accordingly, Q132 isolates and protects the central producer problem but does
not close it.  It supplies exact finite interfaces and several strong
regressions; PPBC, the anchored repair-or-descent theorem, and a genuine
all-profile counterexample all remain open.
