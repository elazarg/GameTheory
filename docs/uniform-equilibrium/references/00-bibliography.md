# Bibliography

Durable citations for the uniform-equilibrium literature. One block per work,
grouped by role. Every DOI below was seen to resolve during the 2026-08-02
research passes unless flagged.

`bib?` column: whether the work has an entry in `latex/references.bib` (`R`),
in the manuscript bibliography of
`docs/uniform-equilibrium/manuscript/UniformEquilibriumFrontierManuscript.tex` (`M`), both, or neither
(`—`). Entries marked `—` are the concrete bibliography gap; see the durable
[bibliography maintenance queue](BibliographyMaintenance.md).

---

## Foundations

| Work | Citation | DOI | bib? |
|---|---|---|---|
| Shapley 1953 | *Stochastic games*, PNAS **39**, 1095–1100 | — | R + M |
| Gillette 1957 | *Stochastic games with zero stop probabilities*, Contributions to the Theory of Games III | — | — |
| Everett 1957 | *Recursive games*, Contributions to the Theory of Games III | — | — |
| Fink 1964 | *Equilibrium in a stochastic n-person game*, J. Sci. Hiroshima Univ. A-I **28**, 89–93 | — | M |

## Zero-sum: the uniform value

**Blackwell & Ferguson 1968** — *The Big Match*. Annals of Mathematical
Statistics **39**(1), 159–163.
DOI [`10.1214/aoms/1177698513`](https://doi.org/10.1214/aoms/1177698513). `M`

**Kohlberg 1974** — *Repeated Games with Absorbing States*. Annals of
Statistics **2**(4), 724–738 (July 1974).
DOI [`10.1214/aos/1176342760`](https://doi.org/10.1214/aos/1176342760). `—`

**Bewley & Kohlberg 1976** — *The asymptotic theory of stochastic games*.
Mathematics of Operations Research **1**(3), 197–208.
DOI [`10.1287/moor.1.3.197`](https://doi.org/10.1287/moor.1.3.197). `M`

**Bewley & Kohlberg 1976b** — *The Asymptotic Solution of a Recursion Equation
Occurring in Stochastic Games*. Mathematics of Operations Research **1**(4),
321–336. DOI [`10.1287/moor.1.4.321`](https://doi.org/10.1287/moor.1.4.321).
⚠ Distinct from the above — this is where the `n`-stage expansion lives. `—`

**Mertens & Neyman 1981** — *Stochastic games*. International Journal of Game
Theory **10**(2), 53–66 (June 1981).
DOI [`10.1007/BF01769259`](https://doi.org/10.1007/BF01769259).
Companion announcement: PNAS **79**(6), 2145–2146 (1982),
DOI [`10.1073/pnas.79.6.2145`](https://doi.org/10.1073/pnas.79.6.2145).
`R + M` — ⚠ **but both repo entries lack the DOI**, and neither records the
PNAS companion.

**Szczechla, Connell, Filar & Vrieze 1997** — re-proof of Bewley–Kohlberg
avoiding Tarski's principle. SIAM J. Control Optim.
DOI [`10.1137/S0363012995284138`](https://doi.org/10.1137/S0363012995284138).
`—`

**Oliu-Barton 2014** — elementary re-proof. Mathematics of Operations Research.
DOI [`10.1287/moor.2013.0642`](https://doi.org/10.1287/moor.2013.0642). `—`

**Renault 2019** — *A Tutorial on Zero-sum Stochastic Games*. arXiv:1905.06577.
The accessible modern restatement of Mertens–Neyman and Bewley–Kohlberg; the
source for most `[secondary]` statements in
[`10-zero-sum-value.md`](10-zero-sum-value.md). `—`

## Zero-sum: partial observation and the boundary

**Rosenberg, Solan & Vieille 2002** — *Blackwell Optimality in Markov Decision
Processes with Partial Observation*. Annals of Statistics **30**(4),
1178–1193. DOI
[`10.1214/aos/1031689022`](https://doi.org/10.1214/aos/1031689022).
Author-hosted [primary PDF](https://www.math.tau.ac.il/~eilons/hidden15.pdf).
`T` `[primary]`

Theorem 1 gives every finite-state, finite-action, finite-signal POMDP a
uniform expected-average value for every initial distribution and, for each
\(\varepsilon>0\), one behavior strategy that is \(\varepsilon\)-optimal for
all sufficiently long horizons and all sufficiently patient discounts. The
general strategy need be neither pure nor stationary; the paper's example
also shows that exact Blackwell-optimal strategies need not exist.

**Chatterjee, Saona & Ziliotto 2022** — *Finite-Memory Strategies in POMDPs
with Long-Run Average Objectives*. Mathematics of Operations Research
**47**(1), 100–119. DOI
[`10.1287/moor.2020.1116`](https://doi.org/10.1287/moor.2020.1116),
arXiv:[`1904.13360`](https://arxiv.org/abs/1904.13360). `T` `[primary]`

Theorem 2.9 proves that every finite POMDP has deterministic finite-memory
\(\varepsilon\)-optimal strategies for its long-run average value. Remark 2.1
identifies that value with the asymptotic finite-horizon and uniform values.
Corollary 3.2 makes the promised-gap approximation problem recursively
enumerable but undecidable for general POMDPs, and Remark 3.3 rules out a
computable general memory bound. These general hardness conclusions do not
transfer merely from the value theorem. Q99 now supplies a separate internal
PFA embedding for exact threshold hardness in its product-filter controller
subclass; that embedding does not yet transfer the general no-memory-bound
statement for \(\varepsilon\)-optimal strategies.

**Rote 2025** — *Probabilistic Finite Automaton Emptiness Is Undecidable for a
Fixed Automaton*. 50th International Symposium on Mathematical Foundations of
Computer Science (MFCS 2025), LIPIcs **345**, 86:1--86:18. DOI
[`10.4230/LIPIcs.MFCS.2025.86`](https://doi.org/10.4230/LIPIcs.MFCS.2025.86),
arXiv:[`2412.05198`](https://arxiv.org/abs/2412.05198). `T` `[primary]`

Theorem 1(a) gives undecidability of strict and weak PFA emptiness at cutpoint
\(1/7\) with seven states, four positive doubly-stochastic input matrices,
and one accepting state. Q99's elementary PFA-to-private-controller gadget
therefore yields the audited small upper bound of two players, one public
state, nine opponent-memory states, five deviator actions, and two opponent
actions for strict-threshold hardness. Those game dimensions and the embedding
are repository derivations, not statements in Rote's paper, and are not
minimality claims.

**Chadha, Sistla & Viswanathan 2018** — *Approximating Probabilistic Automata
by Regular Languages*. 27th EACSL Annual Conference on Computer Science Logic
(CSL 2018), LIPIcs **119**, 14:1--14:23. DOI
[`10.4230/LIPIcs.CSL.2018.14`](https://doi.org/10.4230/LIPIcs.CSL.2018.14).
`T` `[primary]`

Section 2 records that strict-cutpoint PFA emptiness is co-r.e.-complete and
that PFA value equality \(\operatorname{val}(A)=x\) is
\(\Pi^0_2\)-complete, even for \(x=1\); the paper attributes the latter
result to the authors' 2013 MFCS paper. This is the primary-source restatement
used in the Q99 audit. Combined with Q99's internal value-preserving embedding
and the direct finite-transducer quantifiers, it calibrates the exact Q99
arithmetic hierarchy; the combination is not itself an external theorem.

**Chadha, Sistla & Viswanathan 2013** — *Probabilistic Automata with Isolated
Cut-Points*. MFCS 2013, Lecture Notes in Computer Science **8087**, 254--265.
DOI
[`10.1007/978-3-642-40313-2_24`](https://doi.org/10.1007/978-3-642-40313-2_24).
`T` `[secondary]`

This is the original source to which the 2018 primary paper attributes
\(\Pi^0_2\)-completeness of PFA value equality. Its theorem role and
bibliographic data were cross-checked through that later paper; the 2013 proof
was not independently re-audited for this repository status update.

**Rosenberg, Solan & Vieille 2003** — *The MaxMin value of stochastic games
with imperfect monitoring*. IJGT **32**(1), 133–150.
DOI [`10.1007/s001820300150`](https://doi.org/10.1007/s001820300150). `—`

**Coulomb 2003** — *Stochastic games without perfect monitoring*. IJGT
**32**(1), 73–96. `—`

**Renault 2011** — *Uniform value in dynamic programming*. JEMS **13**(2),
309–330. DOI [`10.4171/JEMS/254`](https://doi.org/10.4171/JEMS/254),
arXiv:0803.2758. ⚠ Not `/256`. `—`

**Vigeral 2013** — *A Zero-Sum Stochastic Game with Compact Action Sets and no
Asymptotic Value*. Dynamic Games and Applications **3**, 172–186.
DOI [`10.1007/s13235-013-0073-z`](https://doi.org/10.1007/s13235-013-0073-z).
`—`

**Ziliotto 2016** — *Zero-sum repeated games: counterexamples to the existence
of the asymptotic value and the conjecture maxmin = lim v(n)*. Annals of
Probability **44**(2), 1107–1133.
DOI [`10.1214/14-AOP997`](https://doi.org/10.1214/14-AOP997), arXiv:1305.4778.
`—`

**Venel & Ziliotto 2016** — *Strong Uniform Value in Gambling Houses and
POMDPs*. SIAM J. Control Optim. **54**(4), 1983–2008.
DOI [`10.1137/15M1043340`](https://doi.org/10.1137/15M1043340),
arXiv:1505.07495. ⚠ arXiv title differs ("Pathwise uniform value…"). `—`

**Ziliotto 2024** — *Mertens conjectures in absorbing games with incomplete
information*. Annals of Applied Probability **34**(2).
DOI [`10.1214/23-AAP2011`](https://doi.org/10.1214/23-AAP2011),
arXiv:2106.09405. `—`

**Bolte, Gaubert & Vigeral 2015** — limit value under semi-algebraic /
definability conditions. Mathematics of Operations Research **40**, 171–191.
`—` ⚠ Mentioned in verification evidence; not independently fetched.

## Non-zero-sum: existence

**Vrieze & Thuijsman 1989** — *On equilibria in repeated games with absorbing
states*. IJGT **18**(3), 293–310.
DOI [`10.1007/BF01254293`](https://doi.org/10.1007/BF01254293). `—`

**Flesch, Thuijsman & Vrieze 1996** — two-person recursive absorbing games have
stationary ε-equilibria. Mathematics of Operations Research **21**(4),
1016–1022.
DOI [`10.1287/moor.21.4.1016`](https://doi.org/10.1287/moor.21.4.1016). `—`

**Flesch, Thuijsman & Vrieze 1997** — *Cyclic Markov equilibria in stochastic
games*. IJGT **26**(3), 303–314.
DOI [`10.1007/BF01263273`](https://doi.org/10.1007/BF01263273). `—`
Open-access copy: Maastricht institutional repository.

**Solan 1999** — *Three-Player Absorbing Games*. Mathematics of Operations
Research **24**(3), 669–698.
DOI [`10.1287/moor.24.3.669`](https://doi.org/10.1287/moor.24.3.669). `M`

**Solan 1999b** — *Uniform Equilibrium: More Than Two Players*. Author-hosted
lecture chapter (30 July 1999), `math.tau.ac.il/~eilons/natoasi4.pdf`;
published as *Uniform Equilibrium: More than Two Players*, in Neyman & Sorin
(eds.), *Stochastic Games and Applications*, NATO Science Series C **570**
(Kluwer, 2003), DOI
[`10.1007/978-94-010-0189-2_20`](https://doi.org/10.1007/978-94-010-0189-2_20).
`—` States Theorem 2.1 ("Every three-player absorbing game admits a uniform
equilibrium payoff") with a proof sketch, contemporaneous with and by the same
author as Solan 1999 above. See
[`20-nonzero-sum-equilibrium.md`](20-nonzero-sum-equilibrium.md).

**Solan 1998 (dissertation)** — E. Solan's doctoral dissertation, Center for
the Study of Rationality, Hebrew University of Jerusalem, advisor A. Neyman
(PDF `CreationDate` 10 Nov 1998). Local copy:
`ephemeral/old/_source_eilons_thesis.pdf`. `—` Section 4 is, per its own
Acknowledgments, the material refereed by three anonymous MOR referees into
Solan 1999 above. Theorem 4.23 ("Every three-player repeated game with
absorbing states has a perturbed equilibrium payoff") plus Definition 3.9 and
the chapter's own global convention ("whenever we write equilibrium payoff...
we mean the uniform equilibrium payoff") together give, verbatim, the
**uniform** reading unconditionally — the decisive source closing the
undiscounted/uniform gap for the `n = 3` absorbing-game citation. See
[`20-nonzero-sum-equilibrium.md`](20-nonzero-sum-equilibrium.md).

**Vieille 2000a** — *Two-player stochastic games I: A reduction*. Israel J.
Math. **119**, 55–91.
DOI [`10.1007/BF02810663`](https://doi.org/10.1007/BF02810663). `M`

**Vieille 2000b** — *Two-player stochastic games II: The case of recursive
games*. Israel J. Math. **119**, 93–126.
DOI [`10.1007/BF02810664`](https://doi.org/10.1007/BF02810664). `M`

**Vieille 2000c** — *Small perturbations and stochastic games*. Israel J. Math.
**119**, 127–142.
DOI [`10.1007/BF02810665`](https://doi.org/10.1007/BF02810665). `—`
⚠ **Missing from both repo bibliographies.** Supplies auxiliary tools used by
the existence proof.

**Solan 2000** — absorbing team games. GEB **31**, 245–261. `—`
⚠ Page range per the arXiv:2512.04306 PDF; an HTML rendering of that same
bibliography gave GEB 33:85–96, which is wrong.

**Solan & Vieille 2001** — *Quitting Games*. Mathematics of Operations Research
**26**(2), 265–285.
DOI [`10.1287/moor.26.2.265.10549`](https://doi.org/10.1287/moor.26.2.265.10549).
`M` — working-paper version: Northwestern CMS-EMS DP 1227 (1998).

**Solan & Vieille 2002a** — *Quitting Games--An Example*. International
Journal of Game Theory **31**(3), 365--381.
DOI [`10.1007/s001820200125`](https://doi.org/10.1007/s001820200125). `M` —
author-hosted final paper available. This is the citation for the four-player
fallback-collapse/Figure-2 fence; do not attribute that example to the 2001
MOR paper. The repository's audit disputes the printed period-two numerical
packet, so use the source-stable qualitative propositions pending recheck.

**Solan & Vieille 2002b** — *Correlated equilibrium in stochastic games*. GEB
**38**(2), 362–399.
DOI [`10.1006/game.2001.0887`](https://doi.org/10.1006/game.2001.0887).
`M` — working-paper version: Northwestern CMS-EMS DP 1226 (1998). Theorem
2.3 gives every finite multiplayer stochastic game a uniform autonomous
correlated-equilibrium payoff. The device can depend on the requested
accuracy and the general construction uses private current recommendations
and one-stage-delayed disclosure. Fresh contingent tables are independent
across dates. After a detected unilateral deviation, the ordinary coalition-
minmax punishment ignores the continuing device signals; the construction
does not use correlated punishment. Q100 isolates endogenous implementation
of the mediated target; this theorem does not supply an ordinary Nash profile
or reduce the problem to a public coin.

**Solan & Vohra 2002** — normal-form correlated equilibrium in multiplayer
absorbing games. IJGT **31**, 91–121.
DOI [`10.1007/s001820200109`](https://doi.org/10.1007/s001820200109). `—`

**Simon 2007** — *The Structure of Non-Zero-Sum Stochastic Games*. Advances in
Applied Mathematics **38**(1), 1–26.
DOI [`10.1016/j.aam.2006.07.002`](https://doi.org/10.1016/j.aam.2006.07.002). `—`
⚠ **Paywalled, full text not obtained.** ScienceDirect and `core.ac.uk` both
refused automated fetch (HTTP 403); LSE Research Online's record
(`eprints.lse.ac.uk/6897`) states "Full text not available from this
repository"; no author-hosted PDF, arXiv preprint, or green open-access copy
was found. What is recorded in
[`20-nonzero-sum-equilibrium.md`](20-nonzero-sum-equilibrium.md) is an
`[unverified]` search-engine text extraction of the abstract plus `[secondary]`
corroboration from Simon's own later survey — not a primary read. This is the
paper AGKRS's Theorem 3.4 cites as "Simon [13], Theorem 3" (bibliographic
match confirmed primary against `ephemeral/s10107-022-01807-6.pdf`); the
content of that theorem itself is not independently verified.

**Simon 2012** — *A Topological Approach to Quitting Games*. Mathematics of
Operations Research **37**(1), 180–195.
DOI [`10.1287/moor.1110.0524`](https://doi.org/10.1287/moor.1110.0524). `—`
⚠ Conditional result. Simon (2007), entry above, is also cited by
Solan–Vieille 2025.

## Non-zero-sum: post-2020

**Solan & Solan 2018/19** — *Sunspot Equilibrium in General Quitting Games*.
arXiv:1803.00878 (v2, 5 Aug 2019). `—`

**Solan & Solan 2020** — *Quitting Games and Linear Complementarity Problems*.
Mathematics of Operations Research **45**(2), arXiv:1707.02598.
DOI [`10.1287/moor.2019.0996`](https://doi.org/10.1287/moor.2019.0996). `—`

**Munk & Solan 2020** — arXiv:2001.03094. `—`

**Ashkenazi-Golan, Krasikov, Rainer & Solan 2022** — Mathematical Programming.
DOI [`10.1007/s10107-022-01807-6`](https://doi.org/10.1007/s10107-022-01807-6),
arXiv:2012.04369. `—`

**Ashkenazi-Golan, Flesch & Solan** — *Absorbing Blackwell Games*.
arXiv:2208.11425. `—`

**Hansen, Ibsen-Jensen & Neyman 2023** — *The Big Match with a Clock and a Bit
of Memory*. Mathematics of Operations Research **48**(1), 419–432.
DOI [`10.1287/moor.2022.1267`](https://doi.org/10.1287/moor.2022.1267). `—`
⚠ Distinct from *Stochastic games with limited public memory*
(arXiv:2505.02623), which **is** in the manuscript bibliography.

**Flesch & Solan 2023** — *Stochastic games with general payoff functions*.
J. Math. Pures Appl. **179**, 1–42.
DOI [`10.1016/j.matpur.2023.09.002`](https://doi.org/10.1016/j.matpur.2023.09.002).
`M`

**Solan & Vieille 2025** — *Undiscounted Equilibrium in Positive Recursive
Absorbing Games with Non-Rectangular Absorption Structure*. arXiv:2512.04306v1
(3 Dec 2025). `M` ⚠ Unrefereed preprint.

**Solan & Vieille 2025b** — *Public correlated equilibrium in positive
recursive games*. **MIMEO, unpublished.** Do not cite as available. `—`

**Jointly Controlled Lotteries with Biased Coins** — arXiv:1803.00802. `—`
⚠ Author list not independently confirmed; directly relevant to the frontier's
endogenous-lottery item.

## Algorithmic finite-memory equilibrium

**Ummels & Wojtczak 2011** — *The Complexity of Nash Equilibria in
Stochastic Multiplayer Games*. Logical Methods in Computer Science **7**(3),
article 20 (28 September 2011), arXiv:1109.4017.
DOI [`10.2168/LMCS-7(3:20)2011`](https://doi.org/10.2168/LMCS-7%283%3A20%292011).
`—` `[primary]`

The peer-reviewed paper's Theorem 4.14 states that `FinNE` and `PureFinNE`
are undecidable even for 14-player simple stochastic multiplayer games
(SSMGs). Its proof is explicitly labelled **“Proof sketch”**: it reduces from
two-counter-machine halting, adds a clock counter and four monitor players,
and gives the halting/nonhalting memory dichotomy, but does not spell out
every gadget verification. The paper does **not** state the corresponding
`FinSPE` theorem; do not cite it for that strengthening.

**Ummels 2010** — *Stochastic Multiplayer Games: Theory and Algorithms*.
PhD thesis, RWTH Aachen University; Pallas Publications, Amsterdam,
ISBN 978-90-8555-040-2. Authoritative PDF:
[`ummels-phd10.pdf`](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/ummels-phd10.pdf);
RWTH record [`63898`](https://publications.rwth-aachen.de/record/63898).
`—` `[primary]`

The thesis's Theorem 4.13 states that `PureFinNE`, `PureFinSPE`, `FinNE`, and
`FinSPE` are undecidable even for 14-player SSMGs. The displayed proof is
again explicitly a **sketch**. What it does state is exactly the source
dichotomy used by the current Q98 answer: if the encoded two-counter machine
does not halt, every Nash equilibrium in which player 0 wins almost surely
needs infinite memory; if it halts, there is a pure finite-state
subgame-perfect equilibrium in which player 0 wins almost surely. The latter
direction refers back to the arguments for Theorem 4.10 rather than repeating
them. Record the theorem as a primary-source result, but keep the proof-sketch
qualification attached whenever it is used as a reduction premise.

**Ummels & Wojtczak 2009** — *The Complexity of Nash Equilibria in Simple
Stochastic Multiplayer Games*. ICALP 2009, LNCS; arXiv:0902.0101.
DOI [`10.1007/978-3-642-02930-1_25`](https://doi.org/10.1007/978-3-642-02930-1_25).
`—` `[primary]`

This is the shorter precursor. Its finite-state construction is also only
sketched (the text leaves details to the reader) and should not be substituted
for the thesis's explicit `FinSPE` statement.

## Counterexamples and separations

**Sorin 1986** — *Asymptotic properties of a non-zero sum stochastic game*.
IJGT **15**(2), 101–107 (June 1986). Received June 1984, revised February 1985;
Physica-Verlag.
DOI [`10.1007/BF01770978`](https://doi.org/10.1007/BF01770978). `M`
Author-hosted copy at `perso.imj-prg.fr/sylvain-sorin/` (site was refusing
connections 2026-08-02; reachable via a Wayback snapshot).

**Renault & Ziliotto 2020a** — *Limit Equilibrium Payoffs in Stochastic Games*.
Mathematics of Operations Research **45**(3), 889–895.
DOI [`10.1287/moor.2019.1015`](https://doi.org/10.1287/moor.2019.1015).
Author's final manuscript: HAL `hal-04041893`. `—`

**Renault & Ziliotto 2020b** — *Hidden Stochastic Games and Limit Equilibrium
Payoffs*. Games and Economic Behavior 2020,
DOI [`10.1016/j.geb.2020.08.001`](https://doi.org/10.1016/j.geb.2020.08.001),
arXiv:1407.3028. `—`

⚠ Two distinct papers, same authors, same year. Example/lemma numbering differs
between the arXiv preprint and the final manuscript — **cite by content, not by
number**. And their bibliography **mis-cites Sorin** as "IJGT 98:296–303, 1984"
(wrong year, impossible volume, wrong pages); do not propagate it.

## Proof-assistant formalization

**Hölzl & Nipkow 2012** — AFP entry *Markov Models*, submitted 2012-01-03.
`isa-afp.org/entries/Markov_Models.html`. Measure-theoretic MDP semantics and
reachability; **no** reward, discount, average, optimality, or game notions.
Documented in Hölzl, *Markov Chains and Markov Decision Processes in
Isabelle/HOL*, J. Automated Reasoning 2017. `—`

**Schäffeler & Abdulaziz 2021** — AFP entries *Markov Decision Processes with
Rewards* (`MDP-Rewards`) and *Verified Algorithms for Solving Markov Decision
Processes* (`MDP-Algorithms`), both 2021-12-16. Discounted infinite-horizon
optimality plus executable VI/PI/Gauss–Seidel VI/modified PI. Puterman ch. 5–6
only — **not** average reward. `—`

**Le Roux, Martin-Dorel & Smaus 2017** — *An Existence Theorem of Nash
Equilibrium in Coq and Isabelle*. GandALF'17, EPTCS **256**, 46–60,
DOI [`10.4204/EPTCS.256.4`](https://doi.org/10.4204/EPTCS.256.4),
arXiv:1709.02096. Artifacts: `irit.fr/~Erik.Martin-Dorel/equi-thm/`.
`R` (as `LeRouxMartinDorelSmaus2017`, without the arXiv id or artifact URL)

**Le Roux 2014** — *Infinite sequential Nash equilibria*, Math. Log. Q.
**60**(4–5), 354–371,
DOI [`10.1002/malq.201300034`](https://doi.org/10.1002/malq.201300034) — the
paper whose Lemma 2.4 the above mechanizes. `—`

**Chevallier & Fleuriot 2021** — *Formalising the Foundations of Discrete
Reinforcement Learning in Isabelle/HOL*. `—` ⚠ Surfaced by an arXiv API query
during the sweep; not independently fetched.

## Surveys and textbooks

**Solan & Vieille 2015** — *Stochastic games*. PNAS **112**(45), 13743–13746.
`M` — PMC open access.

**Laraki & Sorin** — *Advances in Zero-Sum Dynamic Games*. Handbook of Game
Theory IV, ch. 2. `—` — Liverpool repository copy.

**Thuijsman 2003** — *The Big Match and the Paris Match*. NATO Sci. Ser. C
**570**, Kluwer.
DOI [`10.1007/978-94-010-0189-2_12`](https://doi.org/10.1007/978-94-010-0189-2_12).
`—`

**Solan 2022** — *A Course in Stochastic Game Theory*. Cambridge University
Press. `—` ⚠ Not reached by research; the natural textbook citation for open
status.

**Mertens, Sorin & Zamir 2015** — *Repeated Games*. Cambridge University Press.
`—` ⚠ Not reached by research.

**Jaśkiewicz & Nowak** — survey. `—` ⚠ Not reached by research.

**Maschler, Solan & Zamir 2013** — *Game Theory*. Cambridge University Press.
`R`

---

## Citation traps recorded during verification

1. Bewley–Kohlberg MOR **1**(3):197–208 ≠ MOR **1**(4):321–336.
2. Renault JEMS DOI is `/254`, not `/256`.
3. Vieille 2000 is **three** papers; I alone proves nothing.
4. Vieille is sole author; Solan did not co-author the two-player solution.
5. Venel–Ziliotto was retitled between arXiv and SIAM.
6. Renault's in-text "Mertens and Neyman (1982)" refers to the PNAS
   announcement, not a typo for 1981.
7. Theorem numbers for Renault (Thm 6.2, Cor 3.9, Thm 3.7, Thm 1.5, Cor 1.6,
   Thm 1.10, Prop 1.8) and Venel–Ziliotto (Thm 4) are **arXiv-version
   artifacts**; typeset versions were inaccessible.
8. Hansen–Ibsen-Jensen–Neyman have two distinct relevant papers (MOR 2023
   clock-and-a-bit; arXiv:2505.02623 limited public memory).
9. `MeasureTheory/Integral/RieszMarkovKakutani/` in mathlib is the *Riesz–
   Markov–Kakutani representation theorem*, **not** the Kakutani fixed-point
   theorem.
10. HTML renderings of arXiv bibliographies **hallucinate page numbers**. Use
    `pdftotext`.
11. Renault–Ziliotto 2020 is **two** papers (MOR and GEB), and their Sorin
    citation is wrong (see above).
12. Sorin's `E(∞)` is the **uniform** equilibrium payoff set, not a
    limiting-average one; his paper contains no Cesàro equilibrium concept.
    Sorin discounts with `λ ∈ (0,1]` and the patient limit at `λ → 0`.
