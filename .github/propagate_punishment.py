from pathlib import Path

root = Path('.')

# FRONTIER
p = root/'docs/uniform-equilibrium/FRONTIER.md'
s = p.read_text()
old = '''The trichotomy's **isolated-negative compiler hole is closed**.  The passive
periodic profile was the wrong object: it implicitly assigns continuation value
`0` when the isolated player refuses to quit.  `QuittingInstantPunishment.lean`
proves the exact replacement for a sure first-stage quitter,

```text
quittingPunishmentValue reward i ≤ r_i({i})
```

together with the outsider no-join inequalities.  The continuation may be a
near-optimal constant punishment row because
`quittingPunishmentValue_eq_stationaryPunishmentValue` identifies the full
behavioral min-max with the infimum of stationary stopping caps.
`QuittingPunishmentCompletedCycle.lean` then extends this to every exact
absorbing cycle: each coordinate must either have deleted survival product
below one, or have punishment value at most its singleton payoff.  Absorption
allows at most one noncontracting coordinate; a long cyclic prefix followed by
its punishment gives terminal approximate equilibria converging to the named
cycle value.  The older nonnegative-solo admissibility predicate is a strict
special case.

One cycle-carrier hole remains.  The trichotomy is exhaustive only under the
hypothesis that the weight admits an absorbing complementary cycle **at all**.
Weights admitting none of any period are outside it entirely. **This hole is
occupied, and the occupancy is machine-checked end to end (`L`)**: for every
`ε ∈ (0, 2]`, `¬∃ terminal, IsQuittingCyclicContinuation (ftvRewardEps ε)
terminal` — the trichotomy's own predicate — via the label lock in the real
encoding (all periods, with the `ε = 0` rotation as the in-file boundary
witness) and the cycle-level transport with entry-for-entry weight alignment
(`PerturbedCyclicWeightNoExactCycle.lean`,
`PerturbedCyclicWeightCycleExistenceHoleOccupied.lean`). The leading hard
candidate provably lies *outside the trichotomy*; the cycle route's
incompleteness is an internal theorem, and the published Theorem 2.1 is
independent confirmation only.
'''
new = '''The isolated-negative compiler now has an **exact punishment
discriminator (`M+L`)**.  The passive periodic profile was the wrong object: it
implicitly assigns continuation value `0` when the isolated player refuses to
quit.  `QuittingInstantPunishment.lean` proves that a sure first-stage quitter
`i` can instead be enforced exactly when

```text
quittingPunishmentValue reward i ≤ r_i({i})
```

and every outsider weakly prefers not to join the exit.  The continuation may
be a near-optimal constant punishment row because
`quittingPunishmentValue_eq_stationaryPunishmentValue` identifies the full
behavioral min-max with the infimum of stationary stopping caps.
`QuittingPunishmentCompletedCycle.lean` extends the same correction to an exact
absorbing cycle: every coordinate must either have deleted survival product
below one, or satisfy the displayed punishment inequality.  Absorption allows
at most one noncontracting coordinate; a long cyclic prefix followed by its
punishment gives terminal approximate equilibria converging to the named cycle
value.  The older nonnegative-solo admissibility predicate is a strict special
case.

This splits rather than erases the isolated-negative branch.  If the isolated
coordinate has punishment value at most its negative singleton payoff, the
named cycle value is now compiled.  If its punishment value is strictly larger,
that named value violates individual rationality and the exact instant theorem
rules out this sure-quitter enforcement shape; a different equilibrium carrier
or a counterexample is still needed.

The cycle route therefore retains two distinct holes.  First, its trichotomy is
exhaustive only under the hypothesis that the weight admits an absorbing
complementary cycle **at all**.  Weights admitting none of any period are
outside it entirely. **This hole is occupied, and the occupancy is
machine-checked end to end (`L`)**: for every `ε ∈ (0, 2]`,
`¬∃ terminal, IsQuittingCyclicContinuation (ftvRewardEps ε) terminal` — the
trichotomy's own predicate — via the label lock in the real encoding (all
periods, with the `ε = 0` rotation as the in-file boundary witness) and the
cycle-level transport with entry-for-entry weight alignment
(`PerturbedCyclicWeightNoExactCycle.lean`,
`PerturbedCyclicWeightCycleExistenceHoleOccupied.lean`). The leading hard
candidate provably lies *outside the trichotomy*; the cycle route's
incompleteness is an internal theorem, and the published Theorem 2.1 is
independent confirmation only.  Second, an existing isolated-negative cycle
whose isolated coordinate fails the punishment inequality is not compiled by
this theorem.
'''
assert old in s
s = s.replace(old,new,1)
old = '''3. **`S₊ ≠ ∅`, `S₋ ≠ ∅`** — a second failure mode. An absorbing discounted
   limit that isolates a coordinate of `S₋` is necessarily the solo row `p·e_i`
   with value `r_i({i}) < 0`: a genuine absorbing cycle that is not admissible.
   The dichotomy then supplies nothing even though absorption did not
   degenerate, and one must argue about the whole supply of cycles rather than
   the selected limit.

Cases 2 and 3 are the remaining content. See
'''
new = '''3. **`S₊ ≠ ∅`, `S₋ ≠ ∅`** — an absorbing discounted limit may isolate a
   coordinate `i ∈ S₋`, necessarily on the solo row `p·e_i` with value
   `r_i({i}) < 0`.  Punishment completion settles exactly the subbranch
   `quittingPunishmentValue reward i ≤ r_i({i})`.  In the strict reverse
   inequality the named cyclic value is not individually rational and the
   instant mechanism is impossible; another cycle/profile or a genuine
   nonexistence argument is required.

Cases 2 and the unpunishable part of 3 are the remaining content. See
'''
assert old in s
s=s.replace(old,new,1)
old = '''Instant profiles
and the unique isolated coordinate of an absorbing cycle now feed explicit
all-errors families into target-identified terminal selection.  Still open are
'''
new = '''Instant profiles and the unique isolated coordinate of an absorbing
cycle now feed explicit all-errors families into target-identified terminal
selection whenever the punishment value lies below the prescribed singleton
payoff.  Still open are the strict reverse-inequality branch,
'''
assert old in s
s=s.replace(old,new,1)
s=s.replace(
    'this model at horizon one. What remains of the general folk bill is narrower.  Single-player\n'
    'punishment attainment is settled in the form actually needed here: every\n',
    'this model at horizon one. What remains of the general folk bill is narrower.\n'
    'Single-player punishment attainment is settled in the form actually needed\n'
    'here: every\n',
    1,
)
p.write_text(s)

# TOOLKIT caveat
p = root/'docs/uniform-equilibrium/TOOLKIT.md'
s=p.read_text()
old='''| Punishment-completed finite cycle | An exact absorbing cyclic continuation block such that every coordinate either has contracting deleted survival or has punishment value at most its singleton payoff | Accuracy-indexed terminal equilibria converging to the named cycle value, hence that value is a uniform-equilibrium payoff | Does not produce an exact cycle; weights with no exact complementary cycle remain outside this carrier. |'''
new='''| Punishment-completed finite cycle | An exact absorbing cyclic continuation block such that every coordinate either has contracting deleted survival or has punishment value at most its singleton payoff | Accuracy-indexed terminal equilibria converging to the named cycle value, hence that value is a uniform-equilibrium payoff | Does not produce an exact cycle and does not cover an isolated-negative coordinate whose punishment value exceeds its singleton payoff; that named cycle value fails individual rationality. |'''
assert old in s
p.write_text(s.replace(old,new,1))

# PIPELINE
p=root/'docs/uniform-equilibrium/PIPELINE.md'
s=p.read_text()
s=s.replace('''target-anchored closure, face-circulation compilation, uniform-payoff
diagnostics, adaptive essential-APS meshes, and the boundary-holonomy tangent
layer are incorporated and reflected below.''','''target-anchored closure, face-circulation compilation, uniform-payoff
diagnostics, adaptive essential-APS meshes, boundary-holonomy tangent
coordinates, and punishment-completed instant/cyclic profiles are incorporated
and reflected below.''',1)
anchor='''- **Support witnesses (`a4f23756`, conditional compiler).**  Retaining the
  support-local endpoint witness collapses the ledger clock deterministically.
  Divergent support-rational paths compile with error
  `2 delta + r + sqrt(delta) (2 + 7 M)`; finite cycles with one absorbing phase
  adapt to the same compiler.  Existence of such paths/cycles at every
  tolerance remains the producer obligation.  The abstract rank-one crossing
  theorem is retained separately and supplies no game-specific process or
  variation bound.
'''
addition='''- **Instant and punishment-completed cycles (this branch, conditional
  compiler).**  Coupled phase switching preserves a shared negative continuation
  anchor.  A sure solo quitter is enforceable iff its singleton payoff dominates
  its exact behavioral punishment value and outsiders do not gain by joining.
  An exact absorbing cycle compiles its named phase value whenever each
  coordinate either contracts in deleted survival or satisfies the same
  punishment inequality.  This resolves the instant-profile audit and the
  punishable isolated-negative subbranch, but not weights with no exact cycle or
  an isolated coordinate whose punishment value exceeds its singleton payoff.
'''
assert anchor in s
s=s.replace(anchor,anchor+addition,1)
# Status index removals/additions
s=s.replace('- `MATH-P0-7` — a sufficiency theorem for the isolated-negative branch\n','',1)
s=s.replace('- `MATH-P1-5` — audit the decomposition for instant approximate equilibria\n','',1)
partial_anchor='''**PARTIAL / BLOCKED / PENDING / ANSWERED IN PART**
'''
assert partial_anchor in s
s=s.replace(partial_anchor,partial_anchor+'- `MATH-P0-7` — punishment-completed isolated-negative branch (`ANSWERED IN PART`)\n',1)
done_anchor='''**DONE / SOLVED / RESOLVED**
'''
assert done_anchor in s
s=s.replace(done_anchor,done_anchor+'- `MATH-P1-5` — instant approximate equilibria characterized exactly — see\n  [archive](PIPELINE-Archive.md)\n',1)
# Remove detailed MATH-P1-5 section
start=s.index('### `MATH-P1-5` — audit the decomposition for instant approximate equilibria')
end=s.index('### `LEAN-P0-7` — two-clock punishment for the deviation-cap constructor',start)
s=s[:start]+s[end:]
# Replace detailed MATH-P0-7 section
start=s.index('### `MATH-P0-7` — a sufficiency theorem for the isolated-negative branch')
end=s.index('### `MATH-P0-8` — the relaxed compiler: formalize Proposition 3',start)
replacement='''### `MATH-P0-7` — a sufficiency theorem for the isolated-negative branch

- **Status:** ANSWERED IN PART
- **Lane:** P0
- **Depends:** the trichotomy; `QuittingStationaryMinMax`;
  `QuittingInstantPunishment`; `QuittingPunishmentCompletedCycle`.
- **Record:** [exact-vs-relaxed]

**Objective.** Show that a weight in the isolated-negative branch has a uniform
equilibrium payoff, or exhibit one that does not.

**State.** `ANSWERED IN PART`, 2026-08-07.  The branch now has an exact
compiler discriminator.  For an isolated coordinate `i`, the passive periodic
mismatch `[-r_i({i})]₊` is replaced by an off-path punishment.  If

```text
quittingPunishmentValue reward i ≤ r_i({i}),
```

then a near-optimal constant punishment row, attached after a long cyclic
prefix, gives terminal approximate equilibria converging to the named cyclic
value; that value is therefore a uniform-equilibrium payoff.  The instant
period-one shape is characterized iff by the same punishment inequality plus
the outsider no-join inequalities.  The old nonnegative-solo admissibility
compiler is recovered as a corollary.

The strict reverse inequality remains.  There the named isolated cyclic value
fails individual rationality, and the instant characterization proves that no
sure-first-stage-quitter punishment can implement it.  This does not refute
uniform equilibrium existence: another cycle, another target, or a genuinely
nonperiodic profile may still work.

**Acceptance.** Resolve the residual `quittingPunishmentValue reward i >
r_i({i})` subbranch by producing another equilibrium carrier, proving it cannot
occur in the relevant selected cycle, or certifying a positive all-behavior
exploitability gap.  The punishment-completed theorem is the complete answer
for the complementary subbranch.

'''
s=s[:start]+replacement+s[end:]
s=s.replace(
    'The resulting priority delta is precise: test density of the positively solved\n'
    'payoff-table strata first; independently seek a support-rational path/cycle\n'
    'producer; and, on the APS lane, determine when an arbitrary game supplies a\n'
    'nonempty compact terminal-free unique-live component with the required face\n'
    'avoidance. None of these conditional compilers receives generic existence\n'
    'credit before its producer is proved.\n',
    'The resulting priority delta is precise: isolate the strict\n'
    '`quittingPunishmentValue > singleton` residue inside the isolated-negative\n'
    'branch; test density of the positively solved payoff-table strata; independently\n'
    'seek a support-rational path/cycle producer; and, on the APS lane, determine\n'
    'when an arbitrary game supplies a nonempty compact terminal-free unique-live\n'
    'component with the required face avoidance. None of these conditional compilers\n'
    'receives generic existence credit before its producer is proved.\n',
    1,
)
s=s.replace(
    '- `MATH-P0-7` — punishment-completed isolated-negative branch (`ANSWERED IN PART`)\n',
    '- `MATH-P0-7` — punishment-completed isolated-negative branch (`ANSWERED IN\n'
    '  PART`)\n',
    1,
)
p.write_text(s)

# ARCHIVE: add MATH-P1-5 under conjecture-closing mathematics after MATH-P0-6
p=root/'docs/uniform-equilibrium/PIPELINE-Archive.md'
s=p.read_text()
insert_at=s.index('### `MATH-P0-11` — the minimal open family: the four-player cyclic phase diagram')
entry='''### `MATH-P1-5` — audit the decomposition for instant approximate equilibria

- **Status:** DONE (2026-08-07)
- **Lane:** P1
- **Depends:** the stationary repair ladder; the absorbing-cycle carrier; the
  positive-plateau split; `QuittingStationaryMinMax`.
- **Record:** [`program-bearings.md`](../../ephemeral/Simon2007/program-bearings.md) §3

**Objective.** Decide where Simon's third equilibrium family lands in this
program's splits, or record that it does not.

**State.** `DONE`.  The family was genuinely absent from the old stationary and
periodic grammars, but no new general behavior datatype was needed.  In a
quitting game, unexpected survival after a sure stage-zero exit is the public
trigger; `quittingOneStagePunishedProfile` already represents it.
`QuittingCoupledPhaseSwitchCap.lean` supplies the missing algebra by retaining
the survival coefficient on a shared continuation anchor instead of first
replacing the tail by passive value `0`.

`QuittingInstantPunishment.lean` gives the exact characterization.  A sure solo
quitter `i` admits terminal approximate equilibria at every accuracy iff its
singleton payoff dominates `quittingPunishmentValue reward i` and every
outsider weakly prefers not to join.  The punishment value is the full
behavioral min-max but equals the infimum of constant-row stopping caps, so a
stationary near-minimizer supplies every requested error.  The resulting
singleton terminal vector is a named uniform-equilibrium payoff.

**Acceptance.** Fulfilled: the instant family is named, represented, proved
sufficient and necessary, connected to the exact punishment value, and fed
through fixed-target terminal-to-uniform selection.

'''
s=s[:insert_at]+entry+s[insert_at:]
p.write_text(s)

print('updated docs')
