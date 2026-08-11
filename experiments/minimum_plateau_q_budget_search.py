"""Exact negative control for the Q.md minimum-plateau restrictions.

The displayed four-player reward table has an executable semantic pair with
one unit of debt, the sharp auxiliary-Nash singleton margins, a unique tight
negative debtor, and a literal profitable Never deviation.  It is not claimed
to be minimum in the executable carrier.  The finite scans below test the
auxiliary cube budget on a stated rational grid and screen obvious stationary
solutions.
"""

from fractions import Fraction as F
from functools import reduce
from itertools import product

from semantic_final_regime_search import (
    blank_table,
    coalitions,
    complementary,
    pure_stationary_roots,
    r,
    rational_stationary_roots,
    root_gain,
    set_coordinate,
    singleton_absorption_semantics,
    small_probability_grid,
)


N = 4
OWNER = 0


ROWS = {
    "0": (-1, 2, 2, 2),
    "1": (F(-18, 7), 1, F(6, 7), F(3, 7)),
    "2": (2, F(2, 7), 1, F(-11, 7)),
    "3": (F(19, 7), F(-5, 7), 2, 1),
    "01": (F(-11, 7), -2, F(16, 7), F(2, 7)),
    "02": (F(8, 7), F(1, 7), 1, F(9, 7)),
    "03": (F(5, 7), -2, F(3, 7), F(-6, 7)),
    "12": (F(18, 7), F(6, 7), F(-4, 7), F(11, 7)),
    "13": (F(9, 7), 0, 1, F(-12, 7)),
    "23": (F(-15, 7), -2, 0, F(-9, 7)),
    "012": (F(-15, 7), F(-13, 7), F(3, 7), F(-12, 7)),
    "013": (F(-20, 7), F(3, 7), F(6, 7), F(20, 7)),
    "023": (F(-20, 7), F(-10, 7), F(17, 7), F(-11, 7)),
    "123": (F(-3, 7), F(3, 7), F(-12, 7), F(-2, 7)),
    "0123": (F(-9, 7), F(-5, 7), F(4, 7), F(-4, 7)),
}


def witness_table():
    reward = blank_table()
    for encoded, row in ROWS.items():
        terminal = frozenset(map(int, encoded))
        for who, value in enumerate(row):
            set_coordinate(reward, terminal, who, F(value))
    return reward


def root_masses(quit_rates):
    continue_mass = reduce(lambda a, q: a * (1 - q), quit_rates, F(1))
    opponent_continue = tuple(
        reduce(
            lambda a, other: a * (1 - quit_rates[other]),
            (other for other in range(N) if other != who),
            F(1),
        )
        for who in range(N)
    )
    singleton = tuple(
        quit_rates[who] * opponent_continue[who] for who in range(N)
    )
    collision = 1 - continue_mass - sum(singleton, F(0))
    return opponent_continue, singleton, collision


def cube_grid_audit(reward, envelope, debt_sum):
    """Test every exact root on the displayed rational `(h,q)` grid."""

    rate_grid = small_probability_grid(3)
    shift_grid = (F(0), F(1, 4), F(1, 2), F(3, 4), F(1))
    roots = tuple(product(rate_grid, repeat=N))
    zero_tail = tuple(F(0) for _ in range(N))
    cache = []
    for quit_rates in roots:
        gain_at_zero = tuple(
            root_gain(reward, zero_tail, quit_rates, who) for who in range(N)
        )
        opponent_continue, singleton, collision = root_masses(quit_rates)
        cache.append(
            (quit_rates, gain_at_zero, opponent_continue, singleton, collision)
        )

    exact_root_count = 0
    strict_interior_absorbing_roots = 0
    for shift in product(shift_grid, repeat=N):
        tail = tuple(envelope[who] - shift[who] for who in range(N))
        strict_interior = all(value < debt_sum for value in shift)
        for quit_rates, gain_at_zero, opponent_continue, singleton, collision in cache:
            gains = tuple(
                gain_at_zero[who] - opponent_continue[who] * tail[who]
                for who in range(N)
            )
            if not all(
                complementary(quit_rates[who], gains[who]) for who in range(N)
            ):
                continue
            exact_root_count += 1
            budget = debt_sum * collision + sum(
                singleton[who] * (debt_sum - shift[who])
                for who in range(N)
            )
            assert budget <= 0
            if strict_interior and any(rate > 0 for rate in quit_rates):
                strict_interior_absorbing_roots += 1

    assert strict_interior_absorbing_roots == 0
    return exact_root_count


def stationary_semantics(reward, quit_rates):
    """Exact stationary prescribed payoff and all-behavior envelope."""

    absorption = F(0)
    prescribed = [F(0) for _ in range(N)]
    for action in product((False, True), repeat=N):
        probability = F(1)
        terminal = set()
        for who, quits in enumerate(action):
            probability *= quit_rates[who] if quits else 1 - quit_rates[who]
            if quits:
                terminal.add(who)
        if not terminal:
            continue
        absorption += probability
        for who in range(N):
            prescribed[who] += probability * r(reward, terminal, who)
    assert absorption > 0
    prescribed = tuple(value / absorption for value in prescribed)

    envelope = []
    for who in range(N):
        opponents = tuple(other for other in range(N) if other != who)
        quit_value = F(0)
        waiting_delivery = F(0)
        opponent_continue = F(0)
        for action in product((False, True), repeat=N - 1):
            probability = F(1)
            terminal = set()
            for other, quits in zip(opponents, action):
                probability *= (
                    quit_rates[other] if quits else 1 - quit_rates[other]
                )
                if quits:
                    terminal.add(other)
            quit_value += probability * r(reward, terminal | {who}, who)
            if terminal:
                waiting_delivery += probability * r(reward, terminal, who)
            else:
                opponent_continue = probability
        refusal_value = (
            waiting_delivery / (1 - opponent_continue)
            if opponent_continue < 1
            else F(0)
        )
        envelope.append(max(quit_value, refusal_value))
    return prescribed, tuple(envelope)


def main():
    reward = witness_table()
    prescribed, envelope = singleton_absorption_semantics(reward, OWNER)
    debt = tuple(envelope[who] - prescribed[who] for who in range(N))
    debt_sum = sum(debt, F(0))
    solo = tuple(r(reward, {who}, who) for who in range(N))
    margins = tuple(envelope[who] - solo[who] for who in range(N))
    prescribed_surplus = tuple(
        prescribed[who] - solo[who] for who in range(N)
    )

    # Executable profile: owner 0 quits immediately and everyone else waits.
    assert prescribed == (F(-1), F(2), F(2), F(2))
    assert envelope == (F(0), F(2), F(2), F(2))
    assert debt == (F(1), F(0), F(0), F(0)) and debt_sum == 1

    # Exact Q.md restrictions.
    assert margins == (F(1), F(1), F(1), F(1))
    assert all(margin >= debt_sum for margin in margins)
    assert prescribed[OWNER] == solo[OWNER]
    assert all(prescribed[who] > solo[who] for who in range(1, N))
    assert sum(prescribed_surplus, F(0)) == (N - 1) * debt_sum

    # The owner's pure Never deviation has mass one on Never and improves
    # `-1` to `0`; this is the literal boundary branch of time disintegration.
    never_gain = F(0) - prescribed[OWNER]
    never_mass = F(1)
    assert never_gain == debt[OWNER] == 1 and never_mass == 1

    cube_roots = cube_grid_audit(reward, envelope, debt_sum)

    pure = pure_stationary_roots(reward)
    admissible_pure = [root for root in pure if root["admissible"]]
    assert not admissible_pure

    stationary_counts = []
    for max_denominator in (3, 4, 5):
        stationary = rational_stationary_roots(
            reward, small_probability_grid(max_denominator)
        )
        admissible = [root for root in stationary if root["admissible"]]
        assert not admissible
        stationary_counts.append(
            (max_denominator, len(stationary), len(admissible))
        )

    # Exact disqualification from the minimum fibre.  Put owner hazard
    # `1-e`, opponent hazards `21e,11e,0`, and let `e -> 0+`.  The owner's
    # conditional refusal reward tends to
    #   (21/32)*(-18/7) + (11/32)*2 = -1,
    # while every outsider's prescribed value and refusal value tend to `2`.
    # The exact rational samples expose the resulting zero-debt approach.
    assert F(21, 32) * F(-18, 7) + F(11, 32) * 2 == -1
    escape_debt = []
    for denominator in (256, 512, 1024, 2048):
        epsilon = F(1, denominator)
        rates = (1 - epsilon, 21 * epsilon, 11 * epsilon, F(0))
        escape_prescribed, escape_envelope = stationary_semantics(reward, rates)
        total_debt = sum(
            escape_envelope[who] - escape_prescribed[who]
            for who in range(N)
        )
        escape_debt.append((denominator, total_debt))
    assert all(
        escape_debt[index + 1][1] < escape_debt[index][1]
        for index in range(len(escape_debt) - 1)
    )

    print("Q-COMPATIBLE MINIMUM-PLATEAU NEGATIVE CONTROL")
    print(f"  prescribed={prescribed}")
    print(f"  envelope={envelope}")
    print(f"  debt={debt}; D={debt_sum}")
    print(f"  envelope-minus-solo margins={margins}")
    print(f"  aggregate prescribed surplus={sum(prescribed_surplus, F(0))}")
    print(f"  Never passport: mass={never_mass}, gain={never_gain}")
    print(f"  exact auxiliary roots audited on cube grid={cube_roots}")
    print(f"  admissible pure stationary roots={len(admissible_pure)}")
    for denominator, roots_found, admissible_found in stationary_counts:
        print(
            f"  stationary denominator<={denominator}: "
            f"exact={roots_found}, admissible={admissible_found}"
        )
    print("  exact stationary zero-debt escape:")
    for denominator, total_debt in escape_debt:
        print(f"    epsilon=1/{denominator}: total debt={float(total_debt):.12f}")


if __name__ == "__main__":
    main()
