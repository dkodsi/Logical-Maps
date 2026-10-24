"""Exhaustive output-t check for §7 of world-indexed-choice-gallin.md."""
from itertools import product


def flip(p):
    return ((p & 1) << 1) | ((p & 2) >> 1)


def act_property(prop):
    return tuple(flip(prop[flip(y)]) for y in range(4))


def choose_at_zero(prop):
    return next((y for y in range(4) if prop[y] & 1), 0)


def selector(event, prop):
    if event == 1:
        return choose_at_zero(prop)
    if event == 2:
        return flip(choose_at_zero(act_property(prop)))
    return 0


law_checks = equivariance_checks = 0
for prop in product(range(4), repeat=4):
    for event in range(4):
        chosen = selector(event, prop)
        assert selector(flip(event), act_property(prop)) == flip(chosen)
        equivariance_checks += 1
        if event in (1, 2):
            witnesses = [y for y in range(4) if event & prop[y] == event]
            assert not witnesses or chosen in witnesses
            law_checks += 1

atom_property = (0, 3, 3, 0)
assert act_property(atom_property) == atom_property
event_witnesses = [y for y in range(4) if atom_property[y] == 3]
assert event_witnesses == [1, 2]
assert all(flip(y) != y for y in event_witnesses)
print(f"PASS: {law_checks} atom-law cases; {equivariance_checks} equivariance cases; event obstruction.")
