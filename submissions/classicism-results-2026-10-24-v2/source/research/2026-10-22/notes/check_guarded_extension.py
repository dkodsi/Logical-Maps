"""Finite semantic stress check of the new TC proof's guarded extension.

Not a formalization or proof of the theorem. Standard library only.
"""

from itertools import product

n = 3
transport = (0, 0, 1)  # Future point 2 has no root preimage.
subsets = range(1 << n)


def member(mask, x):
    return bool(mask & (1 << x))


def rel(mask, x, y):
    return bool(mask & (1 << (n * x + y)))


def equivalence(mask):
    return (
        all(rel(mask, x, x) for x in range(n))
        and all(rel(mask, x, y) == rel(mask, y, x)
                for x, y in product(range(n), repeat=2))
        and all(not (rel(mask, x, y) and rel(mask, y, z))
                or rel(mask, x, z)
                for x, y, z in product(range(n), repeat=3))
    )


def pointwise_good(root_f, future_f, root_r, future_r):
    for x, y in product(range(n), repeat=2):
        if (member(root_f, x) and member(root_f, y)
                and rel(root_r, x, y) and x != y):
            return False
        hx, hy = transport[x], transport[y]
        if (member(future_f, hx) and member(future_f, hy)
                and rel(future_r, hx, hy) and hx != hy):
            return False
    return True


def guard(f, r, x):
    # q quantifies every individual at its current world, including future 2.
    return all(not (member(f, z) and (rel(r, x, z) or rel(r, z, x)))
               or z == x for z in range(n))


root_relations = [r for r in range(1 << (n * n)) if equivalence(r)]
assert len(root_relations) == 5
checked = 0
for root_r, future_r, root_f, future_f in product(
        root_relations, range(1 << (n * n)), subsets, subsets):
    if not pointwise_good(root_f, future_f, root_r, future_r):
        continue
    for x in range(n):
        if any(rel(root_r, x, y) and member(root_f, y) for y in range(n)):
            continue
        q0 = guard(root_f, root_r, x)
        q1 = guard(future_f, future_r, transport[x])
        g0 = root_f | ((1 << x) if q0 else 0)
        g1 = future_f | ((1 << transport[x]) if q1 else 0)
        assert q0 and g0 != root_f
        assert root_f & ~g0 == 0 and future_f & ~g1 == 0
        assert pointwise_good(g0, g1, root_r, future_r)
        checked += 1

print(f"Passed {checked} guarded extensions; 5 root equivalences, "
      "512 arbitrary future relations, 64 predicate intensions; "
      "future point 2 is new.")
