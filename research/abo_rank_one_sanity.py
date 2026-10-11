#!/usr/bin/env python3
"""Independent finite sanity check of genuine rank-one ABO cover shapes.

No external packages. Run:
  python3 research/abo_rank_one_sanity.py

Enumerates all 4^4 ordered endpoint patterns for two distinct original
positive edge labels e/f on a fixed four-vertex carrier. This includes
loops, oppositely oriented parallel edges and disconnected pairs.
Each letter acts in the source H1 group as its transposition together
with its independent unary detector bit (zero for a loop).

Crucially, true e/f edges are pulled back from the ORIGINAL graph,
and each unary coset in the completed CE is attached to a component
of that old incomplete graph, NOT to vertices newly attached by
the other label. Distinct component tags are never identified merely
because their ambient group values happen to be equal.

This is a computational regression test, not a proof for arbitrary E.
"""
from collections import Counter, defaultdict, deque
from itertools import product
from math import lcm

N = 4
IDENT = tuple(range(N))


def transposition(a, b):
    p = list(IDENT)
    p[a], p[b] = p[b], p[a]
    return tuple(p)


def right_move(g, t, bit, which):
    p, bits = g
    return (tuple(t[x] for x in p), bits ^ (bit << which))


def local_h1(edge_e, edge_f):
    ts = [transposition(*edge_e), transposition(*edge_f)]
    bits = [int(edge_e[0] != edge_e[1]), int(edge_f[0] != edge_f[1])]
    gen = {
        "e": lambda g: right_move(g, ts[0], bits[0], 0),
        "f": lambda g: right_move(g, ts[1], bits[1], 1),
    }
    q = deque([(IDENT, 0)])
    seen = {(IDENT, 0)}
    while q:
        x = q.popleft()
        for fn in gen.values():
            y = fn(x)
            if y not in seen:
                seen.add(y)
                q.append(y)
    return sorted(seen), gen


def components(vertices, edges):
    adj = {x: set() for x in vertices}
    for x, y in edges:
        assert x in adj and y in adj
        adj[x].add(y)
        adj[y].add(x)
    seen = set()
    result = []
    for v in vertices:
        if v in seen:
            continue
        part = {v}
        q = [v]
        for x in q:
            for y in adj[x]:
                if y not in part:
                    part.add(y)
                    q.append(y)
        seen.update(part)
        result.append(frozenset(part))
    return result


def source_covers(group, gen, ee, ff):
    endpoints = set(ee + ff)
    source_components = components(sorted(endpoints), [ee, ff])
    result = []
    for base in endpoints:
        image = {h: h[0][base] for h in group}
        inside = {h for h in group if image[h] in endpoints}
        edges = []
        for edge, label in [(ee, "e"), (ff, "f")]:
            a, b = edge
            for h in inside:
                if image[h] != a:
                    continue
                z = gen[label](h)
                assert z in inside and image[z] == b
                edges.append((h, z, label))
        for base_comp in source_components:
            verts = [h for h in inside if image[h] in base_comp]
            for comp in components(
                verts, [(x, y) for x, y, _ in edges if x in verts and y in verts]
            ):
                if comp:
                    result.append((comp, [
                        (x, y, t) for x, y, t in edges if x in comp and y in comp
                    ]))
    return result


def complete_full_ce(old_vertices, old_edges, gen):
    old = {("old", x): x for x in old_vertices}
    original = set(old)
    vertices = set(original)
    edges_by_letter = defaultdict(list)
    for x, y, label in old_edges:
        edges_by_letter[label].append((("old", x), ("old", y)))
    stage_edges = set()
    for letter in ("e", "f"):
        # IMPORTANT: these are components of the OLD skeleton only.
        for idx, comp in enumerate(components(original, edges_by_letter[letter])):
            assert len(comp) <= 2
            representative = old[next(iter(comp))]
            full_coset = {representative, gen[letter](representative)}
            old_values = {old[z] for z in comp}
            assert old_values <= full_coset
            added = []
            for value in full_coset - old_values:
                fresh = ("fresh", letter, idx, value)
                vertices.add(fresh)
                old[fresh] = value
                added.append(fresh)
            fibre = sorted(list(comp) + added, key=str)
            assert len(fibre) == len(full_coset)
            stage_edges.add((letter, fibre[0], fibre[-1]))
    # Trivial completion: missing signed letters become loops.
    for letter in ("e", "f"):
        occupied = set()
        for t, a, b in stage_edges:
            if t == letter:
                occupied.update((a, b))
        for z in vertices - occupied:
            stage_edges.add((letter, z, z))
    return vertices, stage_edges, old


def complete_action(vertices, edges):
    action = {letter: {} for letter in ("e", "f")}
    for letter, a, b in edges:
        assert a not in action[letter] and b not in action[letter]
        action[letter][a] = b
        action[letter][b] = a
    assert all(set(d) == set(vertices) for d in action.values())
    return action


def augment(vertices, edges, group_value, gen, letter, root):
    assert (letter, root, root) in edges
    if gen[letter](group_value[root]) == group_value[root]:
        return vertices, edges
    fresh = ("augmentation", letter, root, gen[letter](group_value[root]))
    assert fresh not in vertices
    new_vertices = set(vertices) | {fresh}
    new_edges = set(edges)
    new_edges.remove((letter, root, root))
    new_edges.add((letter, root, fresh))
    other = "f" if letter == "e" else "e"
    new_edges.add((other, fresh, fresh))
    complete_action(new_vertices, new_edges)
    return new_vertices, new_edges


def word_order(vertices, edges, word="ef"):
    rho = complete_action(vertices, edges)
    order = 1
    for start in vertices:
        x = start
        for count in range(1, 300):
            for letter in word:
                x = rho[letter][x]
            if x == start:
                order = lcm(order, count)
                break
        else:
            raise AssertionError("Unexpected long cycle")
    return order


def one_pattern(ee, ff):
    group, gen = local_h1(ee, ff)
    covers = source_covers(group, gen, ee, ff)
    old_max = plain_max = augmented_max = 0
    witness = []
    for comp, original_edges in covers:
        old_max = max(old_max, len(comp))
        V, E, group_value = complete_full_ce(comp, original_edges, gen)
        plain_max = max(plain_max, len(V))
        augmented_max = max(augmented_max, len(V))
        for letter in ("e", "f"):
            for root in V:
                if (letter, root, root) in E and gen[letter](group_value[root]) != group_value[root]:
                    W, F = augment(V, E, group_value, gen, letter, root)
                    augmented_max = max(augmented_max, len(W))
                    if len(V) == 4 and len(W) == 5 and word_order(V, E) == 4 and word_order(W, F) == 5:
                        witness.append((len(V), len(W), 4, 5))
    return (len(group), len(covers), old_max, plain_max, augmented_max), witness


def main():
    patterns = []
    witnesses = []
    for ee in product(range(N), repeat=2):
        for ff in product(range(N), repeat=2):
            stats, witness = one_pattern(ee, ff)
            patterns.append((ee, ff, stats))
            if set(ee).isdisjoint(ff):
                witnesses.extend(witness)
    maxima = [max(stats[i] for _, _, stats in patterns) for i in range(5)]
    hist = Counter(stats[2:] for _, _, stats in patterns)
    print("Original ordered edge-pair patterns:", len(patterns))
    print("Max |H1[e,f]|, rooted covers, old component, plain CE, augmented CE:", maxima)
    print("Histogram (old component, plain CE, augmented CE):")
    for k, v in sorted(hist.items()):
        print(" ", k, ":", v)
    assert len(patterns) == 256
    assert maxima == [12, 12, 4, 5, 6]
    assert witnesses and set(witnesses) == {(4, 5, 4, 5)}
    print("Nonredundancy witness (plain size, augmented size, ord(ef) plain, augmented):", witnesses[0])
    print("PASS")


if __name__ == "__main__":
    main()
