# Research / formalization ledger

This ledger records proof-engineering decisions that matter mathematically.
It is intentionally stricter than ordinary implementation notes.

## 2026-10-07 — project bootstrap

### Target

Ordinary EPPA for finite partial Steiner triple systems with **closed**
substructures/embeddings.

### Adopted initial architecture

Use the user-supplied PSTS-EPPA formalization advice as a non-authoritative
starting point:

1. certify the transfer `fibre-MAX => PSTS-EPPA` first;
2. only then formalize the corrected ABO I construction through Lemma 2.5;
3. specialize Lemma 2.5 to the Cayley graph / semidirect-product construction;
4. instantiate the transfer.

This is a project decision, not an axiom about the mathematics. If Lean makes a
proposed simplification false or disproportionately awkward, move down the
fallback ladder toward the corrected source formulation.

### Explicit non-goals for Phase I

Do not make ordinary PSTS-EPPA depend on coherent EPPA, ABO II local-tree
strengthenings, Ash/Ribes–Zalesskii/Herwig–Lascar/Otto groupoid black boxes,
quantitative witness bounds, or a general inverse-semigroup library unless the
specialized route genuinely fails.

### Known ABO-I repair obligations

The prose audit supplied with the project records the following repairs. They
must be represented by explicit Lean statements/proofs rather than silently
absorbed into tactics or comments.

- **R1:** Theorem 4.7 uses retractability of `G`; derive/package it explicitly.
- **R2:** Proposition 5.4 has a genuine `k = 1` base-case gap; prove the base
  case separately.
- **R3:** State Condition 5.2 / admissibility only in ranks where defined;
  handle ranks 0 and 1 separately.
- **R4:** Proposition 4.4 needs the omitted two-letter admissibility argument.
- **R5:** Coset-extension transitivity must split off equal/degenerate
  parameters instead of invoking strict nesting there.
- **R6:** Lemma 4.3 has an `A_1`/`A_2` notation typo.
- **R7:** Theorem 4.7(iii) has the analogous `A_1`/`A_2` typo.
- **R8:** Theorem 4.7(iii) must include the full-coset alternative; it is a
  degenerate one-constituent case.

### Transfer-layer hazard already known

Do **not** use the false claim that the total identity partial bijection is the
maximum of the entire restriction order. In the identity fibre, MAX gives
`1 <= w`; totality of `1` then forces `w = 1`.

### Orientation / edge-case checklist

Actively regression-test:

- word-composition convention versus Lean function composition;
- left versus right actions;
- the precise `g h⁻¹` orientation in quotient equality;
- formal inverse letters versus symmetric generating alphabets;
- repeated arguments in the PSTS operation;
- empty closed substructures and empty partial-map domains;
- loops/trivial generators/multiple labels inducing the same permutation;
- empty intersections and equal subset parameters in coset extensions;
- trivial completion adding only loops;
- no use of canonical-map injectivity before it is proved.

### Fallback policy

Preferred path: concrete partial equivalences + fibre-MAX interface + direct
PSTS development. If needed, first formalize ABO Theorem 2.4 more literally;
then introduce only the minimal inverse-monoid interface; then specialize even
harder to the binary PSTS case; finally mirror the audited corrected source
more literally. A nonlocal gap is isolated as a named missing lemma rather than
patched silently.


## 2026-10-07 — Gate T2 accepted

The specialized transfer route has passed Lean and the axiom audit.

### Certified interface

`MaxTransporterExtension A gen` assumes only a finite ambient group, lifts of
the selected generators, and one maximum partial transporter in every
group-value fibre.  No inverse-monoid abstraction and no generation hypothesis
on the ambient group are required by the transfer proof.

### Certified quotient facts

The generated development relation satisfies the exact equality criterion

```text
[a,g] = [b,h]
  iff
∃ w, evalH(w) = g * h⁻¹ ∧ evalPartial(w)(a) = b.
```

The identity fibre is handled by the repaired argument
`refl ≤ eval(maxWord 1)` plus totality of `refl`; no global maximality claim
for the identity is used.

Fibre-MAX proves functionality of the common-chart PSTS operation.  The
canonical base copy is injective and closed, and the exact base operation
formula shows it is an induced copy of the original PSTS.

Right multiplication by the ambient group gives total automorphisms of the
quotient PSTS.  The distinguished lift of every selected generator extends the
corresponding partial automorphism on the base copy.

### Constructive hard gate

`MaxTransporterExtension.selectedEPPAWitness` is the constructive
`MAX => selected-PSTS-EPPA` theorem.  For finite `V` it returns a finite
witness together with the closed embedding and explicit total extensions.
A redundant existential `Nonempty` wrapper was intentionally omitted because
it erased the concrete quotient universe and created a universe metavariable;
the constructive definition is strictly stronger and avoids that artefact.

**Decision:** Gate T2 is accepted.  Begin ABO only now, starting from the
finite oriented-labelled-graph/transition-group layer.

## 2026-10-08 — A2 structural cluster checkpoint

### Lean-certified additions on main

- ABO Proposition 3.3 and retractable subgroup/coset intersections.
- Literal cluster graphs, common-core projection (Lemma 3.11), exact
  subalphabet component-slice dichotomy (Corollary 3.12), and intersection
  formulas (Corollary 3.13).
- Labelled quotient stability and vertex/edge bijectivity of corresponding
  clusters (Lemma 3.10), including injectivity across different constituents.
- Literal augmented clusters, the degenerate full-coset case, cross-piece
  coset-reflection, and vertex/edge bijectivity under stable quotients
  (Lemma 3.14).
- Exact vertex/edge formulas for the attached and disjoint branches of
  Corollary 3.15. These are structural results about ambient C-slices,
  **not yet** the full intrinsic path-component statement.
- General `CayleySubgraphSpec` skeleton API with a genuinely intrinsic
  subalphabet-path relation; each such path lies in its ambient coset.

### Nontrivial mathematical points

The cluster-transport argument cannot infer injectivity on a union merely
from injectivity on every constituent: two points in different constituents
could a priori have the same image. The Lean proof uses target retractability
and subgroup intersections to lift their common image to the intersection
alphabet and then applies stability on both constituents.

Likewise, the augmented-cluster case cannot be proved by naively gluing the
bijective cluster map and the bijective coset map. The mixed overlap is
reflected using the retractable core projection and stability on proper
constituent alphabets; separate stability on the attached B-alphabet then
establishes injectivity on the full union.

The new Lemma-3.14 transport statement is somewhat stronger than the
source-facing hypotheses: target retractability plus the relevant constituent
and attachment stability are sufficient for the bijective labelled graph
morphism. This is verified by Lean, not assumed as a simplification.

The Corollary-3.15 work deliberately keeps the path-component obligation
separate: old C-slice and newly attached coset can be disjoint even when
both lie inside the same ambient C-coset. The disjoint graph-data lemma proves
that there are no crossing C-labelled edges, but path-connectedness of each
piece still needs an explicit skeleton-path argument before declaring the
full corollary proved in Lean.

### Next substantive A2 gate

Use the generic Cayley-skeleton E-graph to formalize intrinsic C-components,
then admissibility exactly as in ABO Definition 3.16. The gluing relations for
coset extensions (3.6)–(3.12), Proposition 3.18, and the equal-parameter
transitivity repair R5 are **not formalized yet**. A3 (corrected Theorem 4.7)
and the finite ABO construction are also still open.
