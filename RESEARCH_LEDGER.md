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

## 2026-10-08 — continued A2 checkpoint (post R4)

- Intrinsic subalphabet reachability for arbitrary incomplete Cayley skeletons
  is now formally an equivalence relation. Actual paths are inverted using
  formal reverse-edge tokens; this is not ambient-coset connectivity by fiat.
- The quotient of skeleton vertices by intrinsic B-reachability gives an
  index for the separately attached B-coset copies. The ambient coset
  attached to an index is shown independent of its representative. A skeleton
  vertex embeds injectively into its uniquely tagged component copy even if
  two distinct indices map to the same group coset.
- ABO Definition 3.16 is certified in its logically equivalent overlap
  reflection form, with proper B₁,B₂ ⊂ B ⊂ A (allowing B₁=B₂ and the empty
  subalphabet). The original disjointness consequence is proved explicitly.
- Repair R4 (only its admissibility claim): in cardinality at most two,
  proper B₁,B₂ necessarily are empty. The corresponding group cosets are
  singletons, so overlap forces equality of base vertices and intrinsic
  intersection. This has a complete Lean proof independent of retractability
  and skeleton connectedness.

**Remaining:** ABO Proposition 4.4 also claims the *cluster property*, not
proved by the rank-two admissibility theorem. Actual CE(G,K;B) graph, gluing
quotient for families of alphabets, Proposition 3.18, and repair R5 are
unformalized. Structural graph-data versions of Corollary 3.15 are certified,
but the bridge to intrinsic connected components still needs a dedicated proof.

**Construction engineering lead (not yet certified):** identify vertices of a
single B-coset extension with the disjoint union of ambient B-cosets tagged
by intrinsic skeleton B-component; every original skeleton vertex already
embeds into exactly one such copy. Extend edge tokens by retaining all
original non-B edges while supplying each tagged B-coset with its complete
B-labelled Cayley edges. This may avoid a separate vertex gluing quotient for
single-B extensions; it must be checked in Lean, and the multi-alphabet
quotient still requires the equal/degenerate-parameter transitivity repair.

## 2026-10-08 — A2 coset-extension and gluing checkpoint (late)

### Lean-certified and merged

- Single-B coset extension is a literal deterministic labelled E-graph:
  old signed edges outside B are retained; complete signed B-edges are
  added separately to each intrinsic B-component; formal inverse tokens
  remain distinct even for geometric loops and trivial generators.
- The original skeleton has a vertex- and edge-injective labelled
  embedding into the single-B extension. Every added B-copy is genuinely
  B-path connected, every B-path preserves its component tag, and
  therefore the intrinsic B-components of the extension are exactly the
  attached B-coset copies. Original B-connectivity is reflected.
- For multi-alphabet gluing, the exact overlap relation is witnessed by
  a tagged (B ∩ C)-coset point, not equality of ambient group coordinates.
  Under admissibility and retractability it is an actual equivalence
  relation; the transitivity proof handles equal, nested and empty
  alphabets explicitly (repair R5, **vertex level**).
- The quotient of raw tagged vertices is constructed, and each individual
  alphabet-summand embeds injectively. Original skeleton vertices have
  an alphabet-independent image. Glued original skeleton points also
  reflect correctly into the individual attached B-summands.
- Raw directed edge tokens, their signed labels, sources/targets,
  projection to the ambient Cayley graph, inverse tokens and reversal
  laws are formalized. The separate edge-token quotient by equal glued
  source and signed label has well-defined source and label and injective
  injections of constituent edge sets. The ambient projection is deliberately
  not treated as globally injective.

### Exact remaining edge gluing gate

Define `MultiCosetTargetCongruent`: whenever two raw directed edges have
**equal sources in the quotient of vertices** and the same signed label,
their **targets are equal in that same quotient**. Equal ambient group
coordinates alone are insufficient. This has three constituent cases:

1. Both edges completed in attached cosets: move the common
   (B ∩ C)-support witness by the shared signed generator.
2. Both edges originally in K: use source projection and determinism of
   the old skeleton, followed by alphabet-independent skeleton inclusion.
3. Exactly one edge completed: use literal skeleton-point reflection to
   identify the completed source and the old skeleton edge, then compare
   their targets.

These case lemmas and a separate conditional construction of the full
multi-coset E-graph are in review; only a successful full Lean build and
axiom audit on merged `main` may promote them to formalized. Until
`MultiCosetTargetCongruent` is proved, the edge quotient is not a
LabelledGraph or EGraph. This distinction is intentional.

### Further obligations and boundary

- Actual multi-alphabet edge gluing and Proposition 3.18, including
  compatibility with formal inversion and an injective skeleton embedding;
- the intrinsic path-component formulation of Corollary 3.15 (current
  results cover exact graph-data slices, not yet all connected components);
- the cluster property of low-rank Proposition 4.4 (admissibility alone
  was certified earlier, not the entire proposition);
- Section 3 coset-extension preservation lemmas, corrected Theorem 4.7,
  finite induction and the eventual unconditional PSTS EPPA theorem.

No claim that ordinary PSTS EPPA is Lean-formalized follows from this
checkpoint: the T2 transfer remains conditional on the fibre-MAX group
extension and A3/A4/A5/C1 remain open.

## 2026-10-08 — A2 edge quotient E-graph certified

### Mathematically substantial Lean-certified results

The proof of target congruence for multi-alphabet coset-extension edge
identifications is now merged into main (PR #74, commit
`4ea8b05cab6a2dfab4a548bf2a39aba7c0900924`). It treats all four
ordered combinations of original outside-alphabet and completed coset
edges. The completed/completed case moves a real (B ∩ C)-support witness
by the common signed generator. The old/old case uses determinism of
the original skeleton. The mixed case uses literal skeleton-point
reflection rather than falsely assuming injectivity of the ambient
group projection. The symmetric mixed orientation follows by reversal
of equality. All three constituent proofs were independently CI-green.

As a result, the previously conditional multi-coset edge construction
is an actual deterministic E-graph, not just an incidence quotient:
formal reversal descends to classes, has order two and no fixed edge
tokens, and reverses signed labels, even for geometric loops and
trivial or repeated generators. Each single-B constituent maps in
with injective vertex and directed-edge maps. The assumptions remain
those of the source construction: admissible skeleton and retractable,
generated labelled group. This is **not** a final PSTS EPPA witness.

### Remaining tasks

The candidate `MultiCosetMorphisms.lean` on PR #76 constructs the
canonical morphism into the ambient Cayley graph and injective,
alphabet-independent skeleton embeddings. It is **not yet accepted**
until the combined Lean CI and axiom audit pass and it is merged.

Source-facing ABO Proposition 3.18 and all later Section 3 preservation
properties still require exact statement-level audit. In particular,
full intrinsic C-component classification (rather than only exact
vertex/edge slices) for Corollary 3.15 and the rank-two cluster
property of Proposition 4.4 remain separate obligations. The corrected
Theorem 4.7 (A3), Section 5 induction, main ABO Lemma 2.5,
Cayley/semidirect fibre-MAX bridge, and unconditional PSTS EPPA are open.

**Scope discipline:** 'unconditional multi-coset EGraph' means no *extra*
unknown edge-congruence hypothesis is left in the Lean statement; it
still takes admissibility, retractability and generation as explicit
hypotheses and does not prove the overarching theorem.

## 2026-10-08 — A2 structural components and local embeddings checkpoint

This checkpoint **supersedes the outdated 'PR #76 pending' note above**.

### Fully checked and merged to main

- PR #76 canonical multi-coset labelled Cayley morphism and skeleton embedding;
  PR #79 uniqueness of that morphism from its skeleton restriction, for
  nonempty alphabet families only. The map into Cayley need not be injective
  globally.
- PR #78 actual intrinsic B/C-component intersection theorem in an
  admissible retractable A-skeleton: any nonempty intersection is exactly
  an intrinsic (B∩C)-component. In the nested/equal-alphabet case the
  strictness requirement is handled separately.
- PR #80 admissibility witnesses remain inside a chosen B-component;
  PR #81 constructs that component as a literal Cayley subgraph; PR #95
  transports realised paths and proves the lower component skeleton
  admissible; PR #97 proves it is actually B-path-connected. A historical
  stacked PR #89 was *not* merged to main: its checked proof was
  explicitly forward-ported with PR #95.
- PR #101 identifies intrinsic D⊆B reachability inside the component
  with inherited reachability in the parent K, and proves injections
  of D-component indices and tagged attached D-cosets.
- PR #85 locally reflects ambient overlaps within a fixed parent
  B-component, avoiding the false claim of global injectivity;
  PR #88 injectively folds lower-family vertices into B-copies;
  PR #92 shows vertex-injective E-graph morphisms inject signed edges;
  PR #98 gives injective single-C→single-B E-graph morphisms;
  PR #99 extends this to the entire lower family and proves
  vertex/edge surjectivity when B itself belongs to the family.
  Historical stacked #93 was green but not in main; #98 ported it.
- PR #102 uses actual B-connectivity to show that the full B-coset
  extension of one intrinsic B-component embeds into the ambient
  Cayley graph. Its vertex image is the actual left coset root·G[B].
- PR #91 weak completeness under original edge-label coverage;
  PR #100 defines the canonical proper-alphabet family P_A and
  discharges coverage for |A|≥2. This is strictly weaker than
  graph completeness.

All the above were merged only after successful full Lean builds and
axiom audits. The head of main must still be checked from GitHub,
rather than inferred from this ledger.

### Live mathematical boundary

The new PR #103 attempts an injective labelled morphism from the
single-C coset extension of a literal B-component into CE(G,K;C).
That PR must not be counted as certified until Lean CI is green
and the code is cleanly merged to main.

**Do not conflate** (a) a single B-component's full B-extension
embedding into Cayley, (b) single-C extension embeddings, and
(c) the full local multi-CE embedding required by all downstream
applications of ABO Lemma 3.20. The first is checked; (b) is under
formalization; (c) remains open. The latter will require naturality
of component-index refinement and exact gluing across C∩D.

Also still open are the augmented-cluster intrinsic path-component
form of Corollary 3.15, Proposition 3.23 cluster property,
Proposition 3.24, rank-two cluster case of Proposition 4.4,
Theorem 4.7 with repairs R1/R7/R8, Section 5 induction,
the MAX transport bridge and unconditional PSTS EPPA. No
final-EPPA claim is warranted by the present graph constructions.

## 2026-10-08 — corrected local multi-CE embedding checkpoint (#105–#115)

This supersedes the preceding “#103 pending” notes. The authoritative
checkpoint is GitHub `main`, not the historical open-PR descriptions.

### Independently checked and merged

- #108 (the clean main port of the earlier single-C component comparison):
  `ComponentSingleCosetHom` embeds an intrinsic B-component's single-C
  extension into the original K's single-C extension.
- #105 / #110: component-index enlargement and true intersection-support
  witnesses are natural under component inclusion. The canonical local
  multi-coset vertex quotient map is well defined, but these results alone
  made no injectivity claim.
- #111 / #113: a lower-alphabet tagged coset point from the local component
  has the selected intrinsic B-parent index, and every global tagged point
  with that index has a local preimage. #113 is the clean main port of
  #112, which had a merge conflict following #111; #112 was closed without
  being merged.
- #114: the global (C∩D)-intersection-support relation between images of
  two local tagged coset vertices reflects to the actual local intersection
  support. A global support witness has the selected B-parent tag and
  lifts via #113; its images can be compared by the checked injective
  attached-coset maps. This proves the multi-coset vertex quotient map
  **injective**, despite the generally noninjective ambient Cayley map.
- #115: raw local single-C signed edges map to global raw edges. Equal
  source classes and equal signed labels remain equal, so the edge map
  descends to the quotient. It preserves sources, labels, formal reversal;
  the result is a genuine `LabelledGraphHom`, injective on vertices and
  on directed edge tokens by E-graph determinism.

### Still not proved by these commits

- The precise intrinsic B-path-component identification for a lower
  multi-CE family, which is stronger than injectivity of a graph morphism;
  the exact image and component-path bridges are separate gates.
- The intrinsic path-component statement of ABO Corollary 3.15, complete
  source-facing Lemma 3.20, Proposition 3.23 cluster property, Proposition
  3.24, and rank-two *cluster* part of Proposition 4.4.
- Repaired ABO Theorem 4.7, Section 5 construction, Lemma 2.5, concrete
  fibre-MAX bridge, unconditional closed-embedding PSTS EPPA.

The original mathematical warnings remain in force: different intrinsic
components can project onto the same ambient group coset; the coset
extension is a tagged quotient, and neither equality of ambient values
nor graph embedding alone supplies intrinsic component correspondence.
