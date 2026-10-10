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

## 2026-10-08 — B-components of lower-family multi-CE: checked (#117–#121)

**This section supersedes earlier notes that the lower-family intrinsic
B-path-component classification was still open.** The following have all
passed full Lean build and permitted axiom audit and been merged to main:

1. #117 (`MultiCosetParentPathInvariant`): a realised B-supported path
   preserves the B-index after folding lower-family extensions into the
   single-B extension; different parent tags preclude a B-path.
2. #118 (clean port of checked #116, `ComponentMultiCosetRange`): the
   global multi-CE vertices in the image of a chosen local B-component
   are exactly the fibre over that parent B-component tag. No global
   ambient-Cayley projection injectivity is used.
3. #119 (`MultiCosetParentComponentExact`): parent-index equality also
   implies an actual B-path, through selected coset to skeleton anchors,
   an old B-path in K and a second coset-to-skeleton anchor. It establishes
   the **iff** for realised B-path reachability.
4. #121 (`ComponentMultiCosetPathImage`): for any nonempty selected
   family, the image of the local B-component multi-CE in the global
   multi-CE is exactly the *vertex set* of the intrinsic B-component
   containing the embedded original root.

The checked local morphism on all oriented edges remains injective (#115),
but the combined claims above do **not** assert that its edge image is all
B-labelled edges on the corresponding global component. In particular,
old outside-B edges can persist in the global graph; component *vertex*
images and subgraph edge universes must not be conflated.

Open: formal full B-edge image/graph-component correspondence for source
ABO Lemma 3.20, intrinsic component version of Corollary 3.15,
Propositions 3.23/3.24, rank-two cluster property, corrected Theorem 4.7,
Section 5 induction, MAX bridge and unconditional PSTS EPPA. The current
record does not silently close these.

## 2026-10-09 — exact lower-family B-component graph-data theorem

This supersedes the preceding statement that B-edge image-surjectivity
in the local multi-coset comparison remains open.

### Accepted on green main

- **#124**: the actual B-component's own lower-family multi-coset
  E-graph is B-connected. The proof reduces B-path reachability to
  equality of its parent B-component tags and uses actual B-connectivity
  of the original literal subgraph. This includes the empty family
  vacuously; no skeleton embedding is claimed for an empty family.
- **#127**: for a local component L of K and a proper family
  `P` of alphabets all contained in B, the canonical injective
  E-graph morphism `CE(G,L;P) → CE(G,K;P)` has directed-edge image
  **exactly** the global edges whose label belongs to B and whose
  source is in the vertex image.
  * For a completed C-edge, source membership determines the
    selected parent B-component tag; the actual tagged C-coset point
    lifts via the earlier attachment range theorem.
  * For a surviving old K-edge labelled in B but outside its
    presenting C, membership of the source in the parent
    B-component yields an actual B-path from the root and a literal
    lifted skeleton edge.
  * All local edges have B-label because the local old skeleton
    has only B-edges and every attached alphabet C is a subset of B.
- **#129**: combining #127 with the true B-path component theorem
  #121 identifies the local image with the global intrinsic
  B-component *simultaneously on vertices and all B-labelled
  oriented edge tokens*. Formal edge inversion is already respected
  by the labelled graph morphism (#115).

All three were checked via full Lean build and permitted axiom audit.
The superseded historical branches #122/#125/#126/#128 were not merged
(the clean main ports #124/#127/#129 are authoritative).

### Explicitly outstanding

This theorem does not extend automatically to arbitrary selected
coset-alphabet families: if some selected D is not contained in B,
the global B-component can interact with that D-attachment through
its D∩B slice. Nor does the theorem identify old edges outside B,
which are correctly excluded from the B-component graph. Remaining
gates: unrestricted coset-extension component/cluster interaction,
Corollary 3.15 actual path components, cluster property Proposition
3.23, augmented Proposition 3.24, rank-two cluster property,
corrected upward induction, Section 5, the main ABO group lemma,
MAX bridge, and final PSTS EPPA.

No global injectivity of the ambient Cayley morphism is assumed or
derived by the present component theorem.

## 2026-10-09 — source-exact A2 component/support checkpoint

### Fully checked and merged

- **#147**: Actual intrinsic C-path-component trichotomy for
  augmentations of **ordinary retractable clusters** (meeting,
  disjoint old/new, and no attachment in the ambient C-coset),
  combining earlier verified vertex and oriented-edge data.
- **#154**: Corollary 3.13 for ordinary clusters upgraded from
  ambient coset slices to actual paths: whenever genuine B/C
  components intersect, the intersection is exactly one intrinsic
  (B∩C)-component.
- **#148**: each full proper-family multi-coset quotient vertex has
  a component-tagged supporting alphabet; simultaneous B/C
  presentations have exact B∩C support, retaining intrinsic tags.
- **#151**: every quotient vertex has a unique least supporting
  alphabet, whose tagged point maps to every other constituent
  presentation. This follows from finite intersection closure.
- **#155**: the least tagged point comes from a real skeleton
  anchor via an actual word using only the least alphabet.
- **#153**: an arbitrarily selected complete B-coset constituent
  is precisely one genuine B-component of the *whole* multi-CE;
  other members of P may be incomparable to B. Proof by global
  EGraph determinism and B-label edge completeness of the
  constituent, not by ambient-group-map injectivity.

### Source-scope correction and open obligations

The exact ABO arXiv source §3.3.3 distinguishes three levels:
(1) singleton-vertex minimal support is an observation preceding
Definition 3.22; (2) **Definition 3.22** demands that every
**off-skeleton entire B-component** be a B-cluster or full coset
and have a unique minimal component support attained at a core
vertex; (3) **Proposition 3.23 assumes (2)** and derives that every
nonempty B/C-component intersection is a (B∩C)-component.
The present #148/#151/#155 certify (1), not (2).

The complete **both-skeleton-meeting case of Proposition 3.23 is
CERTIFIED on main** by #156, #157 and #161 (clean port of individually
green #158/#160): B/C paths between embedded old skeleton vertices
reflect to K, intrinsic B∩C tags are determined injectively by their
B/C parent tags, and any nonempty intersection of two selected
full B- and C-coset components of the global full proper-family
extension is precisely one intrinsic (B∩C)-component with realised
signed-word connectivity. This relies on the completed B/C constituent
EGraph determinism, exact gluing support and admissibility, not on
injectivity of ambient Cayley coordinates.
The two remaining off-skeleton component cases of Proposition 3.23
still require the whole-component cluster property (Definition 3.22).
The two off-skeleton cases of Prop 3.23 require the genuine
whole-component cluster property and are still OPEN.

Proposition 3.24 concerns augmentations of **full multi-coset
extensions**, not ordinary cluster augmentation Corollary 3.15.
This scope difference must not be conflated. Further open gates:
cluster property of rank-two Proposition 4.4, repaired Theorem 4.7,
Section 5 induction, Lemma 2.5, concrete fibre-MAX bridge,
unconditional finite PSTS EPPA.


## 2026-10-09 — rank-two base and genuine higher-rank component split

### Main-certified structural steps

- **#162** identifies the criterion for a full proper-family vertex's
  actual B-component to meet the embedded skeleton, using its inclusion-least
  component-tagged vertex support. **#165** proves that this criterion is
  invariant along actual B-paths; it does **not** assert that the least
  supporting alphabet remains equal from vertex to vertex.
- **#167/#169** prove that any signed B-edge anywhere in an entire
  off-skeleton B-component is a *completed* edge of some selected C-copy,
  with its signed generator in B∩C. No old skeleton edge can witness
  an off-skeleton B-component edge.
- **#172** closes the rank-|A|≤2 base: each actual B-component of the
  full proper-family coset extension is a selected full B-coset or a
  singleton. The latter carries a unique least component-tagged
  support, universally minimal over its entire B-component, and
  admissibility is supplied by the previously proved rank-two lemma.
  This does not prove the higher-rank cluster-property induction.
- **#175** sharpens the general off-skeleton patch cover: if no B-reachable
  point is supported by a selected C with B⊆C, all signed B-edges of the
  component are completed in *strictly lower* intersection alphabets
  C∩B ⊊ B. Its CI and axiom audit passed; merged as b95f162.
- **#178** proves exact intrinsic B-component geometry inside a selected
  C-copy when B⊆C, *including the case B is not itself selected*: a
  real B-path from a tagged C-point reaches precisely the same C-tag
  and ambient left B-coset. The proof uses EGraph determinism and real
  paths, not ambient projection injectivity. Its CI/axiom audit passed;
  merged as f599cd6.
- **#180** extends #178 to an **entire** B-component of an arbitrary
  admissible multi-CE that meets some selected completed C-coset
  with B⊆C. It is exactly the corresponding tagged full B-coset.
  This establishes the unrestricted-rank *full-coset alternative* of
  the geometric component-shape dichotomy, without assuming the
  higher-rank cluster property. Its CI/axiom audit passed; merged
  as 4fef62f.

### Main-certified component-wide support invariance

- **#181** (clean port of individually green #179) passed its own
  full Lean build and permitted axiom audit and merged as afe6794.
  Support by any selected complete C-coset is invariant along genuine
  B-paths whenever B⊆C. Hence the no-selected-superset-support
  hypothesis for the strict lower-rank patch cover need only be
  checked at a *single* starting vertex, not universally throughout
  the component. This also implies the entire component is disjoint
  from the embedded skeleton. Neither global Cayley injectivity nor
  the higher-rank cluster property is assumed.

Historical conflicting/stacked versions #163/#164/#166/#168/#170/
#171/#173/#174/#176/#177 are superseded and closed; check the main
HEAD and CI for the definitive state rather than relying on their
old PR titles or their obsolete unmerged branches.

### The genuine next mathematical gate

The two branches above must **not** be conflated with the full
ABO Definition 3.22 cluster property. In the no-large-coset branch,
a cover of B-edges by lower-alphabet C∩B patches has been proved;
it does **not** establish that the patches assemble into a single
translated B-cluster with a common core, nor that the entire
off-skeleton B-component has one least tagged support attained
at a core vertex. Those are still nontrivial obligations.

For higher rank, preserve the source's logical structure:
Definition 3.22 is an additional *cluster property*, Proposition
3.23 uses it to deduce exact B/C-component intersections, and
Proposition 3.24 concerns augmentation of the *full multi-coset
extension*, not Corollary 3.15's ordinary-cluster augmentation.
Do not assert that an arbitrary admissible skeleton automatically
has the entire higher-rank cluster property without proof.

Research order: formalize the conditional cluster-property interface,
prove the missing off-skeleton intersection cases of Proposition 3.23,
and then the preservation/augmented extension theorem needed in the
corrected Section 4 induction (including R1/R7/R8). Section 5,
ABO Lemma 2.5, its concrete fibre-MAX instantiation, and
unconditional finite PSTS EPPA remain open. The pre-existing T2
fibre-MAX => PSTS-EPPA transfer is a certified conditional theorem.


## 2026-10-09 — scope guard: PSTS EPPA, not unrestricted ABO

User-reconfirmed primary goal: ordinary EPPA for finite partial Steiner
triple systems with CLOSED embeddings. Do not treat formalization of all
stronger general ABO statements as an independent objective.

The supplied PSTS_EPPA_LEAN_ADVICE_2026-10-07 archive is the main
advisory roadmap, especially its target/scope file, recommended plan,
dependency DAG, the audited transfer note and the Project-2 ABO audit.
The original ABO paper can clarify details but must not override the
independently audited local repairs R1–R8. Neither source shortcuts nor
the audits count as Lean proofs.

### Minimal sufficient final route

1. Gate T2 is ALREADY Lean-certified: the concrete fibre-MAX interface
   yields a finite PSTS EPPA witness for selected partial automorphisms.
   Do not reopen the abstract inverse-monoid or general partial-algebra
   development just to reproduce this transfer.
2. The missing input is a FINITE group satisfying fibre-MAX. A
   sufficient intermediary is the CAYLEY specialization (Cayley-GRL)
   of the ABO graph lemma on Cay(Q,P), with E = Q x P, requiring only
   (a) the group action induced by LEFT Q-translations,
   (b) generator deletion/retractability and minimum content,
   (c) same-endpoint, same-group-value CONTENT-REDUCED paths,
   including the empty-content case.
3. Derive the group H inside the semidirect product G ⋊ Q using the
   chosen permutation extensions of the partial automorphisms;
   prove the concrete path-inclusion order lemma, fibre-MAX and then
   instantiate the already-certified Gate T2.
4. The full general arbitrary-graph ABO Lemma 2.5 may be a useful
   proof METHOD, not a required final deliverable. If the Cayley
   specialization avoids full arbitrary-graph equivariance, complete
   F-inverse covers or other stronger claims, do not formalize them
   merely for their own sake.

### Source repairs and continuation discipline

Respect R1 (derived retractability), R2 (separate k=1 base),
R3 low-rank domains, R4 two-letter admissibility, R5 equal/degenerate
coset parameters, R6/R7 notation corrections, R8 full-coset alternative.
Before opening a new general ABO theorem, identify its concrete
dependency in the Cayley-GRL -> fibre-MAX -> PSTS EPPA route.
If a proposed shortcut fails in Lean, return to the audited
corrected statement rather than silently adding a hypothesis.

### Accepted latest A2 structural checkpoint

After passing full GitHub Lean CI plus the permitted-axiom audit
and merging on main: PR #183/#188 (arbitrary-ambient rank-one component
base and whole-singleton support), #186/#194 (actual boundary/exit
and support descent), #195/#198 (coatom support reduction), #200
(exact coatom signed-edge cover and pairwise tagged anchors),
#202/#205/#206 (coatom-only/full graph isomorphism and signed
path equivalence), #207/#210/#216/#217 (strict lower coatom
edge patches and complete B∩C slices of actual B-components),
#219 (ONE universal skeleton anchor for ALL presentations of
ONE quotient vertex).

The higher-rank common-core property for the ENTIRE B-component,
the corrected Section 4/5 induction, finite Cayley-GRL/MAX and
unconditional PSTS EPPA remain OPEN. Do not conflate vertexwise
common anchors or lower-patch cover with the full cluster property.

## 2026-10-09 — verified Cayley/MAX bridge and finite-full-PSTS transfer

This checkpoint supersedes earlier status notes that described the
entire C1 gate as OPEN. GitHub main is authoritative: merge commit
`d874283` (#241) passed full Lean CI and the allowed-axioms audit.

### Certified on main

1. **Concrete C1** (#222/#226/#228/#230/#231): finite selected Q
   consists of the subgroup of total permutation lifts; every signed
   partial word extends to its Q-value; all Q values have signed words.
   Cayley path endpoint and signed **positive-edge** contents respect
   the actual inverse-edge orientation. Left Q translations act on
   the literal Cayley graph. No faithfulness of distinct generator
   labels is assumed.
2. **Concrete signed path inclusion** (#234): if signed words u,v
   have equal Q endpoint and positive-edge trace(u) is contained
   in trace(v), the partial map of v is a restriction of that of u.
   This is not a conditional ABO/group-existence lemma.
3. **Exact finite-H certificate to MAX** (#237): a finite H with a
   projection to Q and a positive-content-minimal word in every H
   fibre yields the Gate T2 `MaxTransporterExtension`. The finite-H
   content certificate is an EXPLICIT unproved input.
4. **Conditional ALL-PSTS EPPA** (#239): choose the full type
   `PartialAut A` as the selected generator alphabet; independently
   extend each partial automorphism to a total permutation. Under
   the explicit finite-H content certificate, Lean constructs a
   finite witness with closed induced base and extends every partial
   automorphism. This is NOT unconditional EPPA.
5. **Necessary finiteness and semidirect algebra** (#241): the entire
   partial automorphism alphabet is finite by injection into the
   finite function type `V → Option V`; its positive Cayley edges
   `Q × PartialAut A` are finite. The exact formula
   `eval_{G⋊Q}(h,w)=(pathG(1,w),eval_Q(w))` is proved for signed
   inverse letters, using only Q-left equivariance of G edge labels.

### New candidate constructions (separate PR CI required)

- **#242**, the *pairwise reduction implies minimum support* step:
  each H-fibre has at least one word; minimise its positive-edge
  set cardinality and apply pairwise intersection-support reduction
  against arbitrary competitors. The resulting least support
  is included in EVERY competing word, and gives MAX by #237.
  This uses finite individual word supports, not finiteness of the
  entire generator alphabet. The first CI run found namespace/
  visibility elaboration mistakes; fixes are submitted for re-audit.
- **#243**, the finite reflecting-group G to semidirect H step:
  from G with left Q-equivariant labels of **actual** Cayley positive
  edges and source-facing pairwise path reflection (equal G-value
  and equal Q endpoint), construct the finite subgroup
  `H ≤ G ⋊ Q` generated by signed lift values. Prove word
  surjectivity to H, projection to Q, semidirect signed value
  formula, and H-fibre pairwise content reduction. Compose
  #242 + #237 + T2 to obtain an explicit conditional full-PSTS
  EPPA witness directly from this G input. This is stacked
  candidate work pending CI, NOT main-certified.

### Exactly what remains

Produce such a **finite G** with Q action, edge labelling, and
pairwise path reduction. This is the genuinely difficult
Cayley-specialised corrected ABO Section 4/5 existence theorem.
The established A2 tagged-coset geometry (including coatom
component slices, common anchors for ONE vertex, strict lower
B-edge covers, and conditional bridge-free interfaces) still
does NOT prove the whole-component cluster property or higher-rank
repaired induction. If the source's general proof is needed,
use the independently audited R1--R8 corrections and respect
Definition 3.22/Propositions 3.23--3.24 logical dependencies.
Do not introduce a global reflecting group as a Lean axiom.

## 2026-10-09 — actual G ⋊ Q / single-edge deletion checkpoint

### Lean-checked main advances

- PR #243 (bd99fa1) proves the full **conditional** semidirect
  realisation, finite generated H, signed word-value and projection,
  from an explicit finite left-Q-equivariant group G satisfying
  intersection-supported Cayley path reflection. It packages the
  actual finite, closed-PSTS EPPA witness via already-green T2.
- PR #246 (d3b06fb) proves same-H-value one-edge positive content
  deletion is *equivalent* to pairwise positive content reflection,
  by minimizing the number of edges in one path outside the other's
  support. This is fully Lean-checked and does NOT produce the
  source's finite reflecting group.
- PR #247 (07ecc55) proves the correct signed E-edge word of a
  Cayley P-word, with its exact G-evaluation and positive edge list.
- PR #248 (a6a5e84) proves the **algebraic** retractability step:
  equality with a competing path omitting e ensures deletion of
  signed E-letter e from the current path word preserves its G-value.
  This does NOT make the deleted word into a valid path; the
  source's Lemma 5.6 still needs its geometric replacement argument.

### Certified algebraic group-content closure

- PR #249 (a84a802) has passed the complete Lean build and
  permitted-axioms audit and merged to main. It proves the source's
  group-only Proposition 3.5 content realization: subgroup intersection
  for a retractable, generated finite-alphabet group yields a
  same-value word supported in the intersection of any two
  representing supports; a least-cardinality word therefore has
  support included in **every** competing support. This must not be
  conflated with endpoint-preserving path reduction.

### Exact next substantive mathematical task

Establish the **geometric one-edge replacement theorem**: under
the finite group G eventually built by corrected ABO Section 4/5,
whenever a path's E-generator deletion has unchanged group value,
find another ACTUAL Cayley path between the SAME endpoints, with
exactly the SAME G-value and positive-edge support contained in
the original support minus the specified edge. The presently
certified arithmetic/semidirect/PSTS bridges then deliver full EPPA.

One must construct the finite reflecting G, retractability and
coherent Q-action rather than postulate them. The existing
whole-component cluster/bridge-free induction obligations are not
settled by the coatom lower-edge patch cover or a universal anchor
for an individual quotient vertex. Match Lemma 5.6 to the
original corrected ABO I Section 5 stage H_k, plain full
coset-extension covering, and final-to-H_k k-stability, treating
the k=1 gap separately (R2). The corrected source is the fallback
if a proposed shortcut is not provable in Lean.

## 2026-10-09 — corrected ABO Lemma 5.6 stage/reflection interfaces

Main checkpoint `a7e6383` after green full Lean CI and allowed-axiom
audits on #251, #252, #254, and the clean re-port #255 of
independently green source #253.

**#251 (4008101):** source-exact Corollary 5.7 is now an internally
checked theorem conditioned only on endpoint-preserving one-edge
geometric path replacement in an E-graph. It computes the genuine,
represented content from Proposition 3.5, minimizes path support
cardinality at fixed endpoints + FINAL Γ-value, and excludes any
extraneous generator using retractability plus the one-edge path
replacement. This yields exact equality of the terminal path
support with canonical group content, not merely inclusion, and
the empty-content case forces the endpoints to coincide.

**#252 (6f2d7ba):** R1 in the independently audited Theorem 4.7 is
formally repaired. If G→H is k-stable and H is (k+1)-retractable
(on all relevant alphabets), G is (k+1)-retractable: deletion of
a generator in A lowers rank to ≤k, H-retractability gives the
equality downstairs and stability reflects it upstairs; for a∉A
erasure is the identity. Proved as a ranked theorem without assuming
global retractability of G, plus lower-rank/global specializations
and KStable composition along labelled quotient chains.

**#254 (3cb95c8):** the FINAL G-value projection step C3 of
corrected Lemma 5.6 is checked: an explicit generator-preserving
group map G→Transition(stage) induces a canonical Cayley-to-stage
labelled morphism, normalized at a chosen basepoint; two words
with equal G-values have identical projected endpoints. No
injectivity of this projection is needed.

**#255 (a7e6383; source #253):** the C4/C5 selected-coset step is
also checked. Using the preexisting A2 theorem on genuine B-path
reflection between embedded skeleton points in a selected B-copy,
extract a REAL B-skeleton path; compare its intermediate H-value
to the competing B-word through the multi-CE ambient Cayley
homomorphism, then reflect to the FINAL group G through stability
at |B|≤k. The quotient tags are retained; ambient coordinates
are not wrongly assumed globally injective.

**#256 (466d38e; certified and merged):** automatic coherence
of the Cayley left Q-action, once individual automorphisms of the
E-generated reflecting G extending each translation are provided.
Equality on generator images forces uniqueness, identity and
multiplication. This proves a Proposition-5.5 *consequence*,
not existence of those automorphisms or the finite reflecting G.

**#257 (d2e2e3a; certified and merged):** the finite
synchronized product subgroup of two E-generated labelled groups
with surjective label-preserving quotient projections onto each
factor and exact signed word coordinate values. Full Lean and
permitted-axioms audit passed. This is preparatory algebra for
finite-stage transition groups, NOT the missing finite reflecting
group or a proved identification with any literal disjoint-union
transition group.

**Genuine remaining gap:** Stage existence and construction,
not the formal deduction from Cayley-GRL to PSTS EPPA. In
particular the H_k-cover and its actual full CE must occur in
the Section-5 tower with the correct generator-preserving
projection from final G; the higher-rank whole-component
cluster property, Proposition 3.24, bridge-free induction,
k-stability of the G_{k+1}→H_k stage, and the independent
k=1 repair R2 remain unproved in Lean. The audited source
(Project 2A/2B) argues these are correct with repairs R1–R8;
that is advisory mathematical evidence, NOT proof-kernel
certification. Follow this dependency order rather than
silently assuming the reflection group exists.

## 2026-10-10 — disjoint-stage transition groups and loop-completion invariant

GitHub green-main substantive checkpoint: `07d28a0`. The following
declarations are independently Lean-checked after full CI and
allowed-axiom audit, not imported as asserted source claims:

1. **#259 / 4c629d1:** automatic 1-retractability of every
   labelled group, plus rank-zero version. This covers precisely
   the elementary low-rank deletion fact of audit repair R2,
   *not* the unresolved 1-stability G₂→H₁ or full Proposition 5.4.
2. **#260 / 9117d3a:** actual disjoint unions of complete
   oriented E-graphs with true inverse-edge tokens and paths,
   and reflection of componentwise paths.
3. **#261 / 07d28a0:** identification of the transition group
   of that literal disjoint complete E-graph with the
   synchronized subgroup of the direct product of both component
   transition groups. The proof constructs an injective
   right-permutation sum hom respecting chronological products
   and each literal transition generator, and proves subgroup
   image-surjectivity by generator-closure induction.
   This DISCHARGES the earlier open transition-group-product
   identification in the ledger; it does not prove any stability
   rank of later quotient maps.
4. **#262 / bf9c850:** paired outgoing positive/negative labels
   for weakly complete full multi-coset extensions: a completed
   tagged B-coset edge at source p has a companion of reverse
   signed label at the same source. General E-graphs do NOT
   have this property, so loop-only completion must rely on
   this proof, not be declared for arbitrary E-graphs.

Active unmerged candidates: **#263** proves construction of
loop-only trivial completion for graphs with locally paired
outgoing labels; **#264** proves such completion cannot create
new B-labelled path connectivity. Both need full Lean/axiom CI
and can still change. Preserve this status on handoff.

Main remaining mathematical gates are the finite Section 5
tower's actual covering and stability inductions, the R2
k=1 stability case, and the higher-rank Definition 3.22
whole-component cluster property/Propositions 3.23--3.24
and Theorems 4.5/4.7. Corrected ABO Lemma 5.6 still requires
its true geometric path replacement; the already certified
ABO-to-PSTS fibre-MAX transfer remains conditional.

## 2026-10-10 — R2 full coset stages, loop completion, and CI status

**Main checkpoint:** `36d42a0`. For #263/#264/#267/#269
the actual full GitHub Actions Lean build and permitted-axioms
audit were SUCCESSFUL before each merge.

1. **#263, 71bfd8e**: locally paired availability of
   positive/negative signed edges permits the actual
   `trivialLoopCompletion` construction by extending
   each partial generator transition with fixed points.
   Old directed edges embed injectively, and all added
   edges are geometric loops. This uses the genuine
   paired-label invariant certified in #262 for weakly
   complete multi-coset extensions.
2. **#264, 5aaffcc**: exactly NO new subalphabet B-path
   relations under trivial completion, for every B.
   This is a real path induction, deleting only newly
   inserted loops, not merely an abstract set-level
   connectedness statement.
3. **#267, d481438**: instantiate those results on
   weakly complete tagged multi-coset extensions and,
   with full all-proper family |A|≥2, prove exact
   B-skeleton connectivity in the completed EGraph
   for all selected B⊂A.
4. **#269, 0032853**: rank-two signed-edge source
   dichotomy. Any original i-labelled edge in a
   full proper-coset CE at |A|=2 necessarily has
   source in the selected complete tagged singleton
   {i}-constituent. This strengthens the older
   full-coset vs isolated singleton component base
   and avoids ambient-coordinate injection.

**Additional accepted mathematical claims (each green after
complete Lean + permitted-axioms audit):**

- **#266, 0ab7e5a**: explicit signed-alphabet finiteness
  and finiteness of every complete finite-carrier EGraph's
  actual generated opposite-permutation transition group.
- **#268, 57201f3**: exact equivalence of k-stability
  with kernel of all ≤k-alphabet labelled words, plus
  the genuinely moved-vertex test for nonidentity
  transition values in complete stage EGraphs.
- **#270, a2579c0**: source's rank-two exact full
  tagged B-coset versus singleton alternative persists
  through the literal trivial-loop completion.
- **#271, 36d42a0**: word-kernel theorem for
  completed unaugmented rank-two full coset stages:
  a B-word of ambient group value 1 fixes every
  completed stage vertex (whether in tagged B-coset
  or isolated singleton). This is a concrete part
  of the corrected k=1 R2 argument.

**Not yet certified:** #273 literal augmented-cluster
trivial stage and no-new-C-path theorem, plus stacked
#274 singleton group-identity word-kernel for these
augmented stages. Their current GitHub CI governs the claims.

**Next actual mathematical gate:** R2 for the WHOLE
Definition 5.3 Z₁ family, including augmented
clusters and augmented full coset extensions,
then 1-stability of G₂→H₁. Group finiteness,
unaugmented full-coset geometry and word-kernel
conditions are necessary but insufficient.
The higher-rank Section-4 cluster/bridge-free
induction and final Cayley finite reflection
remain open; do not assert unconditional PSTS EPPA.

## 2026-10-10 — repaired Proposition 5.4 R2: augmented type-(1) and assembly checkpoint

All of PRs **#273, #274, #275, #276, #277, #278** were merged following
green full Lean builds and allowed-axioms audits of their PRs.

**Certified results and exact source scope:**

1. #273: genuine loop-completed *augmented clusters*, preserving all
   actual labelled-component reachability.
2. #274: for any signed singleton-supported word w of ambient group
   value 1, every vertex of an actual completed augmented-cluster
   stage is fixed by w. The proof splits real full-coset coverage
   from complete absence of old edges for that singleton label.
   This discharges the word-kernel aspect of Definition 5.3
   type-(1) objects (the augmented cluster stages).
3. #275: synchronous product over two k-stable quotients to one
   labelled target remains k-stable; this uses BOTH coordinate
   word-value identities and never assumes joint generator
   injectivity.
4. #276: the transition word kernel on the LITERAL disjoint
   union of two complete E-graphs is the intersection of their
   kernels, including inverse letters and empty carriers.
5. #277: an actionGraph on dependent tagged vertex fibres
   (a sigma-type) has exactly componentwise signed-word
   evaluations, and hence for any indexed family its transition
   word kernel is the intersection over all stages. This is an
   ACTION RE-ENCODING, not a claim that pre-existing edge-token
   types are literally the same.
6. #278: the true generated transition subgroup of any complete
   E-graph satisfies `IsGenerated` for the labelled generators.
   This supplies the generation hypothesis when applying #275
   to actual stage transition groups.

**Outstanding hard gate, not a corollary of the six results:**
The corrected source audit (Project 2A, §8.3) first constructs
`H₁` and the finite `Z₁`, then analyzes BOTH (1) augmented clusters
and (2) augmented full coset extensions of `H₁`-covers.
The formalization now has the word-kernel step for (1) and the
algebraic disjoint/synchronized assembly. It does **NOT** have:

- the complete rank-two cluster-property conclusion of source
  Proposition 4.4 (the checked two-letter admissibility alone
  is insufficient);
- a literal augmented **full coset extension** stage with the
  Proposition 3.24 singleton-component classification, or its
  corresponding completed-stage word-kernel;
- the real `H₁` cover and finite indexed `Z₁` family with the
  generator-preserving quotient `G₂→H₁`;
- a Lean proof that this quotient is `1`-stable, or the later
  higher-rank Section 4–5 induction and reflecting finite group.

**Recommended next route:** finish the rank-two whole-component
cluster property, implement the type-(2) augmented full-CE
construction and singleton full-coset/isolated-component split,
prove its word-kernel on the genuine completed stage, and combine
with #274/#277/#278 (and #275 where suitable) to assemble
`Z₁` and prove the actual corrected R2 `G₂→H₁` 1-stability.
Do not replace type (2) by an arbitrary augmented cluster,
or assume its singleton classification without Lean proof.

The fibre-MAX → PSTS-EPPA transfer on green main remains
**conditional on the finite reflecting group**; no
unconditional PSTS EPPA has been certified.


## 2026-10-10 — R2 genuine type-(2) rank-one kernel certified; finite-stage construction frontier

GitHub authoritative **main merge `89ea31c4`**, via PR #299,
full Lean compile plus permitted-axioms audit **SUCCESS** on PR
CI run `38051990893`. The post-merge `main` CI is separate.

**New certified stage geometry and action:**

1. #280/281/285: for a genuine rank-two all-proper multi-coset
   EGraph, an off-selected-B singleton has NO original signed
   B-edge. This discharges the actual deterministic full B-coset
   gluing with root identified, all other coset points fresh,
   true formal inverse edge tokens, and original old-edge inclusion.
2. #282: the same rank-two singleton base has the full *off-skeleton
   B-component* statement from Definition 3.22 and component-tagged
   least support over its entire one-vertex component.
3. #283/287: locally paired old/new signed availability gives an
   actual COMPLETE loop-only augmented type-(2) stage; ambient
   identity-valued attached B-words fix the entire attached coset
   including the old root.
4. #284/286/288: complementary true path and completed-action
   transport: C disjoint B paths between old vertices unchanged,
   old nonroot B-paths cannot reach the new root, and the
   *whole signed B-word action* at old off-root points agrees
   literally with the old completed stage.
5. #299: the formalized
   `rankTwoOffComponentCompletedStage_rankOne_wordValue_eq_one`
   states: for arbitrary finite-label subset C with |C|≤1
   and signed word w using C, ambient eval(w)=1 forces the
   **actual augmented completed stage's transition-group**
   wordValue(w)=1. THIS IS FOR ALL SINGLETON GENERATORS,
   including those outside A; the rank-two proper-or-disjoint
   C dichotomy, actual all-proper multi-CE edge-label support
   and outside-A fixed-loop theorem establish the final case.
   In particular it is stronger than earlier results for
   only the attached B. The 11 underlying modules and all
   assertions are integrated in the green-tested #299 merge.
   Component PRs #289–#298 have been marked superseded and
   closed; nothing essential remains only in those branches.

**Research boundary (important for handoff):** the above is
one concrete class of stage in the R2 catalogue, NOT existence
of the full finite `H₁` and `Z₁` from the source,
and does NOT automatically give an actual 1-stable labelled
quotient `G₂→H₁`. The surviving hard construction work is:
(A) verify all Definition-5.3 stage variants and their relation
to the H₁-cover; (B) obtain actual finite stage carriers and an
explicit finite indexed family; (C) prove the common-target
generator-preserving transition-group quotient; (D) combine
the per-stage rank-one kernels via the previously certified
dependent-disjoint-stage kernel #277 and exact k-stability
word-test #268. The higher-rank Section 4 construction,
endpoint-preserving geometric path replacement, and final
finite reflecting group remain open.

**#300 pending / failed first build:** real finite-carrier
certificate for type-(2) stages under a finite Γ. First run
`38051912898` failed because simply calling `infer_instance`
did not synthesize dependent/quotient `Finite` certificates.
The current revision explicitly constructs finiteness from
finite components and quotient surjections. **Do not mark
#300 accepted until its updated CI turns green and merges.**


## 2026-10-10 — AUTHORITATIVE post-#334 checkpoint: explicit finite algebraic rank lift and connected-cover factorization

**Repository cutoff:** \`main\` merge \`509636b86531f7d8c43b1ab274dcdf3c1800e0cd\`
(#334), itself stacked on green merges #328 (\`3b8307e8\`), #329
(\`2f889cff\`) and #331 (\`4e4af178\`). Each integration PR passed
a fresh whole-project Lean build and permitted-axiom audit before merge.
The separate post-merge \`main\` CI must be checked on its own.

**Older entries through #299/#300 above are historical snapshots, NOT
current open-item lists.** In particular, their statements that finite
type-(2) carriers, rank-one stage kernels and the rank-two cluster base
are pending were superseded by later merged source files. The items
listed as still open below are the *current* conservative boundary.

### A. What is actually formalized

1. **Rank-bounded group calculus:** #310–312, including local-to-global
   retractability on generated ≤k subalphabet completions and literal
   subgroup/coset intersections under |A∪B|≤k
   (\`KRetractableCosetIntersections.lean\`).
2. **Actual rank-two augmented action and stable finite assembly:**
   #299–309, #313–316, #318 and consolidated #325. Includes actual
   finite type-(1), singleton type-(2) augmented full-coset and plain
   coset-extension completed stages, their complete singleton signed
   word kernels, one finite dependent stage union and an actual
   generator-preserving 1-stable synchronous quotient. The source
   rank-two subgraphs can be literal slices of a SINGLE incomplete
   ambient Cayley skeleton, not a hypothesized family.
3. **Concrete finite low-rank tower:** #328 (integrating #324/#326/#327)
   constructs, for each finite generated labelled Γ and genuine
   incomplete Γ-Cayley skeleton K, finite groups
   \`G₂ → H₁ → Γ\`, actual surjective generator-preserving 1-stable
   quotient maps, 2-retractability of the new groups, composition and
   1-stability of the composite. Its H₁ skeleton is a TRUE finite
   graph pullback with actual signed-edge surjectivity and unique
   signed-path lifting, not an arbitrary finite abstract graph.
4. **Connected-Cayley normalization and pullback factorization:**
   #329 and #331 show that, over any FIXED labelled group quotient
   Q:H→Γ, the coordinates of an actual labelled Cayley-skeleton
   morphism are left translations of Q on each intrinsic component.
   Each component then INJECTS as a genuine labelled subgraph of
   the corresponding translated canonical pullback. Factorization
   commutes with the original morphism on BOTH vertices and signed
   oriented edge tokens; it is not merely an ambient-coset identity.
5. **NEW all-rank algebraic detector theorem:** #334 integrates
   \`RankDetectorGroup.lean\` and \`RankDetectorSynchronizedLift.lean\`.
   With finite label set E and arbitrary labelled Γ, let
   \`D_k = ∏_{A⊆E, |A|≤k} Γ[A]\`, with all labels outside A trivial
   in each genuine generated-subgroup coordinate, and put
   \`H_{k+1}=⟨(gen(e),detector(e)):e∈E⟩≤Γ×D_k\`.
   The actual synchronously generated \`H_{k+1}\` is
   **(k+1)-retractable for every Γ**, with NO k-retractability
   assumption on Γ. If Γ is generated and k-retractable, the
   generator-preserving quotient \`H_{k+1}↠Γ\` is **k-stable**.
   For finite Γ, \`H_{k+1}\` is finite.
   The proof checks equality of arbitrary PAIRS of signed words
   through the corresponding lower-rank detector coordinate after
   erasure; it neither postulates a group quotient nor assumes
   generator independence. This is a candidate simplification of
   the ALGEBRAIC part of corrected ABO Theorem 3.8, not a claim of
   complete replacement of its finite graph-action family.

### B. Exactly what remains OPEN

- **Source-faithful Y₁/Z₁ and Y_k/Z_k completeness.** Our finite
  detector and rank-two stage families need not equal, or be proved
  sufficient for, every H_k-cover \`C_H\` and augmentation indexed
  by source Definition 5.3, including B=∅. Do not equate a redundant
  all-coset-stage superfamily or an arbitrary pullback with the
  actual entire source catalogue without a covering/simulation lemma.
- **Cover component surjectivity:** #331 proves an INJECTIVE
  factorization of any intrinsic component into a translated
  pullback. It does NOT prove its image equals the ENTIRE connected
  pullback component. A promising next lemma assumes that the
  original morphism locally lifts every actual target edge and
  proves surjectivity onto that component by path lifting.
- **Geometric closure and propagation:** Definition 3.16
  admissibility, source Definition 3.22 cluster property, whole
  augmented CE/component classification, embeddedness and
  bridge-freeness must be verified for the actual chosen stage
  families at higher ranks, and then Condition 5.2 and
  corrected Theorem 4.7 / Proposition 5.4 must run without
  silently strengthening the inductive assumptions.
- **Naturality/equivariance:** Proposition 5.5's left-translation
  symmetry through the entire finite stage tower and the eventual
  finite reflecting group still require proof, followed by the
  already certified conditional fibre-MAX → PSTS-EPPA transfer.

**Suggested order:** (i) formalize generic genuine signed-path lifting
from local edge-covering data; (ii) upgrade #331's component embedding
to image equality for true connected covers; (iii) audit source
Definition 5.3's precise index set against the proposed canonical
pullback/slice construction; (iv) prove the exact geometric
admissibility/cluster/bridge-free induction or fall back to the
source-specific stage family wherever the shortcut is false.

**Non-claim:** no complete finite reflecting-group construction and
no unconditional ordinary EPPA theorem for finite partial Steiner
triple systems is currently certified. The progress above is a
real group-theoretic and low-rank graph-theoretic formalization
milestone, not a completion of the project.
