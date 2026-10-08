# Formalization status

This file is the live map from the mathematical proof plan to Lean.
A statement is called **Formalized** only after the corresponding declaration
is on `main` and GitHub Actions is green.

**Status meanings**

- **API formalized** — definitions compile and are used by later files.
- **Formalized** — theorem and proof are checked by Lean on green `main`.
- **Current target** — active work frontier.
- **Planned** — intentionally not opened yet.

| Mathematical item / gate | Lean declaration / file | Status | Notes |
| --- | --- | --- | --- |
| Repository / CI bootstrap | `PSTSEPPA.lean`, `.github/workflows/lean.yml` | **Formalized** | Lean/mathlib 4.34.1; full build and axiom audit are green. |
| T0: PSTS basic API | `PSTSEPPA/PSTS/Basic.lean` | **API formalized** | `Option`-valued partial operation; diagonal is total; symmetry plus one companion identity, with the other derived. |
| T0: closed subsets / induced systems | `PSTSEPPA/PSTS/Closed.lean` | **API formalized** | Closed sets are closed under defined operation values; restriction to a closed subtype is a PSTS. |
| T0: partial automorphisms | `PSTSEPPA/PSTS/PartialAut.lean` | **API formalized** | Uses option-valued `PEquiv`; source/target are closed; inverse and composition are checked. Composition means first `p`, then `q`, matching `PEquiv.trans`. |
| T0: regression examples | `PSTSEPPA/PSTS/Examples.lean` | **Formalized** | Discrete systems on 0/1/2 points, one Steiner triple, a non-closed two-point subset, and a genuinely partial singleton automorphism. |
| T1: signed words and partial evaluation | `PSTSEPPA/PSTS/WordEval.lean` | **Formalized** | Signed letters, left-to-right evaluation, append/composition and inverse-word calculus; orientation regressions include `p ; p⁻¹` being only a partial identity. |
| T2: abstract MAX interface | `PSTSEPPA/PSTS/MaxTransporter.lean` | **Formalized** | Finite ambient group, group-valued word evaluation, fibre maxima in the `PEquiv` restriction order, and the corrected identity-fibre lemma. |
| T2: quotient development | `PSTSEPPA/PSTS/Development.lean` | **Formalized** | Equality criterion with orientation `g * h⁻¹`, injective base copy, and right-`H` action are checked. |
| T2: quotient PSTS operation | `PSTSEPPA/PSTS/DevelopmentOperation.lean` | **Formalized** | Common-chart operation; fibre-MAX proves functionality; resulting quotient PSTS is checked. |
| T2: closed base copy | `PSTSEPPA/PSTS/DevelopmentBase.lean` | **Formalized** | Exact base-copy operation formula, reflection of undefinedness, and closedness of the base image. |
| T2: quotient automorphism action | `PSTSEPPA/PSTS/DevelopmentAction.lean` | **Formalized** | Right multiplication gives total PSTS automorphisms; distinguished lifts extend the selected partial automorphisms. |
| T2: conditional EPPA transfer | `PSTSEPPA/PSTS/EPPAFromMax.lean` | **Formalized** | Constructive hard gate: `selectedEPPAWitness` packages finiteness, closed induced base copy, and explicit total extensions. |
| A1: labelled graphs / transition groups / retractability | `PSTSEPPA/ABO/Graph.lean`, `Transition.lean`, `ActionGraph.lean`, `CayleyGraph.lean`, `Morphisms.lean`, `CanonicalCover.lean`, `Retractability*.lean` | **Formalized** | Includes loops/formal inverse edge tokens, repeated or trivial generators, right-action orientation, canonical Cayley-to-component maps, source-facing cover normalization, and ABO Proposition 3.3. |
| A2: retractable subgroup/coset intersections | `PSTSEPPA/ABO/SubgroupIntersections.lean`, `CosetIntersections.lean`, `CosetConnectivity.lean` | **Formalized** | Exact `G[A] ∩ G[B] = G[A ∩ B]`; nonempty left-coset intersections and connectedness in the intersection alphabet. |
| A2: ordinary clusters, ABO Lemmas 3.10–3.11 and Corollaries 3.12–3.13 | `PSTSEPPA/ABO/Cluster*.lean`, `Stability.lean`, `ClusterTransport.lean` | **Formalized** | Literal vertex/edge unions; common-core projection; full-coset/lower-cluster component slices; intersection identities; stable-quotient graph bijectivity. |
| A2: augmented clusters and ABO Lemma 3.14 | `PSTSEPPA/ABO/AugmentedCluster.lean`, `AugmentedClusterReflection.lean`, `AugmentedClusterTransport.lean` | **Formalized** | Literal augmented graph and degenerate full-component case; cross-piece reflection; vertex/edge bijective graph morphism under proper-alphabet stability. |
| A2: structural graph-data layer for ABO Corollary 3.15 | `PSTSEPPA/ABO/AugmentedComponentSlices.lean`, `AugmentedComponentClassification.lean`, `AugmentedComponentSeparation.lean` | **Formalized (structural layer)** | Exact C-slices and edges; full-coset/lower-augmented result when the old slice meets the attachment; disjoint union and absence of crossing edges otherwise. Actual path-component correspondence remains open. |
| A2: Cayley skeletons and intrinsic C-components | `PSTSEPPA/ABO/CayleySubgraph.lean`, `CayleySubgraphComponents.lean` | **Formalized** | Arbitrary incomplete skeletons; path concatenation/reversal; intrinsic component equivalence classes; containment in ambient group cosets. |
| A2: admissibility and rank-two base | `PSTSEPPA/ABO/CayleySubgraphAdmissibility.lean` | **Formalized** | ABO Definition 3.16, equivalent ambient-overlap reflection and original disjointness implication; automatic admissibility for |A|≤2 (R4, admissibility part only). |
| A2: component-indexed coset copies | `PSTSEPPA/ABO/ComponentIndexedCosets.lean` | **Formalized (preparatory API)** | Intrinsic B-component quotient indices and separately tagged ambient B-coset copies; original skeleton vertices inject into the copies, with no premature identifications. |
| A2: single-alphabet coset extensions | `SingleCosetExtension.lean`, `SingleCosetEGraph.lean`, `SingleCosetSkeletonEmbedding.lean`, `SingleCosetConnectivity.lean`, `SingleCosetComponentInvariant.lean`, `SingleCosetComponentExact.lean` | **Formalized** | Component-tagged CE(G,K;B) as deterministic E-graph; old skeleton embeds injectively on vertices/edges; intrinsic B-components are exactly the separately attached full B-coset copies, and old B-connectivity is preserved/reflected. |
| A2: non-strict attachment maps and vertex gluing | `ComponentIndexMonotonicity.lean`, `AdmissibleAttached*.lean`, `MultiCosetOverlap.lean`, `MultiCosetTransitivity.lean`, `MultiCosetVertexQuotient.lean`, `MultiCosetSkeletonRigidity.lean` | **Formalized (vertex level)** | Literal intersection-support relation is transitive even with equal/nested/empty alphabets (R5 vertex gate); actual vertex quotient exists, with injective summands and skeleton copies. Ambient projection is not globally injective. |
| A2: raw multi-alphabet edges and provisional edge quotient | `MultiCosetRawEdges.lean`, `MultiCosetRawEdgeInversion.lean`, `MultiCosetEdgeQuotient.lean` | **Formalized (pre-graph)** | Raw alphabet-tagged directed edges, source/target/label/ambient maps and formal reversal; quotient by equal glued source and signed label, with well-defined source/label and injective individual summands. This quotient is NOT YET a labelled E-graph. |
| A2: target congruence and full multi-coset E-graph | `MultiCosetCompletedEdgeOverlap.lean`, `MultiCosetOldEdgeOverlap.lean`, `MultiCosetMixedEdgeOverlap.lean`, `MultiCosetConditionalEGraph.lean` | **Current target; open PRs** | Prove glued-target equality for all raw edges with equal glued source and signed label. Then descend inversion to edge quotient and obtain an unconditional deterministic E-graph. The conditional construction and three case lemmas are pending Lean CI; do not mark Proposition 3.18 complete. |
| A3: corrected ABO Theorem 4.7 | `PSTSEPPA/ABO/UpwardInduction.lean` | Planned | Incorporate repairs R1, R7, R8. Highest-risk gate. |
| A4: corrected Section 5 induction | `PSTSEPPA/ABO/FiniteConstruction.lean` | Planned | Separate repaired `k = 1` base case R2. |
| A5: corrected ABO Lemma 2.5 | `PSTSEPPA/ABO/MainLemma.lean` | Planned | Include final-group equality and equivariance. |
| C1: Cayley / semidirect-product bridge | `PSTSEPPA/ABO/CayleyApplication.lean`, `PSTSEPPA/ABO/MaxTransporter.lean` | Planned | Derive the concrete fibre-MAX property. |
| FINAL: unconditional PSTS-EPPA | `PSTSEPPA/PSTS/EPPA.lean` | Planned | Instantiate T2 with C1. |

## Gate discipline

Do not begin the long ABO construction merely because its definitions are
available. The first major milestone is a compiled conditional theorem of the
form

```text
finite PSTS A + finite selected partial automorphisms + MAX extension
    => finite PSTS witness extending the selected maps.
```

If that transfer layer does not compile cleanly, repair it or use the documented
fallback ladder before investing in ABO Sections 3–5.


### Gate T0 design note

The PSTS API deliberately uses a partial binary operation
`op : V → V → Option V` rather than a ternary relation.  Diagonal values are
total (`op x x = some x`).  Symmetry and one Steiner companion identity are
stored; the second companion identity is derived.  This keeps the structure
nonredundant while making closure under the partial operation literal.

Partial automorphisms are built on mathlib's option-valued `PEquiv`.  The
operation-isomorphism condition is a single `Option.bind` equality, so it
simultaneously preserves and reflects definedness.  Their domains and ranges
are required to be closed.  Inversion, closed preimages and composition are
proved in Lean; the composition convention is the one used by
`PEquiv.trans`: first the left map, then the right map.  This convention is
the one to be used by the signed-word layer.


### Gate T1 checkpoint

Signed words use the same left-to-right convention as `PartialAut.trans`.
Group-valued evaluation uses the matching multiplication order.  Formal
inversion reverses a word and inverts its letters; both group evaluation and
partial-automorphism evaluation respect this inversion.  Regression examples
explicitly prevent the false simplification `p ; p⁻¹ = refl`: for a proper
partial automorphism the composite is only the identity on its source.

### Gate T2 checkpoint: MAX and the quotient skeleton

The abstract input is intentionally only fibre-MAX: for every group value
`h`, a selected word `maxWord h` has that group value and its partial
evaluation extends every other word in the same fibre.  No inverse-monoid API
and no generation hypothesis on the ambient finite group are assumed.

The identity fibre uses the repaired argument:
`refl ≤ eval(maxWord 1)`; since `refl` is total, the latter partial
equivalence equals `refl`.  Hence every identity-fibre word is a partial
identity.

The quotient development is generated by
`(a, liftGen i * k) ~ (gen i a, k)`.  Lean now proves the exact equality
criterion

```text
[a,g] = [b,h]
  iff
there is a signed word w with
  evalH(w) = g * h⁻¹
  and evalPartial(w)(a) = b.
```

This fixes the orientation permanently and yields injectivity of the base map
`a ↦ [a,1]`.  Simultaneous right multiplication of group coordinates
descends to the quotient.  A common-chart relation also defines an
option-valued PSTS operation on the quotient; fibre-MAX is used to prove this
relation functional.

The base image is then proved closed, with an exact formula showing that the
induced partial operation is precisely the original operation on `A`.  Right
multiplication by every `h : H` is lifted to a total automorphism of the
quotient PSTS, and the distinguished lift of each selected generator extends
the corresponding partial automorphism on the base copy.

Finally `EPPAFromMax.lean` packages the construction as
`selectedEPPAWitness`: for finite `V`, any finite fibre-MAX extension
constructively returns a finite PSTS witness, an injective closed induced base
embedding, and explicit total automorphism extensions (with both source and
target equal to `Set.univ`).  This is the completed hard gate; ABO is now the
active frontier.

### ABO A1 checkpoint: labelled groups and retractability

The complete E-graph layer now matches the source conventions: formal edge inversion is fixed-point-free even for geometric loops; distinct labels may induce the same transition permutation; generators may act trivially; and word composition is aligned with ABO's right action by using the opposite permutation group.

For every complete E-graph and base vertex, Lean constructs the canonical labelled morphism from the Cayley graph of the transition subgroup and proves that its vertex and directed-edge images are exactly the reachable component.  Retractability is formalized by deletion of all occurrences of a generator and its formal inverse.  Trivial subalphabet completions are encoded by making generators outside the subalphabet act as the identity.

The based cover formulation is proved equivalent to the source-facing unbased one by left-translation normalization; vertex-surjectivity automatically implies directed-edge surjectivity for complete E-graph morphisms.  The resulting theorem is the source-facing form of ABO Proposition 3.3: for a labelled generating family, retractability is equivalent to existence of covers of all trivial subalphabet completions.

### ABO A2 checkpoint: clusters and the next coset-extension gate

The formalized retractability package now includes the exact subgroup
intersection identity, nonempty coset-intersection formula, and word-level
connectivity of those ambient intersections.  Ordinary clusters are represented
literally by their union of subgroup vertices and signed directed edge tokens;
the canonical retraction projection gives the common point in active pieces.
The full-coset / translated lower-cluster dichotomy and the corresponding
intersection result both identify vertices **and** directed edges, not merely
abstract graph isomorphism types (ABO Corollaries 3.12–3.13).

A labelled quotient that is stable on the proper constituent alphabets induces
a vertex- and edge-bijective labelled graph morphism on the cluster (Lemma
3.10).  The difficult mixed overlap for augmented clusters is handled by the
formal cross-piece coset-reflection argument; adding stability on the attached
alphabet yields a vertex- and edge-bijective augmented cluster morphism (Lemma
3.14).  The Lean statement actually needs target retractability plus
piecewise stability; no extra ambient source retractability is used by this
particular transport proof.

The current Corollary-3.15 package proves exact graph-data decompositions for
C-slices of B-augmented clusters. If the attachment meets the old C-slice,
that slice is either the full C-coset or a translated lower C-cluster augmented
along B ∩ C. In the disjoint case the original C-slice and the new (B ∩ C)-coset
have disjoint vertex sets, and every C-labelled directed edge stays entirely
inside one of those two pieces. These are **not yet** a formal assertion that
the slices equal their intrinsic path-connected C-components. Do not mark the
full path-component form of Corollary 3.15 complete until that bridge is proved.

The new general `CayleySubgraphSpec` provides a skeleton representation for
Definition 3.16, beyond the special case of clusters. Its intrinsic
subalphabet reachability is defined by actual paths in the skeleton, and the
ambient-coset containment direction is checked. Next prove the elementary
intrinsic path-component calculus and then implement admissibility and
coset-extension quotient/gluing with explicit equal-parameter cases (R5).

### 2026-10-08 continuation: admissibility and indexed attachment gate

Intrinsic B-reachability of a general incomplete Cayley skeleton has been proved
reflexive, symmetric and transitive by explicit concatenation and inversion
of realised graph paths. Its quotient into true connected B-components is now
available. In particular, these components must **not** be confused with
ambient B-cosets, which may overlap for different skeleton components.

ABO Definition 3.16 is formalized in the equivalent contrapositive form:
inside one intrinsic B-component, an overlap of ambient B₁- and B₂-cosets
(on proper B₁,B₂ ⊂ B ⊂ A) must be witnessed by a skeleton vertex reachable
from both chosen vertices over the corresponding smaller alphabets.
Its source-facing disjointness implication is proved. The rank-two
admissibility argument from repair R4 is now a Lean theorem for every A of
size at most two, requiring no group retractability or skeleton
connectedness; the *cluster property* part of the cited Proposition 4.4
is a separate future gate.

For a fixed attaching alphabet B, each skeleton B-component indexes a
**separate** ambient B-coset copy, represented without choosing a basepoint
using quotient recursion. Original skeleton vertices inject into this family
of tagged copies. This prepares CE(G,K;B) while avoiding the mathematically
false identification of distinct intrinsic B-components whose images happen
to occupy the same ambient B-coset. Directed-edge completion and the
multiple-alphabet quotient are not constructed yet.

The open proof-engineering task is now to build a literal labelled graph
CE(G,K;B) retaining old non-B skeleton edges and completing all tagged
B-cosets, then formalize the multi-alphabet gluing with the explicit
strict/equal-parameter split R5. An explicit possible model is tagged coset
vertices together with the union of full tagged B-edges and original
skeleton edges outside B. This is a **research plan, not a formalized claim**.
