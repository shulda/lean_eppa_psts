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
| A2: ABO Corollary 3.15 — augmented clusters | `AugmentedComponentSlices.lean`, `AugmentedComponentClassification.lean`, `AugmentedComponentSeparation.lean`, `AugmentedComponentTrichotomy.lean`, `AugmentedMeetingComponentPaths.lean`, `AugmentedDisjointComponentExact.lean` | **Formalized (graph data and intrinsic components)** | PRs #131/#132/#134/#137/#144/#147. Actual signed C-path trichotomy for each ambient C-coset slice: old/attachment meeting gives one connected piece; disjoint old and new pieces yield two disconnected components; no attachment intersection retains old cluster's component. Exact graph-data identities also checked. This is the *cluster* augmentation result, not Prop 3.24 for augmented **full coset extensions**. |
| A2: Cayley skeletons and intrinsic C-components | `PSTSEPPA/ABO/CayleySubgraph.lean`, `CayleySubgraphComponents.lean` | **Formalized** | Arbitrary incomplete skeletons; path concatenation/reversal; intrinsic component equivalence classes; containment in ambient group cosets. |
| A2: admissibility and rank-two base | `PSTSEPPA/ABO/CayleySubgraphAdmissibility.lean` | **Formalized** | ABO Definition 3.16, equivalent ambient-overlap reflection and original disjointness implication; automatic admissibility for |A|≤2 (R4, admissibility part only). |
| A2: component-indexed coset copies | `PSTSEPPA/ABO/ComponentIndexedCosets.lean` | **Formalized (preparatory API)** | Intrinsic B-component quotient indices and separately tagged ambient B-coset copies; original skeleton vertices inject into the copies, with no premature identifications. |
| A2: single-alphabet coset extensions | `SingleCosetExtension.lean`, `SingleCosetEGraph.lean`, `SingleCosetSkeletonEmbedding.lean`, `SingleCosetConnectivity.lean`, `SingleCosetComponentInvariant.lean`, `SingleCosetComponentExact.lean` | **Formalized** | Component-tagged CE(G,K;B) as deterministic E-graph; old skeleton embeds injectively on vertices/edges; intrinsic B-components are exactly the separately attached full B-coset copies, and old B-connectivity is preserved/reflected. |
| A2: non-strict attachment maps and vertex gluing | `ComponentIndexMonotonicity.lean`, `AdmissibleAttached*.lean`, `MultiCosetOverlap.lean`, `MultiCosetTransitivity.lean`, `MultiCosetVertexQuotient.lean`, `MultiCosetSkeletonRigidity.lean` | **Formalized (vertex level)** | Literal intersection-support relation is transitive even with equal/nested/empty alphabets (R5 vertex gate); actual vertex quotient exists, with injective summands and skeleton copies. Ambient projection is not globally injective. |
| A2: multi-alphabet edge quotient / formal inversion | `MultiCosetRawEdges.lean`, `MultiCosetRawEdgeInversion.lean`, `MultiCosetEdgeQuotient.lean`, `MultiCosetConditionalEGraph.lean` | **Formalized** | Raw directed edges and source/label quotient, all inversion and ambient-rigidity laws; target-congruence was isolated explicitly and the resulting deterministic E-graph constructed conditionally before discharge. |
| A2: completed multi-alphabet CE graph | `MultiCosetCompletedEdgeOverlap.lean`, `MultiCosetOldEdgeOverlap.lean`, `MultiCosetMixedEdgeOverlap.lean`, `MultiCosetEGraph.lean` | **Formalized** | The three old/old, completed/completed and mixed edge cases discharge target congruence for all raw tokens. This constructs a full deterministic multi-alphabet E-graph with formal inverses and injective single-B constituent vertex/edge maps, assuming the source admissibility/retractability/generation conditions. |
| A2: canonical morphisms / ABO Proposition 3.18 | `MultiCosetMorphisms.lean`, `MultiCosetMorphismsUnique.lean` | **Formalized (nonempty-family scope)** | Canonical labelled graph morphism CE(G,K;P)→Cayley(G), injective and alphabet-independent skeleton embeddings, unique morphism extending skeleton values when P is nonempty. The ambient morphism need not be globally injective; P=∅ is excluded from the literal skeleton-containing model. |
| A2: actual component intersections (ABO Lemma 3.21) | `AdmissibleComponentIntersections.lean` | **Formalized (intrinsic paths)** | For B,C⊂A, admissibility+retractability imply simultaneous B/C path reachability iff (B∩C)-reachability; any nonempty intersection of intrinsic B/C skeleton components is exactly one (B∩C)-component, including nested and equal cases. |
| A2: lower-component skeleton and admissibility (ABO Lemma 3.20) | `LocalComponentAdmissibility.lean`, `ComponentSubgraph.lean`, `ComponentSubgraphPaths.lean`, `ComponentSubgraphAdmissibility.lean`, `ComponentSubgraphConnected.lean`, `ComponentSubgraphIndices.lean` | **Formalized (local core)** | Actual B-component as a Cayley subgraph, B-path connected; D⊆B paths reflect both ways, D-component indices and attached D-cosets inject into those of K. The lower B-component inherits admissibility. |
| A2: local coset embeddings and lower-family folding | `LocalCosetEmbedding.lean`, `SingleCosetEnlargement.lean`, `GraphHomInjectivity.lean`, `MultiCosetParentFold.lean`, `MultiCosetParentHom.lean`, `ComponentFullCosetEmbedding.lean` | **Formalized (specified embeddings)** | Injective CE(G,K;C)→CE(G,K;B) for C⊆B⊂A, whole family CE(G,K;P)→CE(G,K;B) for P⊆P(B); bijection if B∈P. A single actual B-component's full B-extension embeds in ambient Cayley with vertex image exactly root·G[B]. The local multi-CE embedding and the lower-family intrinsic B-component comparison on vertices and B-labelled edges are formalized separately below; extending to unrestricted coset families remains open. |
| A2: canonical full proper-alphabet family | `StandardCosetFamily.lean`, `MultiCosetWeakCompleteness.lean` | **Formalized (rank ≥ 2)** | P_A consists of all proper subsets of A. If |A|≥2, every old edge label lies in some proper singleton alphabet and the standard multi-CE is weakly complete. The rank-one exception is explicit; weak completeness is not global edge completeness. |
| A2: local single-C extension comparison | `ComponentSingleCosetHom.lean` | **Formalized** | Injective labelled graph embedding of the single-C extension of a literal B-component into the corresponding extension of K; ported by PR #108. |
| A2: local multi-alphabet extension embedding | `ComponentCosetNaturality.lean`, `ComponentMultiCosetVertexMap.lean`, `ComponentParentIndexControl.lean`, `ComponentAttachmentRange.lean`, `ComponentMultiCosetEmbedding.lean`, `ComponentMultiCosetHom.lean` | **Formalized (injective labelled E-graph morphism)** | PRs #105/#110/#111/#113/#114/#115. Component-tagged intersection supports preserve **and reflect** actual gluing within an intrinsic B-component; the quotient vertex map is injective and extends to a labelled graph morphism injective on vertices and signed directed edges. No global ambient-Cayley injectivity is claimed; the later lower-family component/path/edge statements are separate checked theorems. |
| A2: exact intrinsic B-components for lower-family multi-CE | `ComponentMultiCosetRange.lean`, `MultiCosetParentPathInvariant.lean`, `MultiCosetParentComponentExact.lean`, `ComponentMultiCosetPathImage.lean` | **Formalized (vertex and actual B-path level)** | PRs #117/#118/#119/#121. The local vertex image is exactly the selected parent-B-index fibre; two global points are genuinely B-connected iff their B-parent indices coincide; for a nonempty lower family the local image is precisely the intrinsic B-path-component of the embedded root. The corresponding exact B-labelled signed-edge image is now formalized separately below. |
| A2: lower-family local B-component as a labelled graph | `ComponentMultiCosetConnected.lean`, `ComponentMultiCosetEdgeRange.lean`, `ComponentMultiCosetBComponentEdges.lean` | **Formalized (all vertices and B-labelled signed edges)** | PRs #124/#127/#129 (clean ports of earlier green work). Every local edge has B-label; a global B-edge has a local preimage iff its source lies in the local vertex image. For nonempty family the local image agrees with the intrinsic B-component of the root on both vertices and B-labelled oriented edges. This does **not** include old edges with labels outside B, or a global family containing alphabets not below B. |
| A2: intrinsic connectedness of ordinary clusters | `ClusterCayleySkeleton.lean`, `CayleySubgraphFullCosetPaths.lean`, `ClusterComponentPaths.lean`, `ClusterIntrinsicComponentIntersections.lean` | **Formalized** | PRs #131/#132/#137/#154. Retraction plus common-core coset intersection yields genuine C-labelled paths; intrinsic C-components of clusters are ambient C-coset slices, and intersections of actual B/C-components are intrinsic (B∩C)-components. |
| A2: full-proper-family singleton minimal support | `MultiCosetVertexSupport.lean`, `MultiCosetMinimalSupport.lean`, `MultiCosetMinimalSupportPaths.lean` | **Formalized (single vertices only)** | PRs #148/#151/#155. Each vertex of CE(G,K;P_A) admits a unique least support alphabet and compatible *component-tagged* supporting coset point. It is reachable from an original skeleton anchor by a word over exactly that supporting alphabet (i.e. uses no other letters). This does **not** prove uniform minimal support for whole off-skeleton B-components, as required by Definition 3.22. |
| A2: full-family selected B-coset component | `MultiCosetSelectedComponentExact.lean` | **Formalized** | PR #153. If B is selected, each intrinsic-component-tagged full B-coset is exactly one genuine B-path component of CE(G,K;P), even when P contains other alphabets not below B. Derives from B-edge completeness of the B constituent plus global EGraph determinism; no global ambient injectivity. |
| A2: ABO Proposition 3.23, both-skeleton-meeting case | `MultiCosetSkeletonComponentIntersections.lean`, `ComponentIndexPairInjectivity.lean`, `MultiCosetSelectedComponentIntersections.lean`, `MultiCosetSelectedComponentInterExact.lean` | **Formalized (both selected full-coset components)** | PRs #156/#157/#161 on green main. For the full proper-alphabet CE, intersecting selected complete B- and C-coset components have exactly one intrinsic (B∩C)-component, with real signed-word paths. Also B/C connectivity between embedded old vertices reflects K. This is *only* the source Proposition 3.23 case when both components meet the skeleton; the two off-skeleton cases still depend on Definition 3.22 cluster property. |
| A2: remaining Section 3/cluster gates | `MultiCosetSelectedComponentExact.lean`, `MultiCosetMinimalSupport.lean` and pending refinements | **Partially formalized; main induction open** | Correct source scope: Definition 3.22 **assumes/defines** the off-skeleton *whole-component* cluster property; Proposition 3.23 **assumes** this property and proves actual B/C-component intersection connectivity. Singleton minimal supports and all selected complete B-cosets are checked; off-skeleton whole-component minimal supports, remaining cases of Prop 3.23, Prop 3.24 augmented full coset extensions and the rank-two cluster property remain OPEN. |
| A3: corrected ABO Theorem 4.7 | `PSTSEPPA/ABO/UpwardInduction.lean` | Planned | Incorporate repairs R1, R7, R8. Highest-risk gate. |
| A4: corrected Section 5 induction | `AugmentedClusterTrivialStage.lean`, `RankTwoType2IndexedFamily.lean`, `SourceH1AllLocalG2.lean`, `Type2G2CatalogueActionOccurrence.lean`, `SourceG2Type1FamilyActionCover.lean`, `SourceG2Type2FamilyActionCover.lean` and source-transport modules | **Partially formalized; higher-rank tower OPEN** | Main 717b30aa includes a genuine input-dependent finite 1-stable G₂→H₁, locally complete type-(1)/(2) augmented signed actions, actual Cayley action covers, correct original type-(2) (B,z) index correspondence and true source/local completed augmentation identification. The FULL original Definition-5.3 Z₁ source stage-family action coverage, corrected Section-4/5 geometry/Condition 5.2 and higher-rank Yₖ/Zₖ induction remain open. Do NOT infer them from local catalogue inclusion alone. |
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

### 2026-10-08 — checked local multi-coset comparison checkpoint

This checkpoint supersedes the outdated “PR #103 pending” table entry and
old ledger frontier. After the local intrinsic B-component was proved
admissible and the single-C embeddings were installed, the following
additional formalized steps were merged to `main` with successful full Lean
CI and axiom audits:

- PR #105 preserves exact intersection-support gluing under local coset
  inclusion; PR #110 constructs the well-defined local-to-global multi-coset
  vertex quotient map.
- PR #111 proves that every local attached lower-alphabet point has the
  selected parent B-component index; PR #113 proves the converse range-lifting
  statement for tagged global lower coset points (clean port of #112).
- PR #114 reflects global intersection support back into the actual local
  component and proves injectivity of the multi-CE vertex map.
- PR #115 extends this map to a genuine injective labelled E-graph morphism
  (including all signed directed edges and formal inversion).

The image can still have a nontrivial intrinsic B-path-component issue:
being an injective labelled morphism is not the same as identifying the
full intrinsic path component of the global extension. This and the rest
of ABO Section 3, Section 4/5 inductions and fibre-MAX bridge remain open.
The unconditional PSTS EPPA theorem has **not** been formalized.

### 2026-10-08 — exact parent-component and path-comparison checkpoint

This checkpoint supersedes the older “path-component identification open”
comments in the preceding status narrative. In addition to the local graph
embedding (#114/#115), Lean CI and the permitted axiom audit have checked:

- PR #117: every actual B-word path in the lower-family multi-CE preserves
  the intrinsic parent B-component tag.
- PR #118 (clean port of green-but-unmergeable #116): a global glued vertex
  lies in the image of the local B-component's multi-CE vertex map exactly
  when its image in the containing single-B extension has the selected
  parent B-component index.
- PR #119: conversely, the equality of these parent indices is *equivalent*
  to the existence of an actual B-labelled path connecting the two global
  multi-CE vertices. The proof uses real constituent coset attachment paths
  and an actual B-path in the original skeleton.
- PR #121: for a nonempty lower-alphabet family, the local multi-CE's
  vertex image is exactly the intrinsic B-path component of the original
  root in the global multi-CE.

Thus source-facing B-component comparison is now verified **on vertices
and reachability**. The image-on-B-labelled-directed-edges statement is a
separate remaining obligation; outside-B old skeleton edges can remain in
the global multi-CE and are not automatically part of the local graph.
Neither this nor the earlier completed multi-coset constructions proves the
ABO upward induction, fibre-MAX extension, or final PSTS EPPA result.

### 2026-10-09 — local multi-coset B-component graph comparison

This checkpoint supersedes the previous notes that the lower-family
multi-CE component correspondence was only checked on vertices.

The following were merged on green full Lean CI with axiom audit:

- **#124**, `ComponentMultiCosetConnected.lean`: the multi-coset
  extension of a single actual B-connected skeleton component is
  itself B-path-connected, for any lower proper alphabet family
  (the empty family case is vacuous).
- **#127**, `ComponentMultiCosetEdgeRange.lean`: in the global
  lower-family multi-CE, a directed edge is in the image of the
  local component morphism iff its signed label is based in B
  **and** its source vertex is in the local vertex image. The
  nontrivial surjection uses separate proofs for completed tagged
  C-edges and old B-labelled skeleton edges.
- **#129**, `ComponentMultiCosetBComponentEdges.lean`: combine
  the exact edge range with the already checked actual B-reachability
  classification (#121). Thus for a nonempty selected family the
  local image is the root's intrinsic B-component on **vertices
  and B-labelled signed directed edges**.

No global Cayley projection is assumed injective; equal ambient
coordinates do not collapse distinct component tags. The result is
a graph-data characterization and injective labelled graph morphism,
not yet a separately packaged type-level EGraph equivalence.

**Next mathematical scope:** the off-skeleton whole-component cluster
property (Definition 3.22), the full conditional Proposition 3.23,
Proposition 3.24 for augmented *full coset extensions*, the rank-two
cluster property, then corrected Section 4/5 inductions. Corollary 3.15's
intrinsic path-component theorem is already checked (#147).
No unconditional PSTS EPPA follows yet.

### 2026-10-09 — actual cluster C-components, tagged singleton supports, selected constituents

**Supersedes** earlier notes that Corollary 3.15 only gives graph-data
slices. PR #147 (clean main port of #145/#146) proves the full real
C-path trichotomy for augmented **ordinary clusters**: meeting, disjoint,
and no-attachment-intersection. The predecessor path/coset lemmas were
integrated through #131/#132/#134/#137/#144. The proof uses genuine
signed directed-edge paths and does not infer connectivity from ambient
coset equality alone. PR #154 additionally upgrades Corollary 3.13's
ordinary-cluster component intersections to intrinsic (B∩C) paths.

PRs #148/#151/#155 introduce a component-tagged vertex-support API
for full proper-subalphabet multi-coset extensions. Every quotient vertex
has an inclusion-least supporting alphabet and exact tagged support
which maps to all its other presentations. It has a genuine supporting
alphabet path from a skeleton anchor. This proves the **singleton**
minimal-support observation immediately before Definition 3.22, but
is not the whole-component cluster-property assumption.

PR #153 proves that any selected tagged full B-coset is precisely one
intrinsic B-path component of the global multi-CE, even with other
incomparable alphabets. **PRs #156/#157/#161 are now checked and merged:**
B/C paths between original embedded skeleton vertices reflect to K;
(B∩C)-component tags are determined by the B/C parent-index pair;
and any intersection of two selected complete B/C-coset components
is exactly one intrinsic (B∩C)-component by genuine signed paths.
The source Proposition 3.23 off-skeleton cases remain explicitly OPEN.

**Source-scope correction:** The cluster property is **Definition 3.22**
(two conditions on every off-skeleton B-component). **Proposition 3.23
assumes that property** and derives connectivity of nonempty B/C-component
intersections; it does not prove the cluster property. The stronger
Proposition 3.24 concerns B-augmentations of **full coset extensions**,
not the earlier Corollary 3.15 about augmentations of ordinary clusters.

The A3/A4/A5/C1 gates and unconditional PSTS EPPA are not yet proved.


### 2026-10-09 — rank-two base and first unrestricted-rank component alternatives

This supersedes the earlier description of the rank-two cluster
property as unformalized. The actual-path base for |A|≤2 is now
certified on main (#172): every full proper-family B-component is a
completed tagged full B-coset or a singleton with one least whole-
component tagged support. The proof supplies low-rank admissibility.

For arbitrary rank, #175 identifies the completed B∩C-edge patches
of any off-skeleton B-component avoiding all selected C⊇B,
with **strict** B∩C ⊊ B. PRs #178 and #180 establish, in genuine
tagged B-path geometry, that a component meeting any selected
C⊇B is a *whole* complete B-coset with the same C tag.
All three are merged after green full Lean CI and axiom audit.

The complementary pointwise criterion is now likewise
Lean-certified and merged (#181, clean port of source #179): selected
C-support is invariant along true B-paths for B⊆C, so one root
vertex's lack of every selected C⊇B support suffices for the whole
component's strict lower-rank edge-patch cover.
Most importantly, the lower-rank patch cover does **not** imply
the missing higher-rank common-core/lower-cluster alternative
or uniform whole-component minimal tagged support. Thus the
source Definition 3.22 cluster property, complete Proposition 3.23
and 3.24, corrected Sections 4--5, and the unconditional PSTS EPPA
statement remain explicitly open.


### 2026-10-09 — PSTS-targeted scope and latest certified structural checkpoint

The final deliverable is ordinary finite PSTS EPPA for CLOSED embeddings,
not unrestricted ABO as a separate result. The finite fibre-MAX ->
PSTS EPPA transfer (Gate T2) is already certified. The minimum
remaining group result is the Cayley-GRL specialization on Cay(Q,P),
including left Q-translation equivariance, minimum-content/retraction,
and content-reduced Cayley paths with the same group value and endpoints.
This suffices for the concrete H ≤ G ⋊ Q fibre-MAX construction and
instantiation of Gate T2. General arbitrary-graph Lemma 2.5 is an
optional intermediate method, never an independent scope requirement.
Follow the project advice archive and independently audited
repairs R1–R8 rather than uncritically the printed paper.

Green-main checkpoint: #183/#188 rank-one B-component and least
singleton support; #186/#194 exact maximal-constituent exit geometry;
#195/#198 coatom support and root no-large criterion;
#200 tagged coatom edge cover and pairwise skeleton anchors;
#202/#205/#206 exact coatom/full-labelled-graph and path equivalence;
#207/#210/#216/#217 exact lower patches and B∩C coatom component
slices, explicit nonautomatic bridge-freeness interface/transfer;
#219 universal tagged skeleton anchor for every presentation of
ONE vertex.

OPEN: the whole-component common-core/cluster property, corrected
Sections 4–5 needed for Cayley-GRL, finite fibre-MAX and unconditional
PSTS EPPA. No broader ABO claim follows automatically.

### 2026-10-09 — authoritative C1/C2 restart (supersedes the earlier open-C1 notes)

The latest **green main** is merge commit `d874283` (PR #241; complete
GitHub Actions Lean build and permitted-axioms audit succeeded). This
checkpoint is substantially newer than the preceding A2-only summaries.

**Green-main PSTS/Cayley steps:**

- #222/#226/#228: selected partial words agree with auxiliary
  total-permutation values, actual Cayley left-Q symmetries, and the
  positive-edge traces of SIGNED paths (negative edges use the positive
  edge at the inverse-step endpoint).
- #230/#231: the actual finite generated permutation subgroup
  `Q ≤ Perm(V)ᵒᵖ`, its complete oriented Cayley graph
  `Cay(Q,PartialAut A)`, word-representability of every Q element,
  and exact signed-word endpoints.
- #234: the genuine *PSTS Cayley path-inclusion lemma*: equal Q
  endpoints and contained positive-edge traces imply the correct
  restriction inequality between partial words, even with inverse
  letters and degenerate generators.
- #237: an explicitly named finite H content-minimal certificate
  yields fibre-MAX. This is CONDITIONAL, not the reflecting-group
  existence theorem.
- #239: construct total permutation lifts of ALL partial PSTS
  automorphisms and a finite closed-EPPA witness conditional on
  that ONE finite Cayley content certificate.
- #241: `AllPartialAutFinite.lean` proves the FULL generator alphabet
  `PartialAut A` and positive edge alphabet `Q × PartialAut A`
  are finite; `CayleySemidirectWordValue.lean` proves the
  complete signed formula for path values in `G ⋊ Q` under
  only left-Q equivariance. This was merged after green CI.

**Current independent candidate work (NOT yet green-main):**

- #242: pairwise intersection-content reduction for same-H-value
  paths implies a globally minimum-positive-edge-content word,
  and hence the existing fibre-MAX interface. CI is the gate.
- #243 (stacked on #242): start from an ACTUAL finite Q-equivariant
  reflecting group G on positive Cayley edges, construct
  `H = ⟨(edge(1,p),generator(p))⟩ ≤ G ⋊ Q`, deduce pairwise
  H-fibre reduction and therefore fibre-MAX; express the
  conditional full-PSTS EPPA theorem directly from reflecting G.
  CI is the gate. These are reductions, not existence proofs.

**One genuine remaining mathematics problem:** construct a finite
Q-equivariant Cayley edge group `G` satisfying same-G-value,
same-Q-endpoint path reduction with positive-edge content in the
intersection of the two original traces. This is the specialised
corrected ABO finite group-reflection theorem. The preexisting A2
geometry is substantial, but whole B-component common core
(Definition 3.22) and the repaired Section 4/5 induction are not
yet available; vertexwise anchors and strict lower edge patches
do NOT give those theorems for free. General arbitrary-graph
Lemma 2.5 or F-inverse covers remain optional proof methods,
not independent formalisation deliverables.

**Discipline:** only promote #242/#243 and subsequent gates after
complete CI and axiom audits; do not conflate the conditional
closed-EPPA theorem with unconditional finite PSTS EPPA.

### 2026-10-09 — C2/C3 finite-reflection bridge (supersedes earlier C1/C2 checkpoints)

The latest code checkpoint here is main merge `a84a802`, after
independently green full Lean CI and permitted-axioms audits for each
integrated PR.

- **#243**, `CayleyReflectingSemidirectToMax.lean` and
  `CayleyReflectingToEPPA.lean`: from an *explicit finite* group G
  carrying a left Q-action, edge generators E = Q × PartialAut(A),
  and **pairwise Cayley path reflection**, construct the actual finite
  subgroup H ≤ G ⋊ Q generated by the selected lifts. Prove signed-word
  surjectivity onto H, projection to Q, the exact signed semidirect
  word-value formula, H-fibre pairwise reduction, fibre-MAX, and a
  concrete finite closed EPPA witness for **ALL** partial automorphisms.
  This is conditional; no reflecting G is constructed.
- **#246**, `CayleyOneEdgeDeletionToMax.lean`: single-edge
  same-H-value positive-edge deletion implies pairwise intersection
  reduction by finite support-cardinality descent, and conversely.
  Together with #242, the one-edge deletion interface suffices for
  finite PSTS EPPA. The local deletion itself is not yet constructed.
- **#247**, `CayleyEdgeWords.lean`: translate signed Cayley P-paths
  to their real signed E = Q × P **edge words**; prove exact evaluation
  in any group G and exact unsigned-positive-edge trace. A negative
  P-letter must use the positive edge based at q·gen(p)⁻¹.
- **#248**, `CayleyEdgeRetraction.lean`: if the E-labelled group is
  retractable, a competing same-G-value path avoids e, and u is the
  original path, deleting e (both signs) from the literal signed E-word
  of u preserves the exact final G-value. **This erased edge word need
  not be an actual path.**
- **#249** (`RetractableGroupContent.lean`, merged as `a84a802`):
  formalizes the source's purely algebraic Proposition 3.5. For any
  finite generating alphabet, generatedness plus retractability gives
  a **realized, inclusion-least generator content** for every group
  element. The complete Lean build and permitted-axioms audit passed.

**Remaining geometric hard gate:** construct finite G, its coherent
left-Q action and retractability, and prove the endpoint-preserving
replacement of a raw E-word after deletion by an actual Cayley path
with the same group value and no new positive edges. The corrected
ABO Lemma 5.6 proves this using the Section 4/5 coset-extension
induction and stability. The current A2 component/coatom/anchor
results do NOT themselves prove the missing whole-B-component
cluster property or bridge-free induction. Source repair obligations
R1--R8 remain active, particularly the k=1 base and full-coset
alternative. Do not conflate group-content minimization with
same-endpoint *path* minimization or conditional EPPA with the
unconditional target.

### 2026-10-09 — source-exact Section 5 / Lemma 5.6 continuation (green main a7e6383)

This section supersedes earlier descriptions of R1 and Corollary 5.7
as unformalized; **the final reflecting-group existence is still open**.

Certified and merged after independent full Lean builds and permitted-axioms
audits:

- **#251** (`EndpointContentReduction.lean`, 4008101): corrected
  Corollary 5.7, assuming the *separately named* endpoint-preserving
  one-edge path replacement theorem. Minimal support-cardinality descent
  yields a REAL path with identical endpoints, exactly the same FINAL
  group value, and positive support **equal** to the canonical group
  content. Empty content forces equal endpoints. Does NOT prove the
  one-edge geometric deletion lemma.
- **#252** (`StabilityRetractability.lean`, 6f2d7ba): the missing
  algebraic R1 implication in corrected Theorem 4.7:
  k-stability of G→H plus (k+1)-retractability of H gives
  (k+1)-retractability of G. Includes a∉A, k=0, total-alphabet
  specialization, and composition of k-stability down quotient chains.
- **#254** (`CayleyStageProjection.lean`, 3cb95c8): a labelled
  homomorphism from the final group G into the transition group of a
  complete stage gives an actual Cayley graph projection based at
  any vertex. Equal FINAL G-word values have the SAME projected
  terminal stage vertex, without map injectivity. The existence
  of that labelled hom at each required stage is not established.
- **#255** (`SelectedCosetStablePathReplacement.lean`, a7e6383):
  if a B-labelled path joins two embedded skeleton vertices in the
  selected complete B-coset constituent of an admissible multi-CE,
  the earlier A2 theorem reflects it to a genuine skeleton B-path.
  The two paths have equal intermediate H_k-values by same-endpoint
  Cayley mapping, and k-stability on |B|≤k upgrades their equality to
  the FINAL G-value. This is the actual C4/C5 step of Lemma 5.6
  and uses no global CE→ambient Cayley injectivity.

Further current branches, not yet accepted until CI and merge:
- **#256** (`CayleyCoherentAction.lean`, merged as `466d38e`):
  generator uniqueness in any E-generated group forces individual
  extensions of left Q-translations to satisfy the action laws;
  constructs the coherent hom Q→*MulAut G and proves uniqueness.
  Complete Lean build and permitted-axioms audit passed. **The
  existence of the individual automorphisms and finite G is OPEN.**
- **#257** (`SynchronizedLabelledGroups.lean`, merged as `d2e2e3a`):
  an actual finite subgroup of a product of two E-generated finite
  labelled groups, generated by paired generator values, with
  explicit surjective label-preserving quotient maps to both factors
  and exact signed-word evaluations. Full Lean/axiom CI passed.
  Identification with the transition group of a literal disjoint
  union of complete E-graphs and the full finite tower is OPEN.

**Remaining mathematical content of Section 5 and Lemma 5.6:**
construct the actual finite tower G₁←H₁←G₂←⋯, the H_k-cover
skeleton and complete coset extension, the final-G projection to
its trivial completion, stagewise ranks/stabilities and the
source's repaired k=1 Proposition 5.4. The higher-rank
whole-component cluster/bridge-free induction (Def. 3.22,
Props. 3.23–3.24, Thms. 4.5/4.7) remains OPEN. Then the
green-main Lemma-5.6 bridges + one-edge deletion + Corollary 5.7
can complete the finite Cayley reflecting-group theorem, H⋊Q/MAX,
and finite PSTS EPPA. Do NOT label the conditional final PSTS theorem
as unconditional or treat independently audited source proofs as
Lean-certified.

### 2026-10-10 — verified finite-stage disjoint transition groups and paired coset edges

**Supersedes** the older note above claiming that the transition-group /
synchronized-subgroup identification is OPEN. Main at this checkpoint is
`07d28a0`, after complete green PR CI and allowed-axioms audits of
the substantive modules below. The post-merge main CI may run separately.

- **#259** (`RankOneRetractability.lean`, `4c629d1`):
  every labelled group is rank-one (and rank-zero) retractable,
  including all signed inverses, degenerate labels and singleton
  alphabets. This proves the elementary starting claim of local
  repair R2, NOT the hard 1-stability G₂→H₁ of Proposition 5.4.
- **#260** (`DisjointUnionEGraphs.lean`, `9117d3a`):
  literal disjoint unions of arbitrary E-graphs and of complete
  E-graphs, with exact formal inverse directed edges, complete
  signed paths and the no-cross-component property.
- **#261** (`TransitionDisjointUnion.lean`, `07d28a0`):
  a FULL GROUP ISOMORPHISM between the transition group of
  the literal disjoint union of two complete E-graphs and
  the synchronized subgroup generated by paired transition
  generators in the direct product of the two component
  transition groups. This is not merely an informal analogy
  or a conditional interface; actual chronological RIGHT
  permutation actions, bijection and group law are checked.
  Repeated/trivial/loop labels require no injective generators.
- **#262** (`WeakCompletePairedEdges.lean`, `bf9c850`):
  every edge of a weakly complete tagged multi-coset E-graph
  has a companion edge with the INVERSE SIGNED LABEL at the
  SAME SOURCE, because its selected full coset constituent
  is complete on that unsigned label. Thus outgoing +i/-i
  at a vertex are simultaneously present or absent.
  This is an actual, nonautomatic structural invariant.

**Two currently running candidates, NOT main-certified:**

- **#263**, stacked atop #262 and retargeted to main:
  `TrivialLoopCompletion.lean` uses paired outgoing signs to
  extend each partial transition by identity fixed points,
  yielding a complete action E-graph on the SAME vertices,
  an injective labelled graph morphism from the old E-graph,
  and only LOOP edges for previously missing signs.
- **#264**, stacked on #263: reflect every genuine
  B-labelled path in this trivial loop completion back to
  a genuine B-labelled old-graph path by deleting only newly
  added loops. Includes B=∅. CI required independently.

**Mathematical priority:** use these complete finite stage
objects in source Definition 5.3 / Proposition 5.4, particularly
the corrected k=1 R2 base and then the whole-component
cluster-property / bridge-freeness Section 4 induction.
The finite reflected group G, its actual stage tower and
the endpoint-preserving geometric Lemma 5.6 are STILL OPEN.
Do not confuse the synchronized transition-group isomorphism
with the full reflecting-group existence theorem.

### 2026-10-10 — canonical trivial-loop stages and rank-two R2 progress

**Authoritative CI-green main at this checkpoint:** merge
`36d42a0` (updating earlier 2026-10-10 checkpoints).
These statements were each included after successful full Lean
compilation and permitted-axioms audit on the corresponding PR:

- **#263** (`TrivialLoopCompletion.lean`, merge `71bfd8e`):
  under LOCAL PAIRED ±-generator availability, complete the
  original EGraph by keeping its vertices and all existing
  signed transitions, fixing a vertex when a signed transition
  is missing. The resulting positive/negative maps are actual
  inverse permutations. The graph inclusion is injective on
  genuine old directed edge tokens. **Every new edge is a loop.**
  Pairing is itself verified for actual weakly complete coset
  extensions in #262; it is NOT automatic for arbitrary EGraphs.
- **#264** (`TrivialCompletionPaths.lean`, merge `5aaffcc`):
  the literal loop completion preserves and reflects
  **every** B-labelled path-reachability relation for all B,
  by deleting exactly the newly inserted loops from real
  completed paths. This includes B=∅ and reverse letters.
- **#267** (`CompletedFullCosetStage.lean`, merge `d481438`):
  construct a genuine complete action EGraph on the SAME
  tagged multi-coset vertices. For the all-proper family and
  |A|≥2, B-connectivity BETWEEN EMBEDDED ORIGINAL SKELETON
  VERTICES agrees exactly with intrinsic skeleton B-connectivity
  for every proper B⊂A. This is not yet a statement about
  all off-skeleton vertices of augmented extensions.
- **#269** (`RankTwoSingletonEdgeDichotomy.lean`, merge
  `0032853`): in a rank-two full proper multi-coset
  extension, every signed edge with base generator i
  has source in a selected complete tagged {i}-coset.
  A vertex outside the {i}-coset images has NO old
  +i or -i edge. The conclusion uses literal tagged
  edge representatives, not an unjustified globally
  injective ambient Cayley projection.

**Further certified and merged after full Lean/axiom CI:**

- **#266**, `0ab7e5a`: finite signed label alphabet and
  actual finite transition groups of complete E-graphs
  on finite carriers, including noninjective/trivial generators.
- **#268**, `57201f3`: k-stability is equivalent to its
  group-word kernel test on each ≤k alphabet; nontrivial
  complete-EGraph word values move an actual vertex.
  These are exact criteria, not a proof of tower stability.
- **#270**, `a2579c0`: the already-certified rank-two
  full B-coset OR singleton dichotomy is preserved under
  the ACTUAL trivial loop completion, for all selected B.
- **#271**, `36d42a0`: in the completed rank-two full coset
  stage, any B-supported word of ambient group value 1
  fixes EVERY vertex. This proves the unaugmented
  full-coset word-kernel ingredient of R2, not all of G₂→H₁.

**Independently active candidates, pending CI:**

- **#273**: construct a real loop-completed stage for literal
  augmented clusters (Definition 5.3 Z₁ type 1), with
  paired sign availability and unchanged all-C reachability.
- **#274** (stacked on #273): every ambient identity-valued
  singleton-supported word fixes the action of a complete
  AUGMENTED cluster stage, using the genuine full-coset
  versus no-old-edge alternative. Do not mark accepted
  before its own full Lean build and axiom audit.

**OPEN substantive obstruction:** complete the finite ABO
tower, including H₁, Z₁ augmented objects, their actual
transition groups and 1-stability G₂→H₁ (R2); prove the
higher-rank whole-component cluster property / bridge-free
induction and source-corrected endpoint-preserving geometric
path replacement. Main's conditional Cayley reflecting-group
⇒ fibre-MAX ⇒ PSTS EPPA chain is Lean-certified, but the
existence of the reflecting group is NOT.

### 2026-10-10 — augmented-cluster R2 kernel and indexed stage assembly

This milestone supersedes the preceding note that #273 and #274 were pending.
PRs **#273–#278** all passed their complete Lean build and allowed-axioms
audit and are merged into `main`. The post-merge `main` build is checked
separately; green PR builds must not be confused with a non-existent
unconditional PSTS EPPA theorem.

- **#273 / `AugmentedClusterTrivialStage.lean`**: a genuine loop-only
  complete action on each actual augmented-cluster graph, with original
  signed-path reachability exactly preserved for every subalphabet.
- **#274 / `AugmentedClusterSingletonKernel.lean`**: for every vertex and
  singleton label, either a real complete containing full coset exists,
  or no corresponding old signed edge exists. Hence any singleton-supported
  word of ambient group value 1 fixes every vertex of that completed
  augmented-cluster stage. This is the corrected R2 type-(1) kernel ingredient.
- **#275 / `SynchronizedProductStability.lean`**: if two generated
  labelled groups map k-stably to the same target, their concrete
  synchronized subgroup admits a k-stable labelled quotient.
- **#276 / `DisjointStageWordKernel.lean`**: identity-valued transition
  words on a literal disjoint union of two complete graphs are exactly
  the words trivial on both summands.
- **#277 / `DependentDisjointStages.lean`**: for a possibly dependent
  family of complete graphs, the action graph on the sigma-type of tagged
  vertices follows signed words componentwise; its identity word kernel
  is exactly the intersection of every component word kernel. This
  action re-encoding need not literally preserve old edge-token types.
- **#278 / `TransitionGroupGenerated.lean`**: the actual transition
  subgroup of a complete graph is generated by its labelled
  transition-subgroup generators, including repeated/trivial labels.

**Still open:** Source Proposition 4.4's rank-two **cluster property**
(not merely admissibility), augmented **full coset extensions** and their
Proposition 3.24 singleton-component cases, the actual finite
Definition-5.3 family `Z₁`, and the quotient/stability proof
`G₂→H₁` at rank one. Higher-rank whole-component cluster property,
Theorems 4.5/4.7 and finite reflection also remain open. Do not
identify the assembled action or word-kernel lemmas with the completed
ABO tower or with unconditional EPPA for PSTS.


### 2026-10-10 — CERTIFIED full rank-one word kernel on genuine rank-two type-(2) completed stages

**Authoritative merged checkpoint:** #299, main merge commit `89ea31c4`.
Its actual GitHub Actions run `38051990893` succeeded for the complete Lean project and
permitted-axioms audit. Main CI after the squash merge is checked separately.
This update SUPERSEDES the preceding 2026-10-10 notes which describe type-(2)
augmented full coset extensions and the exact rank-two cluster-property base as OPEN.

The geometric and action-kernel progression, all integrated into `main`:

- **#280, #281, #282, #285**: the true rank-two multi-CE off-selected-B
  vertex has NO original B-signed edge, even a loop; the literal
  deterministic full B-coset gluing and canonical old/new labelled
  morphisms exist. The off-skeleton rank-two B-component is exactly a
  singleton with its unique least component-tagged core support (source
  Definition 3.22), not merely two-letter admissibility.
- **#283, #284, #286, #287, #288**: legal trivial-loop completion of
  singleton type-(2) gluing, attached-coset identity-B-word kernel,
  exact C-path preservation for C disjoint B, original off-root B-path
  preservation, and *completed action* transport for B-supported words
  at every old off-root vertex. All of these individual PRs passed Lean
  and axiom CI before merge.
- **#299 (incorporating exact modules from #289–#298)**: the whole
  singleton type-(2) augmented stage now has the full **rank-one
  word-kernel property**. The case split is an essential audited point:
  for EVERY `C : Finset ι` with `C.card ≤ 1`, if a signed word `w`
  uses only `C` and `SignedWord.evalGroup gen w = 1`, the actual
  `rankTwoOffComponentCompletedStage` follows `w` to the SAME vertex
  for EVERY old and fresh vertex. Its genuine transition-group
  `wordValue w` therefore equals identity.
  For `C ⊂ A`, the rank-two proper-alphabet dichotomy treats the
  newly attached B and C disjoint B cases. For `C ∩ A = ∅`,
  the all-proper multi-coset quotient's actual raw edge labels and
  the new attached B-edges lie in A, hence outside-A signed labels
  act ONLY via new loops, irrespective of ambient group values.
  The elementary `|A|=2`, `|C|≤1` dichotomy ensures exhaustiveness.
  The underlying 11 source files are present in `main` with Git
  blob SHAs matching the checked #299 branch. The duplicate component
  PRs #289–#298 were closed as already integrated by #299.

**Exactly what is NOT proved:** this is a genuine completed type-(2)
**singleton off-component stage** over an already supplied finite-group
skeleton. It is not a construction of the finite labelled H₁-cover,
the full source Definition-5.3 family Z₁ of all required stages,
nor an actual labelled quotient `G₂→H₁` with `1`-stability.
Type-(1) augmented-cluster kernel (#274) and ordinary full-CE
kernel (#271), and dependent-stage disjoint action assembly (#277),
remain separately certified inputs. Higher-rank cluster geometry,
bridge-free Section 4 induction, finite reflecting group and final
unconditional PSTS EPPA remain OPEN.

**Pending, NOT yet certified:** #300, `FiniteRankTwoType2Stages.lean`,
aims to show finiteness of the concrete tagged quotient, completed
augmented carrier and transition group when Γ is finite; its first CI
failed at explicit `Finite` instance synthesis, and the revised
branch is awaiting its own independent CI. A failed or pending CI
must NOT be recorded as a formalized result.


### 2026-10-11 — Authoritative #334 checkpoint and human geometry falsification

**Repo main at cut-off:** `509636b86531f7d8c43b1ab274dcdf3c1800e0cd`,
with **successful post-merge full Lean and allowed-axioms CI**
(run `38078483414`). The older entries above (including
"\#300 pending") are HISTORICAL and are superseded by the
later successful main merges.

**Certified integrated stages:**

- `#300–#318`, `#322`, `#325`: actual finite rank-two
  completed stage geometry and singleton word kernels; genuine
  ambient/coset slices; pullbacks of existing incomplete Cayley
  skeletons along labelled quotients.
- `#328`: finite generated low-rank group chain
  `G₂ ↠ H₁ ↠ Γ`, each quotient 1-stable, the new groups
  2-retractable, actual finite H₁ graph pullback with signed
  path lifting.
- `#329`, `#331`: any connected labelled morphism between
  **already Cayley-embedded** skeletons is a translated quotient
  map on each intrinsic component, and its component injectively
  factors through a translated canonical pullback with exact
  vertex and directed-edge commutation.
- `#334`: for each `k`, the actual finite synchronously
  generated group
  `H_{k+1} ≤ Γ × ∏_{|A|≤k} Γ[A]`
  is `(k+1)`-retractable without requiring `k`-retractability
  of `Γ`. If `Γ` is generated and `k`-retractable, the
  quotient `H_{k+1}↠Γ` is `k`-stable.
  This is an **ALGEBRAIC** rank lift, not a proof of geometric
  cover or source full stage-family completeness.

**Critical human counterexample / STOP SIGN:**
See [ABO_HUMAN_GEOMETRY_SHORTCUT_AUDIT_2026-10-11.md](ABO_HUMAN_GEOMETRY_SHORTCUT_AUDIT_2026-10-11.md).
For `Γ=C₂×C₂` and the admissible two-letter Cayley path
`1 —a— a —b— ab`, the full proper-alphabet coset extension
contains two different points of ambient coordinate `b`:
true paths `b` and `aba` have distinct endpoints even though
their group values coincide. The completed extension has five
vertices; the ambient Cayley group has only four.
Since `Γ` is already retractable, the detector-based rank
lift `H_{k+1}` is actually isomorphic to `Γ` and cannot
cover this completed extension. Thus **retractability and
k-stability alone cannot replace the geometry of augmented
coset-extension stage action**. Our rank-two augmented
transition stages may still distinguish the two endpoints.

**Remaining mathematical gates, in order of risk:** prove
Cayley covers of the **exact source-indexed**
`Y_k/Z_k` completed stages, including plain `B=∅`
full extensions and all prescribed augmented variants;
derive global higher-rank admissibility, cluster property,
and bridge-freeness without using the embedding in advance;
carry equivariance and reach corrected ABO reflecting-group
existence. Only then discharge the already certified
conditional Cayley-content → PSTS-EPPA transfer.

**Avoid circular use:** #331 requires both graphs to already
embed in Cayley graphs; a coset extension may fail to embed.
The next best human falsification test is the signed-word
kernel of each required completed stage, **not** merely
component surjectivity of existing embedded pullback maps.


### 2026-10-12 — Source-rooted rank-two multi-coset EGraph isomorphism CERTIFIED

**Authoritative integration cutoff:** main merge commit `eb1e10fa1b5a49d00ce318025d02bc0673628009` (#390).
The source branches #385/#386/#387 each passed a full Lean build, the independent 256-original-edge-pattern ABO regression and the allowed-axioms audit. The exact final theorem blobs were then assembled unchanged in clean #390, whose own full CI was also green before merge. A *separate post-merge CI run* must be checked before calling this particular main revision post-merge green.

**New integrated source-facing declarations:**

- `PSTSEPPA/ABO/RootedSourceMultiCosetVertexQuotient.lean` (#380): `rootedLocalMultiCosetVertexQuotientEquiv` transports the **literal** component-tagged intersection-supported vertex gluing quotient from the genuine A-rooted source component to the local Γ[A] representative. Assumes `A.card = 2` and `KRetractable gen 2`, **not** global retractability of Γ.
- `PSTSEPPA/ABO/SourceLabelEdgeQuotientNaturality.lean` (#378) and `SourceLabelEdgeQuotientGraphIso.lean` (#390): the exact edge quotient is by **equal glued source plus equal signed label**, never merely equal ambient Γ-edge coordinate. Under honest bijective source/edge maps and explicit target congruence, the quotient EGraphs are isomorphic and reflect all genuine signed paths.
- `RootedSingleCosetEGraphHom.lean`, `RootedSingleCosetEGraphIso.lean`, `RootedMultiCosetRawEdgeEquiv.lean` (#384): actual vertex-and-directed-edge-bijective signed isomorphisms of single-B completions for B⊆A, and a component/alphabet-tag-preserving equivalence of **all raw oriented signed edges** of a multi-coset family.
- `RootedMultiCosetRawGraphNaturality.lean` (#390): exact source/local RAW multi-coset signed graph isomorphism over the genuine glued vertex quotients, preserving source, inverse edge and full signed labels.
- `RootedSourceMultiCosetCompletedEGraphIso.lean` (#390): `rootedLocalMultiCosetRawGraph_target_congruent` is derived from the **local Γ[A]** retractable construction; `rootedAmbientMultiCosetRawGraph_target_congruent` transports it to the original source component. `rootedMultiCosetCompletedEGraphHom_bijective` gives an actual signed labelled EGraph isomorphism on all glued vertices and directed edge classes; `rootedMultiCosetCompletedEGraphHom_follows_iff` preserves and REFLECTS every truly realised signed path. These results apply to any proper-alphabet family `P : CosetFamilySpec A`, provided `A.card = 2`, `KRetractable gen 2` and a genuine rooted A-component.
- `RootedSourceOffCosetIndexEquiv.lean` (#389): `rootedLocalMultiCosetOffCoset_iff` exactly preserves/refects the source type-(2) condition that a selected old quotient vertex lies outside the *entire component-tagged B-coset constituent*, including degenerate B, rather than testing its ambient coordinate.

**Do not overstate this checkpoint.** The constructed source EGraph is the **plain** multi-coset extension, not the full corrected Definition-5.3 source stage catalogue. The source's outside-alphabet legal fixed-loop completion and B-coset **augmentations** have not yet been transported as complete signed EGraphs; exact matching of ALL source Z₁ stages to the finite G₂ local supercatalogue is NOT proved. Subsequent corrected Condition 5.2 / Theorem 4.7 (admissibility, embeddedness, cluster and bridge-free geometry), higher-rank Yₖ/Zₖ induction, reflecting group and unconditional ordinary PSTS EPPA remain **OPEN**.

**Pending independent CI / active frontier (NOT integrated):** #388 legal trivial-loop completion naturality, #391 signed-edge availability and locally-paired transport, #392 local all-proper multi-CE pairing, #393 true fresh B-coset point equivalence, #394 exact ambient value of the source-glued quotient. Treat every statement in those PRs as a CANDIDATE until its specific latest head passes the full project and axioms CI, and then integrate only the checked code.


### 2026-10-12 evening — Certified TRUE source completed actions and first augmentation carriers

**Main integration cutoff:** `120cdf48e1baf864d42a998ae49775544cebacee` after green PRs #396 `aa5791ca`, #393 `e11cf7a3` and #394 `120cdf48`, in addition to #388 `2839bd04` and #391 `6b94957e`. Each individual PR passed the entire Lean build, 256-case source regression and permitted-axioms audit **before merge**. A separate post-merge full CI run on this latest main head must be checked independently. This update **supersedes the interim pending-status sentences in the preceding October 12 checkpoint**; it does not change their claims at their earlier cutoff.

**CERTIFIED and on main:**
- `TrivialLoopCompletionIsomorphism.lean` (#388): any vertex- and oriented-edge-bijective morphism of genuine incomplete EGraphs with paired opposite signed availability induces a vertex- and edge-bijective morphism of their LEGAL fixed-loop-completed action graphs. Exact signed path preservation and reflection included.
- `LocallyPairedGraphIso.lean` (#391): signed-edge availability, including inverse labels, preserves and reflects across actual signed graph isomorphisms; paired outgoing signs transport.
- `RootedLocalCosetPairedLabels.lean` (#392, integrated by #396) and `RootedSourceAllProperCompletedStageIso.lean` (#396): the true original H1-rooted `P_A` full proper-coset EGraph satisfies paired signed labels. Its literal complete stationary-loop stage exists and is **isomorphic on vertices, signed directed action-edge tokens and genuine labelled paths** to the local Γ[A] stage, for |A|=2 under only `KRetractable gen 2`. This is the unaugmented full-proper-coset stage, not an assertion about all Z₁.
- `RootedFreshCosetEquiv.lean` (#393): explicit bijection of the **fresh, non-root** points of the attached full B-coset under translation Γ[A]→Γ, for B⊆A, without globally retractable ambient Γ.
- `RootedSourceMultiCosetAmbientValue.lean` (#394): well-defined Γ-coordinate on the TRUE tagged source multi-coset vertex quotient and exact rooted-translation naturality. Equality of ambient values is NOT an identification of tagged quotient points.

**New active research candidates, NOT certified yet:** #397 derives the absence of all OLD signed B-edges at an original source off-B augmentation root (including loops) from the existing rank-two local theorem, using actual signed edge surjectivity. #398 constructs from this premise the literal original-source rank-two **type-(2) B-augmented signed EGraph** and its LEGAL loop-only completed action, with a canonical old-edge embedding. Neither PR should be promoted until its latest head has green complete Lean/axiom/regression CI.

**Remaining hard gates:** explicitly match the FRESH B-coset's signed directed edges, source/target and gluing basepoint, giving a complete source/local augmented-stage EGraph and action isomorphism. Then prove every ACTUAL source Definition-5.3 Z₁ stage (type-(1) and type-(2), B=∅ and nonempty) is represented/covered in the constructed finite G₂ stage family, and discharge corrected Condition 5.2, Theorem 4.7 geometry, later-rank induction and MAX→PSTS-EPPA. None of these downstream conclusions currently follows merely from the completed **plain** stage isomorphism.

### 2026-10-13 — certified input-dependent first-rank G₂ action bridge

**Authoritative checkpoint:** main `717b30aa9b1d54307ef39e428e91fc100d935278` following clean merges #423 and #427. PR #423 and its *separate post-merge main run* are full Lean/256-original-source-pattern/allowed-axioms **GREEN**. PR #427 passed the same independent full checks before merge; its *separate post-merge main run* must be checked independently rather than assumed green.

**Actual Lean-certified scope on main:**

- Original H₁ source type-(2) (B,z) **dependent indices** match exact real local Γ[A] three-family G₂ indices (including empty B), and the real local completed type-(2) action is definitionally the selected catalogue fibre. Do not confuse index equality with completed-action identification.
- The actual finite input-dependent source G₂ Cayley graph has rooted complete signed **word-action cover formulas** for every LOCAL type-(1) augmented cluster and LOCAL type-(2) B-augmented full-coset stage, with old/fresh tags, negative letters and legally completed loops; #423 has been independently verified and merged.
- The LITERAL named original H₁ source B-augmented complete action is heterogeneously equal to its root-translated model after the proven ambient-basepoint equation. The general complete labelled-EGraph isomorphism transports and reflects entire signed-word action congruences. These exact #424/#426 Lean blobs were integrated in independently verified clean #427.

**New proof frontier (candidate, not on green main):** #425 derives equality/identity word-action kernels of the whole local type-(1)/(2) finite-G₂ stage families (initial 200,000-heartbeat proof rewrites were replaced with direct map congruences; final new head awaits CI). #428 proved exact source/local type-(2) whole-word action congruence on its stacked head with full GREEN checks; clean carry #434 awaits its own independent head CI. #429/#431/#432/#433 propose the original Γ[A]↔Γ signed graph and actual type-(1) index normalization; #430 proposes the fibrewise sigma-stage action equality interface. Each candidate needs its own full Lean, 256-case original-source regression and allowed-axioms CI.

**Explicitly OPEN:** complete source Definition-5.3 Z₁ action family coverage; corrected source Condition 5.2 and Theorem 4.7 admissibility/embeddedness, cluster and bridge-free geometry; higher-rank historical Yₖ/Zₖ induction, finite reflecting group, the final concrete fibre-MAX proof and unconditional finite PSTS ordinary EPPA. No generic Cayley pullback is allowed to replace completed stages; original ambient coordinates do not identify distinct component-tagged quotient points.
