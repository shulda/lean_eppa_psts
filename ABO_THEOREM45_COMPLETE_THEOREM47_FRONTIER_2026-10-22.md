# PSTS EPPA Lean — forward ABO Theorem 4.5 completed; corrected upward Theorem 4.7 frontier

Checkpoint: **2026-10-22**, authoritative `main`
[`8738074992b90d7de5c48b3b2c7b1295ed389472`](https://github.com/shulda/lean_eppa_psts/commit/8738074992b90d7de5c48b3b2c7b1295ed389472).
This supersedes the *forward 4.5* OPEN markers in the 2026-10-21 and
earlier historical checkpoint files, without altering the historical record.
This is not the unconditional finite-PSTS EPPA theorem.

## Accepted: full original Γ-facing signed k-local FORWARD geometry

Clean **#890** (full green CI run **39746029629**, whole Lean build, all
256 genuine signed original rank-one edge input-pair regressions and
permitted-axioms audit) merges the source-certified proof on actual
ORIGINAL Γ-rooted old/fresh signed quotient components:

`PSTSEPPA/ABO/ForwardInductionOriginalExactTheorem45.lean`
- `CayleySubgraphSpec.sourceKLocal_originalCanonicalExactSignedWholeClusterProperty`
- For an admissible genuine incomplete signed Γ-Cayley skeleton, a finite
  merely **k-retractable** Γ, a rooted actual C-component with
  C⊆A, **2≤|C|≤k**, all proper B⊊C, assume the genuine lower
  rooted H[C]-component bridge-free premises and original signed
  off-skeleton B-component condition.
- The ENTIRE original B-component has one *attained* original
  old-component-index-tagged minimum; there is one real signed B-reachable
  original quotient core attaining it with genuine original tagged
  support at every original active coatom.
- **FULL branch:** the entire ORIGINAL signed B-component is exactly
  one original component-tagged original Γ-left B-coset in a selected D-copy;
  all its real oriented signed B-component edge tokens are ORIGINAL
  freshly completed D-edges with that very same old D-component index;
  every positive AND inverse signed B-step genuinely exists at each
  original B-component vertex.
- **PROPER branch:** the entire ORIGINAL signed B-component is isomorphic
  as a labelled graph, bijective on original quotient vertices AND BOTH
  oriented edge-token classes, to the CANONICAL original Γ proper B-cluster,
  left-translated by the exact ambient original core coordinate
  `root.1 * localH[C]Core`. No fake missing old edges.
- Actual ORIGINAL active coatom slices are defined intrinsically by
  actual signed paths + original old component-tagged support and were
  proved equal to the transported local finite coatom family by #889
  (independent full green CI).
- The finite globally retractable instance also has its separate
  rank induction theorem and genuine low-rank bases.
- Crucially, no lower *cluster* assumption, no global Γ
  generation/retractability, and no quotient by ambient-coordinate
  equality of distinct original component tags occurs in the proof.

Supporting accepted mathematical interfaces:
`ForwardInductionOriginalFullCosetVertexExact`,
`ForwardInductionOriginalFullCosetGammaExact`,
`ForwardInductionOriginalFullSignedAlternative`,
`ForwardInductionOriginalFullCosetSignedSteps`,
`ForwardInductionOriginalFullCosetSignedEdgeClass`,
`ForwardInductionOriginalTaggedCommonCore`,
`ForwardInductionOriginalActiveCoatomTags`,
`ForwardInductionIntrinsicOriginalActiveCoatoms`,
`ForwardInductionOriginalGammaProperShape`.

Do not overstate **rank 0/1**: the displayed source k-local theorem
explicitly requires `2 ≤ C.card`; keep the separately certified
rank≤2 bases, rather than claim these are discharged by the displayed
high-rank theorem.

## Source of the next task: corrected ABO Theorem 4.7 (UPWARD induction)

Reference: Auinger–Bitterlich–Otto,
[Finite approximation of free groups I](https://arxiv.org/pdf/2208.03273),
published Theorem 4.7, pp. 39–43 (PDF zero-based pages 38–42),
Definition 4.6 and the proofs following it. Read the ACTUAL source before
tightening any of these hypotheses.

The source theorem assumes:
1. `1 ≤ k < |E|`; H is an E-group **(k+1)-retractable**;
   `A⊆E` with `|A|=k+1`.
2. LH is a genuine connected A-subgraph of H[A], admissible for the
   proper-A coset extension; its full CE(H,LH;PA) has the cluster property.
3. A labelled quotient **G→H** is k-stable. Cayley G covers **every**
   graph `CE(H,LH;PA) augmented at v by the FULL B-coset vH[B]`,
   for *every* vertex v of CE(H,LH;PA) and B⊊A, not just the
   UNaugmented CE(H,LH;PA).
4. LG is ANY rooted connected G-cover of LH (Definition 4.6),
   preserving actual signed old path lifting.

The THREE output clauses are separate:
(i) LG admissible for proper-A coset extension;
(ii) actual full CE(G,LG;PA) embedded in G[A] on true signed vertices
     AND both oriented edge token classes;
(iii) that exact embedded CE(G,LG;PA) is B-bridge-free
      for all B⊊A, as real signed path reflection.

**Corrections R1, R7, R8 are mandatory:**
- R1: The proof uses retractability of the SOURCE G at rank k+1.
  `StabilityRetractability.lean` already certifies
  `Q.kRetractable_of_kStable`: k-stable G→H plus H (k+1)-retractable
  implies **G (k+1)-retractable**. Apply it to each genuine local
  generated G[A]/H[A] via
  `retractable_trivialCompletionGenerator_of_kRetractable`;
  do NOT assume global E-wide G retractability.
- R7: correct A₁/A₂ source-index notation in (iii).
- R8: when the H B-component meets the old LH skeleton,
  its **FULL B-coset** branch must be used; it is NOT covered by a
  generic multi-constituent proper cluster. The source proof treats
  skeleton-meeting FULL separately, proper cluster with ≥2 constituents
  and proper single-constituent case separately.

## Preferred Lean dependency / proof decomposition

**(i):** `KStablePullbackAdmissibility.lean` already proves
`pullbackQuotient_admissible_of_kStable`; and
`ForwardInductionLocalAdmissibility.lean` proves
`subalphabetComponentSubgraph_admissible_of_subset` **also for B=A**.
In a pulled-back source Γ A-skeleton, combine them to prove
admissibility for EVERY rooted connected A-component.
Candidate new
`UpwardInductionActualGCoverAdmissible.lean`
is #892, stacked on #891
`UpwardInductionR1LocalGroupPackage.lean`.
**Neither is green/promoted at this checkpoint.**

**(ii):** two collision types in the true signed multi-coset
ambient map, both requiring actual group/stage-cover hypotheses:
(a) same selected B-summand at different old B-components, where
k-stability plus signed old B-path lifting and exact original
B-component tags must identify the true constituent;
(b) mixed distinct selected B- and C-summands. Project to H, use
the source-H coset intersection meeting an ACTUAL skeleton vertex,
lift both B and C paths to one actual G-old ancestor and prove
the witness lies in the common (B∩C)-tagged support; **only then**
identify original quotient vertices. Existing accepted
`KStablePullbackCommonSupportLift`,
`PullbackAttachedCosetSupportReflection`,
`KStablePullbackMultiCosetStageCoverEmbedding`,
`RootedTaggedAttachedCosetEquiv` are useful, but an H
ambient-embeddedness hypothesis must not be silently presumed
from its cluster property. The source's **complete CE-stage G-cover**
is the missing control.

**(iii):** source H signed B-component, with ORIGINAL whole-component
cluster property from #890. Split into:
- B-component meeting LH: **FULL B-coset**; actual G B-cover
  isomorphism returns a real G path in CE(G,LG;PA). This is R8.
- off-skeleton PROPER B-cluster with ≥2 active constituents:
  common core; two lower (B∩Ci)-coset paths; pass through the
  genuine **B-augmentation** of the original H CE at the core,
  not merely the unaugmented CE. Use signed path lifting, k-stability
  and real G word-value reflection to build an honest path using
  the original completed G constituents. Keep old-component tags.
- off-skeleton PROPER case with exactly ONE active constituent:
  prove paths remain in the corresponding existing full selected
  G constituent (the source explicitly treats n=1).
Do not forget the actual edge orientations / inverse tokens and
trivial generator loops on either side.

These clauses, once proved, must be instantiated with the
printed Definition-5.3 selected three-kind source H-stage family
and suitable G finite Cayley-stage cover. Existing first-rank
G₂/H₁ results are partial precursors, not a general upward
Theorem 4.7.

## Later source §5 and final transfer

After Theorem 4.7, still formalize corrected Condition 5.2,
equivariant *selected* historical stages `Yₖ/Zₖ/Xₖ₊₁`,
rank k=1 Proposition 5.4 separately (repair R2),
finite reflecting group / Cayley semidirect pairwise-content
certificate, and finally instantiate
`FiniteEquivariantCayleyReflection.toMaxTransporterExtension`
to derive unconditional finite PSTS ordinary EPPA with closed
embeddings. Do not conflate the existence of that conditional
API with having constructed the required finite reflection.

## Recovery protocol

At the next session check live `main` SHA, latest PR HEADs and exact
GitHub Actions *completed* outcomes. A green stacked mathematical
file is a candidate for clean BYTE-IDENTICAL current-main re-port
with its own independent full CI. Do not merge from stacked branches
onto an obsolete base. Preserve the published theorem source
scope and repairs, do not introduce `sorry` or custom axioms.
