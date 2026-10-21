# PSTS EPPA Lean — certified ABO Theorem 4.5 handoff (2026-10-21)

This document records what **Lean on GitHub main** proves as of squash commit
[`e3e138d5`](https://github.com/shulda/lean_eppa_psts/commit/e3e138d5353a003d0847a23e2f00b35064ee7ebc),
not what remains to be proved from the published ABO paper. Older dated
sections in `FORMALIZATION.md` and `RESEARCH_LEDGER.md` are historical
checkpoints and cannot supersede this one.

## Certified mathematical interfaces

- The specialized conditional PSTS **fibre-MAX → finite ordinary EPPA** witness
  (closed substructures, full partial automorphism extension) is already Lean
  checked in `PSTSEPPA/PSTS/EPPAFromMax.lean`. This remains CONDITIONAL on
  a finite group with the required fibre maxima; the group construction is
  not yet instantiated.
- ABO §§3–4 signed coset extensions use **real, incomplete old signed edges**,
  attached cosets carrying **intrinsic old component tags**, actual word paths
  and BOTH oriented signed edge-token sorts. Ambient Γ-coordinate equality
  must not identify distinct old-component tags.
- [#835](https://github.com/shulda/lean_eppa_psts/pull/835) checks
  `exactSignedClusterProperty_of_allLowerRootedBridgeFree` for finite
  generated globally retractable labelled Γ. The ORIGINAL lower rooted
  bridge-free premise suffices, by rank induction; extra lower cluster
  hypotheses are not assumed.
- [#840](https://github.com/shulda/lean_eppa_psts/pull/840) applies the result
  to normalized locally retractable H[C] from `KRetractable gen k`, for
  `C.card ≤ k`, via `sourceKLocal_forwardExactSignedClusterProperty`.
- [#848](https://github.com/shulda/lean_eppa_psts/pull/848) proves source
  Γ-rooted versus local H[C] **whole** signed B-component bijective graph
  morphisms and reflection of genuine paths, attained original tagged
  support, complete B-component minima and old/off-skeleton conditions.
- [#854](https://github.com/shulda/lean_eppa_psts/pull/854) proves the
  **canonical** signed proper B-cluster graph transport H[C] ↪ Γ, for all
  vertices and oriented edges, with exact root translation.
- [#856](https://github.com/shulda/lean_eppa_psts/pull/856) proves
  `arbitraryRankRootedOriginalBridgeProperty_iff_standardLocal`, exactly
  relating original Γ-rooted two-clause bridge-free to normalized local H[C]
  bridge-free; NO ambient global retractability assumption.
- [#858](https://github.com/shulda/lean_eppa_psts/pull/858), merged
  `4d384922`, upgrades global proper cluster graph shape to the actual
  canonical translated signed Cayley skeleton and strengthens the full
  off-skeleton/whole-component cluster predicate under lower rooted bridge-free.
  Source declarations:
  `allProperCoset_B_component_canonicalTranslatedCluster_signedIso`,
  `canonicalExactSignedWholeClusterProperty_of_lowerBridgeFree`.
- [#859](https://github.com/shulda/lean_eppa_psts/pull/859), merged
  `78b4f5b7`, establishes original Γ-rooted off-skeleton ⇒ standard local
  off-skeleton and derives an **attained original-tagged (D,d) minimum of the
  ENTIRE true B-component** under k-local lower bridgefree:
  `sourceKLocal_originalOffSkeletonBComponent_hasMinimum`.
  The `d` is a genuine old D-component index, not a Γ-coordinate.
- [#861](https://github.com/shulda/lean_eppa_psts/pull/861), merged
  `a0b57033`, formalizes `EGraph.signedBComponent_shape_transport_of_bijective`,
  composing actual signed whole-component isomorphisms on original vertices
  AND both oriented edge tokens. It **reuses**, rather than duplicates,
  `LabelledGraphHom.inverseOfBijective` in
  `PSTSEPPA/ABO/BijectiveGraphPathReflection.lean`.
- [#863](https://github.com/shulda/lean_eppa_psts/pull/863), merged
  `e3e138d5`, shows the **ORIGINAL Γ-rooted** entire true signed B-component
  is isomorphic to a canonical locally translated H[C] proper B-cluster
  in the proper branch. It also proves lower-local-bridgefree ⇒
  (local full-B-coset alternative) OR
  (original Γ signed canonical **LOCAL** proper B-cluster), for actual
  original off-skeleton B-components. The clean mathematical file
  `ForwardInductionOriginalCanonicalProperShape.lean` is byte-identical
  (blob `ec24808ba55bcc0a68cdf99d636dfd16875372ea`) to independent
  CI-green source #862. **This is not yet the final original Γ root-translated
  cluster alternative.**

## Exact CI gate

Each of #858, #859, #861 and #863 passed *on its exact head* an independently
green GitHub Actions `Lean CI`: whole `lake build`, all 256 real signed
old rank-one edge pair input regression configurations, and allowed-axiom
audit. Representative runs:

- #858: [39555298659](https://github.com/shulda/lean_eppa_psts/actions/runs/39555298659)
- #859: [39575046629](https://github.com/shulda/lean_eppa_psts/actions/runs/39575046629)
- #861: [39576227571](https://github.com/shulda/lean_eppa_psts/actions/runs/39576227571)
- #863: [39577452733](https://github.com/shulda/lean_eppa_psts/actions/runs/39577452733)

No project `sorryAx`, custom axiom, fictitious old signed edge, or
collapse of original component indices is permitted. Historical #860
was closed WITHOUT merge: it independently reimplemented an inverse
already present in `BijectiveGraphPathReflection.lean`, causing an
import collision. The reused existing inverse is certified by #861.

## Next mathematical Lean gates (do NOT prematurely mark as completed)

1. **Literal original Γ proper-cluster signed shape.** Under original
   `KRetractable gen k` and its actual rooted component, take the
   H[C]-canonically translated proper cluster from #863 and construct an
   explicit *vertex-and-oriented-signed-edge bijective* isomorphism to the
   corresponding ORIGINAL Γ root-translated proper cluster. The existing
   `ClusterSpec.localSignedTranslatedClusterHomOfParent` is for
   UNTRANSLATED local H[C] cluster. Source original-rooted vs local ambient
   coordinates satisfy `originalValue = root.1 * localValue` by
   `arbitraryRankRootedOriginalMultiCosetValue_natural`.
   Thus translate local center `t∈H[C]` to `root.1 * (t:Γ)` — do NOT
   silently lose the local translation.
2. **True original FULL-B-coset branch.** Transport its *source old C-tagged
   constituent*, whole original B-component signed paths, both oriented
   edge-token completeness and full fibre under the actual tagged quotient
   equivalence. A local full-B-coset result alone is not yet a correctly
   named original Γ result.
3. Assemble complete **original-rooted k-local Theorem 4.5 signed
   whole-component cluster property**: original off-skeleton B-components
   have attained original (D,d) minima, actual signed proper/full shape,
   and support-attaining common tagged core. Do not confuse the local common
   tagged core from #863 with the final Γ-rooted original active coatom tags.
   Use already-certified original/local bridge-free iff, but be explicit
   about whether the premise is local H[C] or original Γ.
4. Corrected **ABO Theorem 4.7** (upward bridge-free/embeddedness step,
   including global retractability scope and full-coset alternative).
5. ABO §5 Condition 5.2, finite reflecting-group construction (with separate
   k=1 base-case repair), the concrete Cayley semidirect fibre-MAX bridge,
   and finally the **unconditional finite closed-PSTS EPPA theorem**.

These are *Lean gaps*, not new mathematical conjectures about the
published proof. ABO I was independently prose-audited with repairs R1–R8;
record and discharge each explicitly.

## Working practice / recovery

After any failed or interrupted interaction inspect `main` branch and
newest commits first, then PRs / exact HEAD workflows. Work in named branches.
A green source stack must be re-ported as a **clean current-main PR**, with
mathematical Lean blobs unchanged and fresh full CI on the CLEAN HEAD before
merging. Superseded stacked PRs can be closed after proving byte-identity.
Do not merge merely because a stacked PR's source CI is green.
