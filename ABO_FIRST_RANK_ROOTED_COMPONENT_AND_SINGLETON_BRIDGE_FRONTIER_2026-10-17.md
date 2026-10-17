# 2026-10-17 — PSTS/ABO first rank: rooted component embedding and singleton bridge frontier

## Authoritative verified cutoff

> **Same-day mathematical addendum.** Subsequent to the a16bb415 cutoff below,
> [#651](https://github.com/shulda/lean_eppa_psts/pull/651) independently passed
> exact-head full Lean/256 real signed-input regression/axioms CI
> [39028791397](https://github.com/shulda/lean_eppa_psts/actions/runs/39028791397)
> and was merged as **1da3ac56397a6603b4e21294ec07118cd916bad1**.
> It proves exact signed B-word displacement in genuine type-(2) added full B-cosets,
> the converse B-word return iff identity, and a B-stable G→H *old-image orbit detector*.
> The detector requires both compared G group points to map to actual OLD augmentation
> vertices (first exactly the attachment root), and DOES NOT establish
> this source-specific OLD-image compatibility for the entire selected G[A] component.
> Work-in-progress [#650](https://github.com/shulda/lean_eppa_psts/pull/650)
> and [#652](https://github.com/shulda/lean_eppa_psts/pull/652) respectively address
> the full-constituent saturation/off-B-only reduction and rooted path compatibility.
> On every restart check latest main and exact green PR heads, not this fixed addendum.


GitHub main at this checkpoint: **a16bb415ca8065f9519f0a649506fd194b3a998b** (merged #648). Always check GitHub anew on restart; this dated SHA is not automatically the latest.

Accepted, merged results, each with independent exact-HEAD full Lean project compilation, 256 genuinely signed original-input edge-pair regressions and configured axiom audit:

| PR | Accepted verified HEAD CI | Result |
|---|---|---|
| [#646](https://github.com/shulda/lean_eppa_psts/pull/646) | [39019134898](https://github.com/shulda/lean_eppa_psts/actions/runs/39019134898) | Unconditional **component-scoped** G[A]/H[A] rank-two rooted full multiCE ambient vertex injection |
| [#647](https://github.com/shulda/lean_eppa_psts/pull/647) | [39024227791](https://github.com/shulda/lean_eppa_psts/actions/runs/39024227791) | Rooted signed edge injection; no empty-B bridges; rank-two relative bridge reflection iff intrinsic B-tag alignment |
| [#648](https://github.com/shulda/lean_eppa_psts/pull/648) | [39024824807](https://github.com/shulda/lean_eppa_psts/actions/runs/39024824807) | The whole old+fresh selected attached region is EXACTLY one intrinsic A-connected component, closed on actual signed edge targets |

Post-#646 independent main CI [39023471953](https://github.com/shulda/lean_eppa_psts/actions/runs/39023471953) was also GREEN. The separate post-#648 main run must be checked before claiming its result. Exploratory stacked #645 is superseded by clean merged #646 and closed.

## Precisely what is proved

Use the actual first-rank original-input-derived finite labelled quotient G=T(X₂^all) onto H=T(Y₁), restricted to genuine local G[A] onto H[A] for |A|=2. The quotient is only ONE-stable, which ensures stability on each proper B⊊A (empty or singleton), not on all of A. The generated local groups are globally retractable.

The selected H[A] old skeleton is literally the one true original incomplete signed A-component based at the printed old H root, inverse-translated into H[A]; the G[A] skeleton is the genuine signed Q_A pullback, potentially disconnected. Select the actual G[A] old identity component. The corrected plain P_A extension uses authentic intrinsic component-indexed old/fresh cosets, exact common-intersection gluing, oriented signed edge token quotient, and legal insertion of stationary loops only at missing signed labels.

The FULL signed Cayley(G[A]) cover of the original normalized H[A] P_A complete stage exists and is based at EXACTLY the component-tagged old root. The based-cover conditions, all proper-subalphabet stability, admissibility, weak completeness and signed old G/H vertex-edge compatibility are Lean-certified.

The main #646 theorem is named **sourceLiteralY1SelectedLocal_rootedMultiCoset_injOn** in PSTSEPPA/ABO/SourceLiteralY1SelectedLocalRootedAmbientEmbedding.lean. It injects every selected original/fresh attached coset quotient vertex into G[A]. It does NOT assert injectivity on the whole disconnected G[A] multiCE.

#647: PSTSEPPA/ABO/SourceLiteralY1RootedBridgeTagObstruction.lean

- General **edge_injOn_of_vertex_injOn**: for deterministic signed EGraphs, injection of vertices on S implies injection of ACTUAL oriented signed edges with sources in S.
- Actual first-rank **sourceLiteralY1SelectedLocal_rootedMultiCoset_edge_injOn**, and **sourceLiteralY1SelectedLocal_rootedMultiCoset_no_empty_bridges** on the genuine selected region.
- Exact **rootedProperBridgeReflection_iff_tagAlignment** and source specialization: at rank |A|≤2, relative proper-B bridge reflection among rooted vertices holds iff any two such vertices sharing one ambient B-coset are equal OR admit presentations in ONE SAME intrinsically indexed full completed B-coset constituent. This is a *reduction*, NOT an assertion that tag alignment has been proved.

#648: PSTSEPPA/ABO/RootedMultiCosetAComponentExact.lean

- **rootedMultiCosetImage_iff_parent_A_index**: the entire selected tagged old+fresh region equals precisely one genuine intrinsic A-parent component-index fibre.
- **rootedMultiCosetImage_iff_A_reachable**: equivalently, exactly the vertices reachable by ACTUAL signed A-words from the old root in the real uncompleted multiCE EGraph.
- **rootedMultiCosetImage_target_mem_of_source_mem**: every original signed edge starting in the region also ends there.
- **rootedMultiCosetImage_A_connected**: every two vertices in that selected region are genuinely A-connected.
- **sourceLiteralY1SelectedLocal_rootedImage_iff_A_reachable**: exact instantiation for the first-rank finite G[A] original old pullback.

Thus the target of the checked injection is an honest A-connected, edge-closed old/fresh signed EGraph component; whole-pullback connectedness is neither claimed nor needed.

## Exact next obstacle: singleton B-bridges in corrected 4.7(iii)

At |A|=2 all proper B are empty or singletons. **B=empty is closed** for the selected region. If two selected vertices share the same intrinsic B-component-indexed complete B-coset, a real B-word connects them (existing multiCoset_selected_B_component_exact and singleCosetEGraph_connected_on_index). Remaining open:

> For singleton B={i}, if any two vertices of the above true old+fresh A-component lie in the SAME ambient G[A][B]-coset, prove that either they are equal or their true component-tagged presentations lie in the SAME attached full B-coset constituent.

This does not follow from the root-region vertex/edge injection, 1-stability alone, or rank-two admissibility. The #647 equivalence reduces rooted relative bridge reflection to precisely this **still-unproved** tag-alignment statement. Do not silently introduce a global bridge-free assumption.

Suggested correct source path:

1. Map an actual ambient singleton-B Cayley connection through the certified BASED FULL signed G[A] Cayley→completed H[A] P_A cover. Strip only newly added stationary loops to get a REAL B-path in the original uncompleted H[A] P_A graph (TrivialLoopCompletionStripPaths.lean, TrivialLoopCompletionCayleyCosetBridge.lean).
2. Classify that H-side B-component with the rank-two full-B-coset / isolated singleton geometry (RankTwoComponentBase.lean, RankTwoClusterPropertyBase.lean); do not identify unequal component tags via equal H group values.
3. Use the already-certified actual original old B-component signed equivalences (SourceLiteralY1X2AllOriginalBComponentGraphEquiv.lean), the local Q_A one-stability and specific TRUE off-B augmented type-(2) stage covers (SourceLiteralY1AllType2FamilyG2Cover.lean, SourceLiteralY1ThreeKindG2Action.lean) to force the missing G-side SAME-tag conclusion, dealing separately with old-meeting and off-old clusters.
4. Note the **distinct** paper repair R8: corrected Theorem 4.7(iii) omits the off-skeleton full B-coset alternative; this is a one-constituent degenerate case. R8 is NOT synonymous with the general external singleton-B tag-alignment problem. The earlier 2026-10-07 user-provided PROJECT2_ABO_AUDIT.md §6.4 explains this repair.
5. Apply #647's exact iff ONLY after source singleton tag alignment has been proved. Do not infer any full multiCE bridge freeness for other disconnected G[A] components without additional argument.

Other key code: SelectedOldComponentMixedCosetCollision.lean, SelectedOldComponentMultiCosetAmbientEmbedding.lean, SourceLiteralY1SelectedRootNormalizedLocalHFullCayleyCover.lean, SourceLiteralY1NormalizedOldRootAnchorAgreement.lean, OriginalRootedAComponentSurjectiveCover.lean, MultiCosetParentComponentExact.lean, BridgeFreenessInterface.lean, CayleySectionBridgeFreeness.lean and RankTwoOffComponentCompletedStage.lean (all under PSTSEPPA/ABO).

## Still open after rank two

Theorem 4.7(iii) beyond one component, Condition 5.2, actual exact equivariant Definition-5.3 Z_k selection, all higher k≥2 histories, stage kernels and cluster/bridge induction, finite reflecting group, fibre-MAX and the final unconditional ordinary PSTS EPPA theorem for closed embeddings. No global H-multiCE embedding, invented old edges, false A-stability, or invented whole-pullback connectivity can be used.

## Recovery

On restart inspect current GitHub main SHA and latest PRs/CI first. Read actual theorems #646–#648 and this checkpoint. Work next on the signed singleton-B external-tag alignment, preserving the independent original signed-input 256-case regression and axiom-audit discipline. No user input is currently needed.
