> **SUPERSEDED CHECKPOINT:** This file documents the post-#638 mathematical state. The now-authoritative 2026-10-17 first-rank rooted component/bridge frontier after independently certified and merged #646–#648 is [ABO_FIRST_RANK_ROOTED_COMPONENT_AND_SINGLETON_BRIDGE_FRONTIER_2026-10-17.md](ABO_FIRST_RANK_ROOTED_COMPONENT_AND_SINGLETON_BRIDGE_FRONTIER_2026-10-17.md). Preserve this older page as historical proof dependency/audit detail, not as the latest current-state summary.

# 2026-10-17 — Corrected ABO first-rank TRUE printed P_A: post-#638 verified checkpoint

## Authoritative status and verification boundary

The authoritative GitHub `main` after the source-old-component
compatibility series is **`d01d98d325f0d4393632afa53a782db2473b64ba`**
(merged **PR #638**). No final unconditional ordinary EPPA theorem for
finite PSTS has been proved. The first-rank TRUE local signed
Cayley(T(X₂^all)[A]) cover and its exact original OLD A-component
compatibility, including actual formally oriented old edges, **have**
been Lean-proved.

Relevant **exact PR head** full-Lean + independent 256 genuinely signed
original-input edge-pair regression + axioms-audit GREEN runs:

| PR | Mathematical source file | Verified PR CI |
|---|---|---|
| #635 | `SourceLiteralY1OldPathLocalStageAgreement.lean` | [39012670675](https://github.com/shulda/lean_eppa_psts/actions/runs/39012670675) |
| #636 | `SourceLiteralY1OldRootTaggedStageInclusion.lean` | [39013072158](https://github.com/shulda/lean_eppa_psts/actions/runs/39013072158) |
| #637 | `SourceLiteralY1OldGToTaggedHCompatibility.lean` | [39013475447](https://github.com/shulda/lean_eppa_psts/actions/runs/39013475447) |
| #638 | `SourceLiteralY1OldGToTaggedHVertexEdgeAgreement.lean` | [39014050678](https://github.com/shulda/lean_eppa_psts/actions/runs/39014050678) |

All four are merged in dependency order and imported from
`PSTSEPPA.lean`. In #638 an earlier PR head failed to parse a
`signedBase` application due only to missing parentheses;
**only its corrected exact head** `3d3663cdf3d6f4d7cdb804355f08cf43ac532b64`
passed all audits and was merged.

The prior file snapshot at #630 (and PRs #628/#629/#631/#632 still
pending then) is historical, **superseded by this checkpoint**; its
detail remains available in Git history. Prior to #635, main
`587afb17b5f6df9edbba2c793eb56a445cc66427` had already
integrated the full source printed local P_A Cayley coverage, old/fresh
signed edge surjectivity, outside-A stationarity and original
old-component surjective G→H cover.

## Precisely what is now proved

Fix a parent alphabet `A` with `A.card = 2`, one genuine ORIGINAL
old H root `root ∈ T(Y₁)`, and a real original G root
`gRoot ∈ T(X₂^all)` projecting to it. Work with genuine original
**incomplete** signed edge preimages in both groups, never with
the artificial X₁ completion. Select the actual intrinsic original
signed A-component of `gRoot`. The H-side completed P_A stage is
the genuine old/fresh **component-tagged** intersection-support
multi-coset vertex quotient; signed edges are quotiented by glued
source + **full signed label**; only missing signed stationary loops
are legally added.

* **#635:** Real old signed A-word path `gRoot --w--> x`
  determines `gRoot⁻¹*x ∈ G[A]`. Its evaluation under the
  TRUE FULL local signed Cayley(G[A])→H-P_A stage cover equals the
  endpoint of `w` from the exact OLD TAGGED H stage anchor.
  The matching orientation-aware complete-stage edge formula is
  separately proved. This alone did **not** identify an actual H
  original old edge / component-tagged old vertex.
* **#636:** Construct a concrete labelled-graph morphism from the
  original incomplete H old A-root component to the actual completed
  P_A stage. Each original signed edge is represented in a genuine
  chosen proper-B raw constituent, then in the exact source/label
  edge quotient, and finally in the legal loop completion. Use the
  genuine B=∅ proper constituent to anchor the original old H root.
  Every realised old H signed path has the corresponding exact
  component-tagged completed-stage endpoint.
* **#637:** Project any actual G original old A-path to H, restrict
  to actual original A-edges, and lift the entire path to the
  selected **intrinsic original H A-component**. Compose #635 and
  #636. The local G[A] cover of the root-normalised actual G point
  equals the image of the exact selected old H vertex **in the
  tagged quotient itself**, not merely in H ambient coordinates.
  Main theorem:
  `sourceLiteralY1X2AllSelectedRoot_oldAComponent_taggedCompatibility`.
* **#638:** Remove the word witness in an all-true-old-component
  vertex API, and strengthen to all **actual original signed A-edge
  tokens** leaving any true old G A-component vertex. Exhibit the
  literal original H signed edge token, lift it to the actual old
  H A-component with the correct source, and prove the local G[A]
  completed cover's edge image equals its tagged old H inclusion
  image. Both positive and negative directions, genuine loops,
  identity/repeated labels are covered by the signed formalism.
  Main theorem:
  `sourceLiteralY1X2AllSelectedRoot_oldAComponent_allEdges_tagged`.

Crucially, **NOT** proved: all original G ambient A-coset points
belong to the selected old A-component; the whole G pullback is
A-connected; the H multi-coset ambient group-coordinate projection
is injective; G↠H is A-stable at |A|=2 (only proper singleton/empty
stability is certified); or every completed H-stage edge existed
in the original old skeleton. Such assertions would generally be
wrong or at least unjustified.

## Existing abstract embeddings and the next exact source gate

Generic conditional ABO corrected 4.7(ii) tools, previously
Lean-certified, include:

* `RootedOldComponentDeterminesHStageCover.lean`:
  `pullbackOldToWeakMultiCosetStageHom`,
  `rootedWeakMultiCosetCompletedStage_represents_all_attached`,
  `pullbackQuotient_multiCosetAmbient_injective_of_rooted_stageCover`.
  The strong unscoped final theorem there explicitly assumes the
  WHOLE pullback is one rooted intrinsic A-component, so it is
  **not** automatically applicable to the possibly disconnected
  original source pullback.
* `SelectedOldComponentMixedCosetCollision.lean` and
  `SelectedOldComponentMultiCosetAmbientEmbedding.lean`:
  `pullbackQuotient_rootedMultiCosetAmbient_injOn`.
  This is the correct conclusion **restricted to the selected old
  A-component's FULL attached B-coset region**, and handles actual
  B/C intersection-support gluing, not merely original old points.

**Next formalization task: instantiate the latter rooted
component-scoped theorem at the true first-rank local
G[A]↠H[A] construction**, using the new #635–#638
old signed graph compatibility.

The next instance must discharge, explicitly and without global
ambient shortcuts:

1. The exact local `G[A]`/`H[A]` **generated** group presentations,
   selected original old signed component skeletons and their
   first-rank labelled quotient, with stability only on selected
   proper `B⊊A` (|B|≤1). Use genuine component/local-coset-slice
   and pullback modules, not whole ambient cosets.
2. The required local retractability, admissibility,
   selected-root multi-coset **weak completeness** and legal loop
   completion, transported along previously certified genuine signed
   source-H₁ ↔ literal T(Y₁) rooted P_A stage isomorphisms.
3. The precise based complete signed local G[A] Cayley cover
   translated to the **selected root** required by the generic
   embedding lemma. Its identity is the actual old tagged H point.
   #637–#638 now certify all old component vertex AND original
   signed edge compatibility at this root. Check the family
   `P=allProperCosetFamily A` and all old/fresh quotient edge
   tokens; do not infer full G global injectivity.
4. Apply the **rooted** mixed-support/ambient `Set.InjOn`
   result to the full fresh/old attached region selected by this
   ONE genuine original G A-component. Distinguish this
   component-scoped conclusion from full global multiCE
   injectivity.

The key nearby source files worth reading together are
`SourceLiteralY1SelectedRootFullLocalCayleyCover.lean`,
`SourceLiteralY1SelectedRootPlainOldAnchorCover.lean`,
`OriginalRootedAComponentSurjectiveCover.lean`,
`SourceLiteralY1X2AllOriginalBComponentGraphEquiv.lean`,
`KStablePullbackMultiCosetStageCoverEmbedding.lean`,
`LocalCosetCayleyPaths.lean`,
`RootedSourceAllProperCompletedStageIso.lean`,
plus all four newly merged source modules above.

Even when corrected rank-two 4.7(ii) is fully instantiated,
**4.7(iii)** needs genuine independent
cluster/augmentation alternatives and **R8 full B-coset repair and
G-external B-bridge freeness**. Subsequently Condition 5.2 at rank
2, exact equivariant Definition-5.3 Z_k selection and higher-rank
word kernels/stages (k≥2), finite reflecting group and fibre-MAX,
and final PSTS EPPA for closed embeddings remain open.

## Recovery instructions

On restarting, check current GitHub `main` and open PR/CI status
before treating this dated SHA as current. Check exact PR HEAD
GitHub Actions GREEN, not cancelled intermediate push runs.
Read the recent source files **and the theorem signatures**,
then tackle the local rooted component-scoped embedding instance
above. Keep reporting conservatively: strong signed old G/H
compatibility is complete, but no unconditional PSTS EPPA and
no blanket rank-two 4.7(ii)/(iii) proof yet. User input is not
needed for this current mathematical next step.
