# PSTS/ABO formalization — genuine selected old component milestone (2026-10-16)

## Current source-based mathematical cutoff

At this dated checkpoint, verified `main` includes PRs #617–#620,
ending at commit `16807605e8941855cdd4477bbb8d7ed189a6be50`
(#620 exact source HEAD `a43080b77e3f21f0374eb3a3c9a66b23469ccea7`,
FULL Lean + 256 **actual original signed input cases** + allowed-axioms CI
run `38939716241` GREEN). Post-merge `main` CI is an
independent check; do not infer it from the PR's success.

Previous exact-head source CI already green:

- #617 `f164064e1c28cc9b7d1d483c047edeee97fd07b5`,
  run `38932551159`: old-skeleton agreement of a TRUE based
  Cayley(G) cover with the LEGAL completed H multiCE stage
  implies correct representation of all actual component-tagged
  attached B-coset vertices; H ambient coordinate-map
  injectivity is NOT required.
- #618 `3a3fb97d7b9114e64874839256c078d71bb90206`,
  run `38933182734`: one correctly normalized old root suffices
  for compatibility over an A-connected OLD G skeleton, hence
  the H-stage cover controls the entire attached B-coset stage.
- #619 `6cfd8cd1ed3d1d2fd24d71a5fea3255f425c96ae`,
  run `38933952700`: important source scope repair:
  the WHOLE old G-pullback can be DISCONNECTED. For two
  attached B/C points anchored in ONE genuinely selected
  old G A-component, equal original G values force actual
  (B∩C)-tagged gluing via a single normalized completed
  H-stage Cayley cover, without any unproved whole-pullback
  connectivity hypothesis.
- #620 `a43080b77e3f21f0374eb3a3c9a66b23469ccea7`,
  run `38939716241`: package the #619 pairwise gluing
  into **Set.InjOn** of the true original G ambient
  multiCE coordinate map on the IMAGE of all selected
  component-anchored tagged raw B-coset constituents,
  including NEW attached points, across ALL selected B.
  That is a precise selected-old-component embeddedness
  result (under a normalized genuine G→completed-H-stage
  cover hypothesis), not all unrelated A-components.

No `sorry` or new axiom is accepted. The new modules use exact
original signed edge tokens and component-indexed B∩C gluing;
they do NOT identify different old components by equal ambient
H group coordinates.

## Next source-geometric rank-two issue: surjectivity vs. bijection

Our actual paper first-rank tower

    G = T(X₂^all)    →    H = T(Y₁)

is a finite, generator-preserving **ONE-STABLE** quotient.
The finite all-choice rank-one stage catalogue includes the genuine
printed original-edge rooted P_A completions, augmented type-(1)
clusters, and actual tagged off-B type-(2) stages.

For |A|=2, the quotient is NOT known to be 2-stable. It is therefore
WRONG to assert that the entire original old G A-component injects
into, or is canonically isomorphic to, its original H A-component.
Nor is the full old G-pullback generally A-connected.

But the exact OLD path lifting of #599 and original edge lifting
of #600 do imply:

* From any chosen genuine G original old root, its single
  intrinsic original B-component SURJECTS onto the original
  H B-component of its image, including all source-reachable
  signed directed B-edges, for every B and **without** B-stability.
* Given ANY genuine original H old root, choose one real G
  preimage root; the resulting selected G old A-component
  surjectively covers the desired original H old A-component
  on the true vertices and oriented signed edges.
* For every B⊊A, |A|=2, our actual one-stability supplies the
  separately certified stronger vertex-and-edge component
  bijection, including empty B and formal inverse labels.

**Candidate, NOT promoted yet at this checkpoint:**
#621 `OriginalRootedAComponentSurjectiveCover.lean`, exact corrected
head `fa71325f7444c0caabcb4d8d370181d2749be9e4`,
proves the first point and its literal first-rank instance;
#622 `SourceLiteralY1X2AllOriginalSelectedRootCoverage.lean`,
stacked exact head `ed4d1c81fdd5b356fee6ed983dab8cef68b94c1c`,
formalizes the second point. Their exact-head full CI was
still running. Both PRs retain the distinction between
surjective true old A-component coverage and proper-B
bijective original component coverage.

## Remaining corrected Theorem 4.7(ii) gate

The accepted #619/#620 injection results are conditional on ONE
root-normalized G-Cayley morphism into the **exact LEGAL completion
of the selected H coset extension**, compatible with the original
old skeleton and its chosen component-root tag.

To instantiate at the ACTUAL literal rank-one source, we need:

1. Choose each genuine original H=T(Y₁) A-component, as already
   constructed in `SourceLiteralY1RootComponentVertexEquiv.lean`.
   Align it with a chosen old G-root and its genuine G A-component.
2. Localize to real G[A], H[A] with the already certified
   quotient `sourceLiteralY1X2AllLocalQuotient`, one-stability,
   actual local generatedness and global retractability
   (#612/#613) for |A|=2. The exact old slice/pullback
   identity is already certified (#616).
3. Match the selected H-root **plain P_A weak completion**
   with the TRUE printed complete stage
   `sourceLiteralY1SelectedRootPlainCompleteStage`,
   respecting actual old/fresh tagged vertices,
   all signed edge tokens and stationary loops.
   Existing source-H₁/paper rank-two completed stage
   isomorphisms are available (e.g.
   `SourceLiteralY1SelectedRootPlainStageIso.lean`).
4. Extract and root-normalize ONE actual Cayley(G[A])
   morphism onto this exact selected H-root completed stage
   from the finite literal T(X₂^all) stage action and
   its genuine transition-factor quotient.
   Its actual old-root image must be the intended
   tagged H old point, not merely an equal H group coordinate.
5. Apply the certified rooted embeddedness theorem to the
   selected old component. Avoid any hypothesis of global
   H-multiCE ambient injectivity, which is FALSE in general.

The all-choice rank-one family is still not yet proven to be an
exact, finite automorphism-equivariant corrected Definition-5.3
representative selection. The higher-rank historical stage
word-kernel and selection inductions remain OPEN.

## Other outstanding hard proof gates

Even after a fully source-instantiated Theorem 4.7(ii),
Theorem 4.7(iii) must rule out **external B-bridges**.
It requires the H cluster property, genuine B-augmented
stage covers, k-stable signed-word comparisons and the
otherwise easily omitted **full B-coset R8 alternative**.
The constructive signed loop-stripping lemma #588 and the
original P_A specialization #589 are accepted, but do
NOT settle the entire bridge-freeness proof.

Only then may we assert corrected Condition 5.2 at rank two.
For k≥2 we still need historical Y_k/Z_k stage word-kernels,
all-rank Theorem 4.7 geometry and Condition 5.2,
the finite reflecting-group theorem, the concrete fibre-MAX
step, and finally unconditional ordinary EPPA for closed
embeddings of finite partial Steiner triple systems.

## GitHub workflows and next session instructions

Treat GitHub `main` as authoritative.
For every mathematical PR, require the exact HEAD
FULL Lean build, 256 REAL signed source-input pattern regression
tests and permitted-axioms audit to be green before merge.
Check post-merge main CI separately. Clean stacked PRs so their
final diff contains only their new mathematical module/import.
When a session crashes, CHECK GitHub before reconstructing progress.
Never call an UNVERIFIED conditional stage cover assertion,
or a mere ambient coset coordinate map, the complete
corrected Theorem 4.7(ii) or unconditional PSTS EPPA.
