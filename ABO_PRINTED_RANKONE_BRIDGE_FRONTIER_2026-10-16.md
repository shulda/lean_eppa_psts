# October 16, 2026 — Printed PSTS/ABO first-rank bridge frontier

## Verified git cutoff and trust rules

The authoritative completed mathematical `main` cutoff at writing is
`bd517df8f3d1e2495cf7ac7b4952fcc6ae3781cc`, after merging
independently exact-head CI-GREEN #588 and #589.
The separate postmerge-main CI is a different condition and was
still in progress at this checkpoint; do not silently treat it as green.

Prior #577–#587, including the literal complete
`X₂^all = Y₁ ⊔ Z₁^all` first-rank three-kind action, are on `main`.
Its *actual* finite transition group has a labelled surjection
onto paper `T(Y₁)`, 1-stability and 2-retractability; the true
based Cayley group projections cover exactly the reachable vertices
and signed oriented edge tokens of the complete three-kind family.

- #588, source head `f25ec3e0`, exact full Lean/256 original signed
  source-edge input regressions/permitted-axioms GREEN `38892811470`;
  commit merged as `81318629bc824ab19e680f8dd54c51bc79e47584`.
  Constructively strips only **new stationary signed loops** from
  arbitrary supported words in the LEGAL completion of a locally
  paired incomplete EGraph, preserving genuine old edge paths
  and their endpoints, all B incl. empty.
- #589, head `d95f6246`, exact full checks GREEN `38892889846`;
  merged as `bd517df8f3d1e2495cf7ac7b4952fcc6ae3781cc`.
  Specializes the exact intrinsic B-component preservation to
  the genuine original-edge-selected, component-tagged printed
  rank-two rooted P_A full coset extension.

## Subsequent candidate PRs (NOT proven/merged at this checkpoint)

All entries below are mathematical proposals, not accepted theorem
statements until their own exact HEAD builds, genuine 256-case
regression test and narrow axiom audits turn GREEN, then clean
integration / exact new postmerge tests where appropriate.

- #590, head `2bba869033`: real finite source
  `G₂ -> T(X₂^all)` SURJECTIVE generator-preserving labelled
  quotient on the ENTIRE literal first-rank disjoint action,
  not merely separate projections; expected 1-stability.
  Its early red version had only a Lean namespace qualification
  error for `CompleteEGraph.rightApply`; corrected head had
  ongoing full CI as of writing.
- #591, head `64a12169`: map a signed B-left-coset Cayley
  path through ANY based morphism into the legal completion
  and strip newly added loops, getting a TRUE B-path in
  the original incomplete EGraph. This is conditional on
  the existence of the map; it DOES NOT give embedding.
- #592, head `8ed1e481`: the true transition subgroup of
  a dependent disjoint completed stage action surjects
  generator-for-generator onto EVERY indexed fibre's
  transition subgroup. This is an exact group action result,
  not mere product projection shorthand.
- #593, head `06340fce`, strictly dependent on #592:
  compose the actual literal T(X₂^all) stage quotient with
  the selected *original printed* rooted P_A fibre quotient.
  Produce a surjective transition map, a genuine signed based
  Cayley projection and exact reachable vertex/edge ranges.
- #594, head `8248a351`, stacked on #593 and temporarily
  carrying the #591 generic source: use the actual literal
  stage quotient to show B-coset-related T(X₂^all) group
  points project to points joined by a TRUE signed B-path in
  the ORIGINAL INCOMPLETE tagged P_A full coset extension.
  **After #591 merges, remove its duplicate blob/import on a
  clean rebase**, preserving only the new specialization.
- #595, head `80517f05`, stacked on #591:
  if a connected incomplete locally paired signed EGraph
  admits an actual labelled old lift S to Cayley(Γ) and
  a labelled based Cayley-to-completion map F compatible at
  one root, connectedness implies `F∘S=id` on old vertices.
  Consequently S is injective and every ambient B-left-coset
  connection between its old image points yields a real OLD
  B-path. This is a CONDITIONAL criterion that **does not
  construct S** and makes no ambient-coordinate injectivity
  assumption.

## Crucial distinction from the hard corrected Theorem 4.7

The formalized rank-one `T(X₂^all)` projections and #588–#589
loop-stripping cover OLD stages built over the **H₁ presentation**.
The corrected Theorem 4.7 relates two different group levels:
a k-stable quotient `G ↠ H`, a true original `H`-cover
skeleton `L_H`, and its `G`-cover `L_G`.

Theorem 4.7(ii) must first show the canonical
`CE(G,L_G;P_A) -> Cayley(G[A])` morphism is actually
vertex-injective, by analysing same-support and mixed-support
collisions through stable proper cosets and exact
intersection-supported component tags. One must NEVER assume
this property merely because the completed H-stage has a
Cayley cover, nor conflate equal ambient H₁ coordinates
with equal tagged quotient vertices.

Theorem 4.7(iii) then excludes B-bridges in the **G-level**
coset extension. Its argument projects to the completed
plain H-level stage and uses the cluster property. In the
genuine off-skeleton B-cluster case one augments by the full
H[B]-coset, uses the augmented-stage cover and k-stability
to identify the lifted G-word with the replacement H-word.
The repaired **full-B-coset alternative (R8)** remains a
separate case. The embedding/bridge statements quantified
over the G-cover are NOT established by any of #588–#595
alone. Also preserve the missing retractability repair R1,
and do not invoke nonexistent H₀/Z₀ at rank one.

One can find the detailed independently audited mathematical
hypotheses, source page references and proof breakdown in
`sources/PROJECT2_ABO_AUDIT.md`, sections 6.1–6.4 in
the October 7 advisory archive, and
`ABO_STAGE_FAMILY_HUMAN_AUDIT_2026-10-11.md`
on this repository.

## Next practical research/formalization steps

First finish and CLEAN integrate any green candidate heads above,
in source-dependency order; inspect red exact-head CI job logs,
do not guess success. Then identify the exact instantiated
`L_G` of the genuine paper/Y₁ original root and prove the
same-support + mixed-support **embedding** argument for
`CE(G,L_G;P_A)`, with correct subgroup rank and
component-index tagging. Use the already proved rank-two
cluster property for the k=1 base. Only after embedding
assemble the genuine H/G bridge argument (full-B-coset
alternative included) and Condition 5.2 at rank 2.

Higher k≥2 historical stage-action word kernels,
corrected Theorem 4.7 induction, finite reflecting group,
concrete fibre-MAX, and unconditional closed-embedding
PSTS EPPA are still OPEN. No general result is promoted
from the rank-one achievements alone.


## Superseding 2026-10-16 afternoon update — G/H original-cover frontier after #599

**Live accepted mathematical `main` at this checkpoint:** `a961e19446d813e5261a9421b6762239ad76ab0e` (PR #599). All PRs listed as accepted below have their own independently GREEN exact-head full Lean / 256 TRUE signed original-input cases / permitted-axiom audit; post-merge main CI is a separate check.

Certified and merged since the historical earlier cutoff in this document:

- **#590** `e5b19d26a525f04009a597cf05711d6deb98959c`: the original finite input-derived source G₂ maps SURJECTIVELY with labels intact and rank-one stability to the entire genuine literal `T(X₂^all)` signed transition group, not only to one of its action factors.
- **#592** `3fab25de9237611ffd4ce2e7d92f5c3d1c3cb9bb`: arbitrary dependent disjoint complete signed action's TRUE transition subgroup surjects onto the transition subgroup of any chosen actual tagged stage.
- **#593** `6dd3aee2205cb65ceaecfee3d4866bfef827a271`: genuine literal `T(X₂^all)` maps surjectively to each ORIGINAL-input rooted printed plain P_A stage transition group, with based Cayley maps of exact reachable vertex and formally signed edge ranges and exact word endpoints.
- **#591** `cc6bfe6a2e36b95372f450ed669572f053db2030`: a labelled Cayley group map into LEGAL stationary-loop completion sends B-coset-related group points to endpoints connected by an actual signed B-path in the original INCOMPLETE graph after stripping only newly added loops.
- **#595** `2f71b2f9c200910f604d66a47e790b69e307b6d2`: a CONDITIONALLY GIVEN labelled OLD graph lift S into the Cayley group, compatible at one root with a based Cayley-to-completion map F, gives `F∘S=id` throughout the original connected old graph. Consequently S is vertex-injective and has no external B-bridges. **Existence of S is NOT proved.**
- **#597** `b0f3441ed4fa5d06230d1c2623ffd3365e1dad51`: for ANY labelled quotient G↠H stable on B, each *chosen* translated coset gG[B] is bijective under that very quotient with the corresponding Q(g)H[B]. In contrast, different component-tagged cosets are not collapsed.
- **#594** `248bb59750f28486397560e065672904a44624e8`: any B-coset relation in ACTUAL `T(X₂^all)` projects into a true old B-labelled path in the exact incomplete original rooted P_A extension, via its real completed-stage quotient.
- **#598** `c9fc86940871b0df413de5a5fd5e4243514b7c95`: the stable translated B-coset bijection COMMUTES with arbitrary chronological signed B-word endpoints, and REFLECTS exactly the same B-word path equation upstairs/downstairs. This is one-coset local geometry only.
- **#599** `a961e19446d813e5261a9421b6762239ad76ab0e`: any real OLD chronological signed path in ANY incomplete H-Cayley skeleton lifts, from EVERY chosen source over its start, to a genuine old path in the Q-pullback G-Cayley skeleton, preserving the ENTIRE signed word, all formal edge tokens and prescribed downstairs target; uniqueness at fixed source.

**New candidate PRs, not yet promoted:**

- **#600** `SourceLiteralY1X2AllOriginalCover.lean`: instantiate the general pullback Q with genuine `T(X₂^all)↠T(Y₁)` and the independently certified ORIGINAL INPUT signed-edge preimage inside literal T(Y₁). Define the actual G-level incomplete old skeleton and map it first to H and then to original E; prove H-surjectivity of old vertices/oriented edges and lifting of EVERY original signed path from every chosen G-cover source. First attempted head had two Lean line-break field-notation mistakes and one named-let rewrite mismatch; updated head is being independently CI checked.
- **#601** `KStablePullbackIntrinsicBComponents.lean`: for any stable-on-B labelled quotient and two points x,y in its TRUE incomplete pulled-back G-skeleton satisfying the ESSENTIAL y∈xG[B] restriction, the genuine old signed B-path x→y exists upstairs iff the image points are connected by an original old signed B-path downstairs. The reverse direction combines new #599 old-path lifting with the #597 fixed-coset injection, so distinct lifted B-components cannot be conflated. Exact-head CI pending.

**Remaining mathematical main bottleneck**: corrected Theorem 4.7(ii) G-level full CE embedding — identify the genuine G-cover of an actual H-cover component, reflect both SAME and MIXED constituent supports via the appropriate stable proper-coset bijections and H-admissibility, and show distinct tagged quotient points with equal G[A] coordinates were already glued through a common intrinsic (B∩C)-component. Theorem 4.7(iii) then additionally needs correct cluster/full-B-coset R8 alternatives, augmented completed-stage covers, and k-stable signed-word comparison. Neither the accepted H-level Cayley cover nor the conditional section lemma #595 supplies this G-level lift automatically. Condition 5.2 at rank two, all k≥2 history, the reflecting group and unconditional PSTS EPPA remain OPEN.
