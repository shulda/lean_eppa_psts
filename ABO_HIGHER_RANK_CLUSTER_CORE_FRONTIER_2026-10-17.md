# 17 October 2026 — Exact higher-rank ABO cluster geometry checkpoint

## Authoritative accepted Lean cutoff

The accepted `main` mathematical cutoff at this checkpoint is
`f1bcb3e1c921b52e5e156b0e584b33bfcb1fb2f2` (PR #687).
Recheck live GitHub for any newer commit. **Every mathematical PR
listed below independently passed its own exact-head full Lean
build, the 256 genuine signed old-input edge configurations and
the allowed-axioms audit before merge.** A separate successful
postmerge main run is not claimed where one had not yet completed.

| PR | Genuine result | Exact PR-head green Actions run | Accepted main commit |
| --- | --- | --- | --- |
| [#683](https://github.com/shulda/lean_eppa_psts/pull/683) | Original rank-two full tagged old+fresh multiCE **vertex injection** into (intrinsic original A-component, true local G[A] group coordinate), and relative B-path reflection within each fixed original tag | [39053926897](https://github.com/shulda/lean_eppa_psts/actions/runs/39053926897) | `82f3df4` |
| [#684](https://github.com/shulda/lean_eppa_psts/pull/684) | Same global COMPONENT-TAGGED injection on **all actual oriented signed old/fresh edge tokens**, respecting missing old edges | [39054743768](https://github.com/shulda/lean_eppa_psts/actions/runs/39054743768) | `4dc5798` |
| [#685](https://github.com/shulda/lean_eppa_psts/pull/685) | At **every parent rank**, true B-component dichotomy for every proper `B` with `|B|≤1`: one selected tagged full B-coset inside a C-copy with B⊆C, or isolated singleton | [39055907009](https://github.com/shulda/lean_eppa_psts/actions/runs/39055907009) | `9abeea0` |
| [#686](https://github.com/shulda/lean_eppa_psts/pull/686) | For `|B|≤2`, any two outgoing actual signed B-edges of **different base letters** from a no-large (cluster-branch) B-component vertex have a common **nonempty tagged support** D with D∩B=∅ and D⊄B, at arbitrary parent rank | [39056422245](https://github.com/shulda/lean_eppa_psts/actions/runs/39056422245) | `bd9331f` |
| [#687](https://github.com/shulda/lean_eppa_psts/pull/687) | For parent `|A|=3` and `|B|=2`, the tagged support D of each such transverse switching vertex can be chosen **exactly A\B** (the unique missing-letter alphabet) | [39057023145](https://github.com/shulda/lean_eppa_psts/actions/runs/39057023145) | `f1bcb3e` |

The new mathematical files, imported from `PSTSEPPA.lean`, are:
- `SourceLiteralY1TaggedFirstRankComponentAssembly.lean`
- `SourceLiteralY1TaggedFirstRankSignedEdges.lean`
- `AllRankSingletonLetterComponents.lean`
- `AllRankTwoLetterBranchingCommonCore.lean`
- `RankThreeCanonicalTransverseMissingSupport.lean`

## Scope of the results

The first two PRs correct a subtle GLOBAL-vs-ROOTED issue:
the genuine old G[A] pullback may be disconnected, and its
distinct old A-components can share ambient G coordinates.
A global injective map exists ONLY AFTER retaining the genuine
original parent A-component tag. These theorems never claim
unqualified old multiCE→Cayley(G[A]) injectivity.

The next three PRs make actual progress on the **first
nontrivial higher-rank cluster-property induction**, rather
than extrapolating the rank-two singleton classification to
every higher-rank B-component:

1. When B has at most one letter, all B-components have the
   fully classified, actually realised one-constituent/singleton
   shape, with no rank bound on A.
2. When B has two letters and the selected B-component lies
   in the **no-large** branch (no genuine C⊇B supports its
   starting vertex), each actual edge has a strict-lower
   C∩B patch. Two transverse letters at one vertex force
   their patches to share a genuine quotient-vertex support
   on an alphabet disjoint from B and **not empty**.
3. If A has precisely three letters and B precisely two,
   the supporting alphabet at such a transition is
   exactly the one-letter complement A\B. Its intrinsic
   OLD-component tag is retained and is not equated with
   the tags at other transition vertices.

No artificial loops from the legal stage's trivial
completion are mistaken for real original edges.
All signed inverse edge tokens are preserved.

## Critical falsification benchmark

The correct rank-three counterexample in
[ABO_STAGE_FAMILY_HUMAN_AUDIT_2026-10-11.md](ABO_STAGE_FAMILY_HUMAN_AUDIT_2026-10-11.md)
has Γ=C₂³, old incomplete K={1}, A={a,b,c}, B={a,b}.
The whole proper coset extension has seven vertices
`1,a,b,c,ab,ac,bc`, and the actual off-skeleton B-component
from c is `{c,ac,bc}`, with a- and b-edges through c;
`abc` is absent. It is a genuine three-vertex B-cluster,
neither a selected full B-coset nor a singleton.

The newly checked rank-three lemma gives actual {c}
tagged support at the transverse center, which is compatible
with this example. It does **not** misclassify the whole
three-vertex component as a singleton, nor assert that
other B-component vertices all have {c} support.

The separate
[ABO_HUMAN_GEOMETRY_SHORTCUT_AUDIT_2026-10-11.md](ABO_HUMAN_GEOMETRY_SHORTCUT_AUDIT_2026-10-11.md)
also prohibits assuming that a merely generated/retractable
ambient Cayley graph covers every completed coset extension.

## Corrected status: SOURCE-PROVED, NOT YET LEAN-FORMALIZED

**Critical correction (17 October 2026):** The previous heading
"Unsolved mathematical theorem" and the description
"Proposition 3.23 whole-component cluster property" were WRONG.
The objective is to translate the **existing ABO proof**, not discover
a new proof of an alleged open mathematical problem. The October-7
independent prose audit classified the corrected construction
as **verified with local repairs R1–R8**; this is a human/AI
mathematical-audit verdict, **not** a Lean certificate of those
still-unformalized statements.

Exact source distinctions ([ABO I, arXiv:2208.03273v6](https://arxiv.org/pdf/2208.03273)):

- **Definition 3.22 (PDF p.31):** defines whole-component
  cluster property, including both genuine cluster and full-coset
  alternatives and the minimum support attained at a core vertex.
- **Proposition 3.23 (PDF p.31–33):** ASSUMES the cluster
  property and proves that intersections of intrinsic B-
  and C-components are (B∩C)-components.
  It does NOT prove the cluster property.
- **Lemma 4.3 (PDF p.35–38):** PROVES the next-rank
  cluster property under precisely stated embeddedness,
  bridge-freeness and cluster-property assumptions on
  lower-rank component extensions.
- **Proposition 4.4 / Theorem 4.5 (PDF p.38–39):** rank-two
  base and general forward-induction consequence.
- **Theorem 4.7 (PDF p.39–43):** upward-induction package.
  Preserve source audit repairs R1 (retractability consequence),
  R7 (index typo), R8 (off-skeleton full-B-coset alternative).
- **Proposition 3.24 / Condition 5.2 / Proposition 5.4:**
  subsequent established source proof ingredients, with
  separate base/domain repairs R2–R3.

**Precise formalization plan: follow ABO Lemma 4.3 as written,
not a new switching-vertex research program.**

1. Take an off-skeleton intrinsic B-component `Q` of the
   genuine signed full `CE(H,L;P_A)`. Classify its case of
   containment in a single maximal tagged constituent; this is
   the full-coset alternative, not the multi-piece cluster case.
2. Otherwise choose a MINIMAL cover of `Q` by genuinely
   maximal constituent cosets `v_i H[A_i]` and set
   `B_i = Q ∩ v_i H[A_i]`. Prove each nonempty `B_i`
   has a genuine support with alphabet of size < |A_i|.
3. Apply the **induction assumptions** to the actual lower-rank
   embedded and bridge-free `CE(H,A_i;P_{A_i})`:
   the portion of `B_i` in it is an intrinsic connected
   component and inherits a unique minimum support `(D_i,u_i)`
   from its lower-rank cluster property. Transfer this support
   to the original upper extension with original-component
   tags unchanged.
4. For two intersecting `B_i,B_j`, use source (3.11),
   (3.12), Lemma 3.21, and **retractability / deletion of
   letters outside D** to prove the minimal supports agree
   (including their genuine tagged coset), attained in the
   intersection. This is the NONTRIVIAL synchronization
   argument in the published proof (PDF pp.36–37).
5. Induct along the finite connected family of constituents:
   obtain a single minimum tagged support attained in the
   common core. Identify the union of maximal constituents
   as an A-cluster and apply Corollary 3.12 for the B-cluster
   representation. The source provides these steps explicitly.
6. Apply the result to Theorem 4.5 and only thereafter
   formalize the off-skeleton cases of conditional Proposition
   3.23 and the Proposition 3.24 augmented classification
   and corrected upward Theorem 4.7. Carry the exact
   Section-5 stage histories and Condition 5.2 subsequently.

**What is currently OPEN means only "not yet checked by Lean":**
the whole Lemma-4.3 argument and corresponding general
cluster property, conditional full Proposition 3.23,
Proposition 3.24, higher Theorem 4.7, Condition 5.2,
exact equivariant Definition-5.3 stage selection,
finite reflecting group, concrete fibre-MAX and
the final ordinary PSTS EPPA theorem. No new mathematical
conjecture is implied.

**Interpretation of PRs #685–#687:** they are valid
Lean-certified auxiliary **local** observations, not the
source's whole-component minimum-support synchronization
argument; they should no longer drive the proof plan.
PRs #683–#684 are useful tagged-component APIs but do not
replace full source embeddedness. The rank-three C₂³
example remains a falsification check against incorrectly
extending the singleton case to |B|=2.

The R8 full-constituent repair already has separately
checked source-facing formalization in
`PSTSEPPA/ABO/CorrectedR8FullCosetOneConstituent.lean`.
First-rank rooted source B-bridge reflection at every original
old A-root is independently certified in
`PSTSEPPA/ABO/SourceLiteralY1EveryOldRootProperBridgeReflection.lean`.
Neither proves the higher-rank induction by itself.

No user decision is needed to resume the known ABO proof translation.
