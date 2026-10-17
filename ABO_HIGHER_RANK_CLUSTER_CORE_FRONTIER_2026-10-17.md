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

## Unsolved mathematical theorem, and recommended next gate

**Still OPEN:** the full ORIGINAL ABO Proposition 3.23
whole-component cluster property and higher-rank Lemma 4.3,
corrected Theorem 4.7(iii) beyond rank one, Condition 5.2,
exact equivariant Definition 5.3 historical Y_k/Z_k stages,
finite reflecting group, concrete fibre-MAX, and unconditional
ordinary EPPA for closed finite PSTS.

The next proof must go BEYOND individual switching vertices:

> For a no-large original off-skeleton B-component
> assembled from actual strictly smaller (B∩C)-patches,
> under precisely the lower-rank component embeddedness /
> bridge-free premises of the ABO forward induction,
> prove a **whole-component common-core / cluster decomposition**.
> At |A|=3, |B|=2, understand how the canonical A\B
> support points and their true old component tags behave
> along an actual B-word path, including the separate
> *already-full-B-coset* R8 alternative.

Do NOT assume the c-component tags at distinct switching
vertices are equal solely from ambient G[B]-coset equality,
and do NOT use the rank-two singleton lemma beyond |B|≤1.
A true full-B-coset component might be assembled from several
lower constituents even when it is not a selected B-constituent.

The full-constituent R8 case already has an independently
Lean-checked source repair in
`PSTSEPPA/ABO/CorrectedR8FullCosetOneConstituent.lean`.
The first-rank rooted source B-bridge reflection for EVERY
original old A-component is already certified in
`PSTSEPPA/ABO/SourceLiteralY1EveryOldRootProperBridgeReflection.lean`.
Neither substitutes for the higher-rank cluster case.

No user decision is needed to continue from this checkpoint.
