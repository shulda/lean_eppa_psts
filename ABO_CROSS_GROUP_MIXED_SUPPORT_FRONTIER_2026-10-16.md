# 2026-10-16 — Cross-group mixed support and full coset-extension embedding frontier

## Accepted mathematical git cutoff

At writing the authoritative `main` mathematical SHA is
`bf87a0f0da035aab7ee1cbfc79abd3663586dc1d`,
after merge of independently full-Lean/256-TRUE-original-signed-input/allowed-axioms
CI-GREEN #606. Separate post-merge main CI is independently checked
and must not be invented.

Additional clean accepted results since the prior October-16 handoff:

- **#603**, exact head `959b8588`, full CI `38913649117`,
  merged SHA `56ef0c49`: proper-subalphabet k-stability
  transfers genuine ABO Definition-3.16 admissibility from a true
  incomplete H-Cayley A-skeleton to its canonical old-edge
  G-pullback when |A|≤k+1. This is a genuine algebraic-geometric
  portion of Theorem 4.7(i), NOT the other parts.
- **#604**, exact head `c71385fb`, full CI `38915487386`,
  merged SHA `4f796002`: for Q:G↠H stable on B, a rooted
  intrinsic B-component of a genuine incomplete G-pullback
  covers its H component BIJECTIVELY on actual OLD vertices
  AND all original formally oriented signed B-edge tokens
  with source inside that component. This strengthens mere
  relative path iff (#601) and keeps original B-component tags.
- **#606**, exact head `3afe8be5`, full CI `38916825856`,
  merged SHA `bf87a0f0`: map actual original G B-component
  INDEX tags to H indices (surjectively but NOT globally
  injectively), natural under B⊆C; transport each full
  component-tagged attached G[B] constituent to H, with a
  BIJECTION INSIDE the fixed coset under B-stability;
  preserve exact B⊆C attached-point enlargement and genuine
  shared (B∩C) support in the FORWARD direction G→H.

## Candidate geometry, NOT certified until exact head full CI GREEN

- **#605** head `ad96b6ee`, dependent only on already certified
  #604: specialize OLD vertex AND signed edge component bijections
  to literal first-rank groups G=T(X₂^all)→H=T(Y₁), for all
  proper B⊊A at |A|=2. Pending CI.
- **#607** head `76e9c285`: exact two-group *common old point*
  support lift. Given actual old G roots x,y with one common
  ambient g∈xG[B]∩yG[C], projected genuine H signed B/C
  paths to ONE H old z, and Q(g)∈zH[B∩C], produce ONE old
  G vertex t reached by genuine B/C paths from x/y and with
  g∈tG[B∩C]. Lift z inside gG[B∩C] by subgroup surjectivity;
  use stability separately on B/C to force both path-lift
  endpoints equal. No global group injectivity is assumed.
- **#608** head `0184fd23`, depends on #607, with exact
  source #607 blob temporarily embedded: reflect the ACTUAL
  ABO (3.10) component-tagged mixed B/C gluing relation
  from H to G IF the two original attached G points have
  the SAME G coordinate. The proof builds a genuine
  (B∩C)-attached G point with the exact original coordinate
  and common old intrinsic support. This is the NONTRIVIAL
  converse complement to certified #606.
- **#609** head `c20db2cb`, stacked on #608: prove the
  canonical ambient value map of FULL glued G multi-CE
  is injective, ASSUMING the corresponding H full multi-CE
  ambient map is already injective, Q stable on each selected
  proper B, genuine G/H admissibility and explicitly
  GENERATED AND GLOBALLY RETRACTABLE local groups. Also
  package rank-k bound |A|≤k+1 using certified #603.
  This is a conditional transfer/partial Theorem 4.7(ii),
  NOT a proof that source H-level CE is embedded, and
  NOT yet the original source's cover-based embedding proof.

**Dependency cleanup:** #608 source tree carries a temporary copy
of #607 pending independently green integration. After merging
#607, cleanly rebase #608 preserving only the NEW reflection
proof. #609 follows #608; after integrating parents,
retarget/rebase so its diff is only its own new theorem and import.
Never merge a red/pending head, nor call a stacked CI-green
status proof of main until all dependencies reconcile.

## The decisive mathematical source caveat

Corrected ABO Theorem 4.7(ii) proceeds in the source from
the fact that the chosen NEW G-Cayley graph covers the
LEGALLY completed H-level coset-extension stage. This
gives the necessary IDENTIFICATION of two H-component-
tagged stage points whenever they are reached from the
same G-group value via compatible OLD skeleton paths.

It does **NOT** follow merely from k-stability that the
old H multi-CE ambient coordinate map is globally injective.
The 3-vertex C₂×C₂ skeleton counterexample in
`ABO_HUMAN_GEOMETRY_SHORTCUT_AUDIT_2026-10-11.md`
shows that such ambient injectivity can be false even
with globally retractable groups and admissibility.
Thus #609's premise `hEmbeddedH` must NOT be
silently assumed as an induction invariant unless
that is specifically established for the chosen stage.

The actual *next* proof gate is the weaker, more precise
**G-equal-coordinate ⇒ H true mixed-support collision**
statement, derived from the already certified literal
T(X₂^all) based Cayley maps into genuine H plain/augmented
stages AND compatibility on each connected old G-cover
skeleton component. With that statement, candidate #608
would prove actual G multi-CE embeddedness without falsely
demanding H multi-CE ambient embeddedness.

Additional localization gate: globally our literal G and
H groups are only **2-retractable**, not retractable.
`LocalRankRetractableSubalphabet.lean` already proves
that the genuine subgroup generated by A, with outside-A
labels trivial, IS globally retractable for |A|≤2.
The generic full multiCE constructions in #609 use
Retractable genΓ/genΔ explicitly; source-specific
instantiation must use correctly localized G[A]/H[A]
and a compatible stable labelled quotient between these
local groups. This has NOT been discharged by #609 alone.

The later corrected Theorem 4.7(iii) B-bridge freeness
still uses the nontrivial cluster/augmentation alternatives,
including the full-B-coset repair R8; Condition 5.2 at
rank two, higher historical Yₖ/Zₖ induction, finite
reflecting group, concrete fibre-MAX and unconditional
closed-embedding PSTS EPPA remain OPEN.

## Honest status

The accepted main is advancing from rank-one finite group actions
to exactly the original tagged coset geometry. The most important
pending proof is mixed-support REFLECTION. The full EPPA theorem
is not yet Lean-certified. No new axiom or 'sorry' is justified.
