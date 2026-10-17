# 2026-10-17 — Literal printed first-rank fully LOCAL signed P_A stage cover: audited checkpoint

## Authoritative verification cutoff

The last accepted mathematical main on inspection was
`88067976cc16052f89b4e97e78e54d50a72d7044` (merged #630).
The ORIGINAL full-Lean exact-source-head, 256 actual original
signed-input regression cases, and permitted-axioms audit
for #630 was GREEN (run `38992141734`). The independent
postmerge main check (run `38992591852`) was still
IN PROGRESS at this dated snapshot. The earlier main
`def5e7271537a9ae290680202fd85256ea935494`,
after #626, had independent fully GREEN main CI run
`38991780164`.

### Newly integrated mathematical results

- **#626**: an ACTUAL incomplete signed A-Cayley skeleton on the
  true generated subgroup G[A], retaining precisely formal
  positive/negative original A-edges, has an authentic labelled
  graph map to every selected ORIGINAL printed paper
  T(Y₁)-rooted, legally completed P_A stage. Correct root is
  the actual OLD component-tagged paper quotient point. Does
  NOT claim a complete local Cayley(G[A]) action outside A.
- **#627**: every genuine original intrinsic A-component, its
  normalized local A-coset slice, and (given source assumptions)
  the full ORIGINAL tagged P_A multi-coset extension including
  every FRESH quotient vertex are genuinely A-WORD CONNECTED.
  LEGAL completion by only missing signed stationary loops
  preserves all the old paths and this connectedness.
- **#630**, the mathematical next step: for arbitrary genuine
  complete signed EGraph T and an ACTUAL labelled surjective
  quotient G↠Transition(T), restrict to genuine G[A] and
  assume every actual transition outside A is trivial.
  This constructs an honest FULL signed Cayley(G[A])→T
  graph morphism based at any stage vertex u, with exact
  identity image. If T is A-WORD CONNECTED from u, the map
  is SURJECTIVE ON EVERY genuine stage VERTEX and EVERY
  formal ORIENTED signed EDGE, including negative and
  stationary outside-A loops. This does not assume
  global G/H ambient injectivity or generator freeness.

## Candidate dependency DAG: exact HEAD full CI required

- **#628**, corrected HEAD `aa91642b3c2ebade1d4924765c84451773b40153`,
  PR CI `38991800669` pending at snapshot:
  `SourceLiteralY1SelectedRootPlainAConnected.lean`.
  Transfers FULL old/fresh A-word connectedness across
  actual source-local → SourceH₁ → literal T(Y₁) rooted
  P_A complete-stage bijections, preserving every signed
  word. Concludes surjectivity of local G[A] old/fresh
  orbit map onto entire actual PRINTED selected stage.
  Original red head `74900b32deac` had two
  Lean source-target `hom_followWord` argument order
  errors at lines 60, 81; corrected source calls
  `G.hom_followWord H f` now undergoing full CI.
- **#629**, corrected HEAD `978a9cc9218410e3c02d9979b27ab61b782941b8`,
  PR CI `38992508100` pending:
  `MultiCosetSignedParentSupport.lean`.
  Strengthens certified parent-alphabet label support
  from all-proper P_A to arbitrary proper selected
  `CosetFamilySpec A`, proving every true signed
  directed raw/quotient old/fresh edge label belongs to A;
  legal fixed-loop completion acts stationarily outside A.
  Important repair: original standalone previous
  commit `714e0a275705` passed a push check but was
  NEVER imported into PSTSEPPA.lean; initial genuine
  full import CI exposed a parser error, then a DUPLICATE
  `singleCosetEdge_label_mem_parent` already provided
  by `AllProperCosetEdgeSupport.lean`.
  Current head reuses existing certified source theorem,
  defines only genuinely new generalized corollaries.
- **#631**, current source HEAD `bb8edc47cc9c94781017d7fe21774de6abd8e64a`,
  stacked on #629 (child branch cleanly rebased as
  `0fcb00dc2ef3210e835bb06892ffb5227ba64892`
  then two syntactic fixes); latest exact-source PR
  CI `38992711137` pending:
  `SourceLiteralY1SelectedRootPlainOutsideASupport.lean`.
  Checks label support for each EXACT original selected
  PRINTED T(Y₁) root-A proper multi-CE signed RAW token,
  descends through the source+FULL-SIGNED-label edge
  quotient, concludes stationarity of outside-A signed
  letters on ALL genuine tagged old/fresh stage vertices
  and actual subgroup generator equality to 1.
  One cannot replace OLD gluing by equal ambient H values.
- **#632**, actual source main goal, branch after fixes
  head `b9f090122fe0282044daca02f2d2d325fcba6be5`,
  PR CI `38992741873` pending, stacked on #631
  but temporarily includes EXACT NEW SOURCE BLOBS for
  #628 and #630 for a full Lean compile:
  `SourceLiteralY1SelectedRootFullLocalCayleyCover.lean`.
  Build the ACTUAL full signed local
  Cayley(T(X₂^all)[A]) → every literal PRINTED
  original-root completed P_A stage for |A|=2,
  based at any actual old/fresh tagged stage vertex.
  Prove surjective on FULL vertex and directed signed
  edge sorts. This combines #628 real A-connectedness,
  #629/#631 true outside-A fixed transitions and
  independently accepted #630 generic local-cover theorem,
  with already-certified actual transition quotient
  T(X₂^all)↠Transition(P_A stage).
  **DO NOT MERGE** until ancestor independent
  exact-head full CI green, then CLEAN rebase #632
  diff to only its new source file/root import, and
  run another exact-head full CI.

### Strongest source-facing implications and honest remaining gates

The local completely signed Cayley(G[A])→actual H completed P_A
cover is a *precondition* of the corrected two-group
Theorem 4.7(ii), not automatically the final G coset
extension's ambient embedding.

Already accepted #617–#620: One ACTUAL root-normalized
G Cayley covering of an exact legally completed
H component-tagged stage, aligned with the ORIGINAL
incomplete old skeleton along genuine A-paths, forces
precise B/C tagged image equality and the
`B∩C` gluing relation upstairs. This establishes
the genuine FULL coset-extension Cayley ambient map
INJECTIVE **ON THE IMAGE OF THE ONE SELECTED ORIGINAL
G OLD A-COMPONENT**, not on all unrelated disconnected
A-components. Do not assume a whole-pullback
connectedness or global H-multiCE ambient embedding.

**Next mathematical bottleneck after #632**:
Connect the new literal local full signed G[A]-cover
to the exact TRUE local OLD H[A] skeleton and selected
G[A] OLD component under the verified original G/H
quotient slice/pullback compatibility (#616). Align
the selected local G root and its H-old genuine tag
with the actual old anchor of the printed stage, via
the existing source/local/paper signed graph
isomorphisms, then instantiate the corrected
component-scoped embeddedness from #619/#620. A
group-Cayley morphism and vertex surjectivity alone
do NOT assert this OLD original-edge compatibility.

After embeddedness, Theorem 4.7(iii) still requires
the source's separate cluster/augmentation
alternatives, especially **full B-coset repair R8**,
and genuine G-external B-BRIDGE FREENESS. The
full rank-two cluster base is independently
certified, as are signed loop-stripping and
genuine old coset B-path-lifting, but those do
not alone establish the entire source bridge argument.

Final ordinary finite PSTS EPPA for closed embeddings
still requires Condition 5.2 at rank 2,
higher k≥2 historical Yₖ/Zₖ stage word kernels
and exact equivariant Definition 5.3 Zₖ selection,
higher-rank corrected Theorem 4.7 and bridge
geometries, finite reflecting group and fibre-MAX.
**NO unconditional PSTS EPPA theorem yet**.

## Safe crash recovery

Check `main` SHA and the PR HEADs for #628,
#629, #631, #632 and exact HEAD CI run conclusions
from GitHub. Do not infer PR status from stale
standalone branch push CI. Do not merge red or
pending exact heads. Retarget and cleanly rebase
stacked PRs in dependency order; each new head
needs independent complete Lean + 256 genuine
signed original input regressions and axiom audit.
If a session stops without a reply, these changes
remain auditable in GitHub. User decisions are
not needed to continue this mathematical work.
