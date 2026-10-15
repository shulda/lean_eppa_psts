import PSTSEPPA.ABO.SourceLiteralY1SelectedRootRawGraphIso
import PSTSEPPA.ABO.SourceLabelEdgeQuotientGraphIso

/-!
# ACTUAL selected paper T(Y₁) root-A complete signed multi-coset EGraph

Corrected ABO's first-rank selected paper H₁=T(Y₁) original-input
old A-component is an actual INCOMPLETE Cayley subgraph with
|A|=2, not its containing ambient group A-coset. We have certified:

* its true vertex/edge-bijective signed graph correspondence with
  the source H₁ original-root component;
* exact component-tagged B-coset attachments and original B∩C
  gluing SETOID for every proper-alphabet family;
* bijections of ALL actual old outside-B and fresh inside-B signed
  raw edges and a true signed RAW graph isomorphism; and
* source H₁'s unconditional rank-two raw source-and-full-signed-label
  target congruence via the local H₁[A] model, without assuming
  globally retractable H₁.

We TRANSPORT the genuine target congruence BACK to the literal
paper selected A-root. Then quotient real raw oriented edges
by their exactly glued SOURCE and full SIGNED LABEL, preserving
formal inversion, to obtain the true deterministic completed
proper-family multi-coset EGraph. A genuine vertex-and-oriented-
edge-bijective labelled graph isomorphism to the independently
constructed source-H₁ completed rank-two EGraph follows, with
reflection of all chronological signed paths.

This is the PLAIN selected completed coset-extension gate.
It does NOT yet identify legal outside-A fixed-loop completion or
selected anchored type-(1)/off-B type-(2) augmentations, prove
all printed Z₁ stage family completeness/equivariance, higher rank
Condition 5.2/Theorem 4.7 or unconditional PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Source-and-SIGNED-label target congruence for the ACTUAL
selected original-input paper T(Y₁) rooted A-component raw
multi-coset graph, obtained from real source H₁[A] rank-two
geometry, not global retractability of T(Y₁). -/
theorem sourceLiteralY1SelectedRootRawGraph_target_congruent
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    (sourceLiteralY1SelectedRootRawGraph
      src dst base A hcard root P).SourceLabelTargetCongruent := by
  let G := sourceLiteralY1SelectedRootRawGraph src dst base A hcard root P
  let H := sourceH1OriginalRankTwoRootRawGraph
    src dst base A hcard
    ((sourceH1EquivLiteralY1Transition src dst).symm root) P
  let F := sourceLiteralY1SelectedRootRawGraphHom
    src dst base A hcard root P
  have hb := sourceLiteralY1SelectedRootRawGraphHom_bijective
    src dst base A hcard root P
  intro e f hs hl
  have hsrc : H.source (F.onEdge e) = H.source (F.onEdge f) := by
    calc
      H.source (F.onEdge e) = F.onVertex (G.source e) := F.map_source e
      _ = F.onVertex (G.source f) := congrArg F.onVertex hs
      _ = H.source (F.onEdge f) := (F.map_source f).symm
  have hlabel : H.label (F.onEdge e) = H.label (F.onEdge f) := by
    calc
      H.label (F.onEdge e) = G.label e := F.map_label e
      _ = G.label f := hl
      _ = H.label (F.onEdge f) := (F.map_label f).symm
  have htarget :
      H.target (F.onEdge e) = H.target (F.onEdge f) :=
    (sourceH1OriginalRankTwoRootRawGraph_target_congruent
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root) P)
      (F.onEdge e) (F.onEdge f) hsrc hlabel
  apply hb.1.1
  calc
    F.onVertex (G.target e) = H.target (F.onEdge e) :=
      (F.map_target e).symm
    _ = H.target (F.onEdge f) := htarget
    _ = F.onVertex (G.target f) := F.map_target f

/-- The TRUE deterministic signed completed multi-coset EGraph
for the literal paper T(Y₁) original signed root A-component.
The vertex Setoid is exact B∩C support, while directed raw edges
are identified by the already GLUED source and full signed label. -/
noncomputable abbrev sourceLiteralY1SelectedRootCompletedEGraph
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :=
  sourceLabelGraphQuotientEGraph
    (sourceLiteralY1SelectedRootRawGraph src dst base A hcard root P)
    (sourceLiteralY1SelectedRootRawGraph_target_congruent
      src dst base A hcard root P)

/-- A genuine paper→source isomorphism of selected rank-two
completed full proper-family multi-coset signed EGraphs,
bijective on the EXACT glued vertex quotient and quotient
classes of formal oriented signed raw edge tokens. -/
noncomputable def sourceLiteralY1SelectedRootCompletedEGraphHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    LabelledGraphHom
      (sourceLiteralY1SelectedRootCompletedEGraph
        src dst base A hcard root P).toLabelledGraph
      (sourceH1OriginalRankTwoRootCompletedEGraph
        src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root) P).toLabelledGraph :=
  sourceLabelGraphQuotientHom
    (sourceLiteralY1SelectedRootRawGraph src dst base A hcard root P)
    (sourceH1OriginalRankTwoRootRawGraph
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root) P)
    (sourceLiteralY1RootToH1MultiCosetVertexEquiv
      src dst base A hcard root P)
    (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv
      src dst base A root P)
    (sourceLiteralY1SelectedRootRawGraph_source_natural
      src dst base A hcard root P)
    (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv_label
      src dst base A root P)
    (fun e => (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv_inv
      src dst base A root P e).symm)
    (sourceLiteralY1SelectedRootRawGraph_target_congruent
      src dst base A hcard root P)
    (sourceH1OriginalRankTwoRootRawGraph_target_congruent
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root) P)

/-- True selected original paper T(Y₁) and source H₁ rank-two
completed multi-coset graph vertex/edge equivalences. -/
theorem sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    Function.Bijective
      (sourceLiteralY1SelectedRootCompletedEGraphHom
        src dst base A hcard root P).onVertex ∧
    Function.Bijective
      (sourceLiteralY1SelectedRootCompletedEGraphHom
        src dst base A hcard root P).onEdge :=
  sourceLabelGraphQuotientHom_bijective
    (sourceLiteralY1SelectedRootRawGraph src dst base A hcard root P)
    (sourceH1OriginalRankTwoRootRawGraph
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root) P)
    (sourceLiteralY1RootToH1MultiCosetVertexEquiv
      src dst base A hcard root P)
    (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv
      src dst base A root P)
    (sourceLiteralY1SelectedRootRawGraph_source_natural
      src dst base A hcard root P)
    (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv_label
      src dst base A root P)
    (fun e => (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv_inv
      src dst base A root P e).symm)
    (sourceLiteralY1SelectedRootRawGraph_target_congruent
      src dst base A hcard root P)
    (sourceH1OriginalRankTwoRootRawGraph_target_congruent
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root) P)

/-- All true signed word paths in the literal selected paper
completed multi-coset quotient exist if and only if they exist
in the corresponding actual source H₁ selected completed graph.
Includes inverse letters, missing old signed edges and identity
group generators. No ambient Cayley map injectivity assumed. -/
theorem sourceLiteralY1SelectedRootCompletedEGraphHom_follows_iff
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (u v : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root P))
    (w : LabelWord ι) :
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root P).Follows u w v ↔
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root) P).Follows
      ((sourceLiteralY1SelectedRootCompletedEGraphHom
        src dst base A hcard root P).onVertex u)
      w
      ((sourceLiteralY1SelectedRootCompletedEGraphHom
        src dst base A hcard root P).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (sourceLiteralY1SelectedRootCompletedEGraphHom
      src dst base A hcard root P)
    (sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
      src dst base A hcard root P).1
    (sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
      src dst base A hcard root P).2 u v w

end ABO
end PSTSEPPA
