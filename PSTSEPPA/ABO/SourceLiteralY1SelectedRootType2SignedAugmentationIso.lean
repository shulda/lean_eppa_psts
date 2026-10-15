import PSTSEPPA.ABO.SourceLiteralY1SelectedRootOffBNoOldEdges
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootAmbientValueNaturality
import PSTSEPPA.ABO.LabelledMulEquivIsolatedAugmentationGraphIso

/-!
# Real original paper T(Y₁) selected rank-two off-B signed B-augmentation

The corrected ABO Definition 5.3 type-(2) attaches a NEW full
B-left coset to a selected OLD quotient point off the entire
actual component-tagged B-constituent. This is the genuine
INCOMPLETE signed coset EGraph before adding any missing loops,
and not the fake completed X₁ action. The attached coset anchor
is the verified actual ambient value of the chosen old quotient
vertex (which need not uniquely specify that vertex).

Earlier certified exact paper/source gluing and off-B index
naturality identify the selected old root in T(Y₁) with the
selected SourceH₁ old root. Source rank-two H₁[A] local geometry
proves that a genuine off-B root has NO old outgoing signed B
edge, making the fresh B-coset attachment deterministic. The
source/paper signed old graph isomorphism and generator-preserving
T(Y₁)≃*SourceH₁ map induce the actual old+NEW vertex/edge
bijection and commute with the correct new-root gluing.

The resulting morphism preserves both orientations, exact
signed labels and every genuine path, including repeated or
identity-labelled generators. No old vertices are identified
merely because ambient coordinates agree. Literal legal
fixed-loop completion, finite G₂ type-(2) word action, the
whole selected paper Z₁ catalogue and higher EPPA induction
remain separate proof gates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- A TRUE original printed T(Y₁) rank-two selected type-(2)
off-B root, retaining its actual exact-component-tagged glued
quotient point rather than a replacement ambient group value. -/
structure LiteralPaperSelectedOffBPoint
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets) where
  vertex : Quotient
    (sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root
      (allProperCosetFamily A))
  offB :
    ¬ ∃ p : (sourceLiteralY1DirectRootComponent
      src dst base A root).AttachedCosetVertex B,
      sourceLiteralY1SelectedRootBInclude
        src dst base A hcard root (allProperCosetFamily A)
        B hBP p = vertex

/-- Old genuine paper selected signed EGraph has no outgoing
old B-signed edge at the selected ACTUAL off-B vertex. -/
theorem LiteralPaperSelectedOffBPoint.paper_noOldBEdges
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root (allProperCosetFamily A)).NoSignedBEdgesAt
        B z.vertex :=
  sourceLiteralY1SelectedRoot_offB_noSignedEdges
    src dst base A hcard root B hBP z.vertex z.offB

/-- Old genuine SourceH₁ selected signed EGraph also has no
outgoing B-signed old edge at the EXACT transported off-B root. -/
theorem LiteralPaperSelectedOffBPoint.source_noOldBEdges
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root)
      (allProperCosetFamily A)).NoSignedBEdgesAt B
      ((sourceLiteralY1RootToH1MultiCosetVertexEquiv
        src dst base A hcard root (allProperCosetFamily A)) z.vertex) :=
  (sourceLiteralY1SelectedRoot_noSignedBEdgesAt_iff
    src dst base A hcard root (allProperCosetFamily A) B z.vertex).mp
    (z.paper_noOldBEdges src dst base A hcard root B hBP)

/-- Actual ORIGINAL paper signed old+fresh B-coset augmented
EGraph, with group anchor the real (noninjective) group value
of the selected tagged old-root quotient vertex. -/
noncomputable abbrev literalPaperSelectedOffBAugmentedEGraph
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :=
  IsolatedCosetGluing.gluedEGraph
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root (allProperCosetFamily A))
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    B
    (sourceLiteralY1SelectedRootAmbientValue
      src dst base A hcard root (allProperCosetFamily A) z.vertex)
    z.vertex
    (z.paper_noOldBEdges src dst base A hcard root B hBP)

/-- Actual SOURCE H₁ signed old+fresh B-coset augmented EGraph,
whose source anchor is the group-isomorphic image of the TRUE
paper ambient value. By independently checked value naturality,
this is exactly the source value of the transported root. -/
noncomputable abbrev literalPaperSelectedOffBSourceAugmentedEGraph
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :=
  IsolatedCosetGluing.gluedEGraph
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root)
      (allProperCosetFamily A))
    (sourceH1Generator src dst)
    B
    ((sourceH1EquivLiteralY1Transition src dst).symm
      (sourceLiteralY1SelectedRootAmbientValue
        src dst base A hcard root (allProperCosetFamily A) z.vertex))
    ((sourceLiteralY1RootToH1MultiCosetVertexEquiv
      src dst base A hcard root (allProperCosetFamily A)) z.vertex)
    (z.source_noOldBEdges src dst base A hcard root B hBP)

/-- The source-group anchor used for the newly attached B-coset
is literally the actual source-H₁ value of the transported OLD
tagged quotient root, never an arbitrary chosen representative. -/
theorem literalPaperSelectedOffBSourceAnchor_eq
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    (sourceH1EquivLiteralY1Transition src dst).symm
      (sourceLiteralY1SelectedRootAmbientValue
        src dst base A hcard root (allProperCosetFamily A) z.vertex) =
    sourceH1OriginalSelectedRootAmbientValue
      src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root)
        (allProperCosetFamily A)
        ((sourceLiteralY1RootToH1MultiCosetVertexEquiv
          src dst base A hcard root (allProperCosetFamily A)) z.vertex) :=
  sourceLiteralY1SelectedRootAmbientValue_natural
    src dst base A hcard root (allProperCosetFamily A) z.vertex

/-- ACTUAL original paper-to-source signed OLD+NEW type-(2)
graph morphism; old component tags and new fresh B-coset
points are transported separately, with one root glued. -/
noncomputable def literalPaperSelectedOffBAugmentedGraphHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    LabelledGraphHom
      (literalPaperSelectedOffBAugmentedEGraph
        src dst base A hcard root B hBP z).toLabelledGraph
      (literalPaperSelectedOffBSourceAugmentedEGraph
        src dst base A hcard root B hBP z).toLabelledGraph :=
  labelledMulEquivIsolatedAugmentationGraphHom
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root (allProperCosetFamily A))
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root)
        (allProperCosetFamily A))
    (sourceLiteralY1SelectedRootCompletedEGraphHom
      src dst base A hcard root (allProperCosetFamily A))
    (sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
      src dst base A hcard root (allProperCosetFamily A)).1
    (sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
      src dst base A hcard root (allProperCosetFamily A)).2
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1Generator src dst)
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    B
    (sourceLiteralY1SelectedRootAmbientValue
      src dst base A hcard root (allProperCosetFamily A) z.vertex)
    z.vertex
    (z.paper_noOldBEdges src dst base A hcard root B hBP)
    (z.source_noOldBEdges src dst base A hcard root B hBP)

/-- The ACTUAL newly augmented old+fresh paper/source type-(2)
signed EGraphs are bijective on ALL genuine old tagged vertices
and NEW non-root B-coset points, and on old/new formal
oriented signed edges, without collapsing ambient coordinates. -/
theorem literalPaperSelectedOffBAugmentedGraphHom_bijective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    Function.Bijective
      (literalPaperSelectedOffBAugmentedGraphHom
        src dst base A hcard root B hBP z).onVertex ∧
    Function.Bijective
      (literalPaperSelectedOffBAugmentedGraphHom
        src dst base A hcard root B hBP z).onEdge :=
  labelledMulEquivIsolatedAugmentationGraphHom_bijective
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root (allProperCosetFamily A))
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root)
        (allProperCosetFamily A))
    (sourceLiteralY1SelectedRootCompletedEGraphHom
      src dst base A hcard root (allProperCosetFamily A))
    (sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
      src dst base A hcard root (allProperCosetFamily A)).1
    (sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
      src dst base A hcard root (allProperCosetFamily A)).2
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1Generator src dst)
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    B
    (sourceLiteralY1SelectedRootAmbientValue
      src dst base A hcard root (allProperCosetFamily A) z.vertex)
    z.vertex
    (z.paper_noOldBEdges src dst base A hcard root B hBP)
    (z.source_noOldBEdges src dst base A hcard root B hBP)

/-- Every true signed OLD+NEW path in the literal paper selected
off-B type-(2) augmentation is preserved and reflected by the
source-H₁ augmentation, including negative labels and loops. -/
theorem literalPaperSelectedOffBAugmentedGraphHom_follows_iff
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP)
    (u v : (literalPaperSelectedOffBAugmentedEGraph
      src dst base A hcard root B hBP z).Vertex)
    (w : LabelWord ι) :
    (literalPaperSelectedOffBAugmentedEGraph
      src dst base A hcard root B hBP z).Follows u w v ↔
    (literalPaperSelectedOffBSourceAugmentedEGraph
      src dst base A hcard root B hBP z).Follows
      ((literalPaperSelectedOffBAugmentedGraphHom
        src dst base A hcard root B hBP z).onVertex u) w
      ((literalPaperSelectedOffBAugmentedGraphHom
        src dst base A hcard root B hBP z).onVertex v) :=
  labelledMulEquivIsolatedAugmentationGraphHom_follows_iff
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root (allProperCosetFamily A))
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root)
        (allProperCosetFamily A))
    (sourceLiteralY1SelectedRootCompletedEGraphHom
      src dst base A hcard root (allProperCosetFamily A))
    (sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
      src dst base A hcard root (allProperCosetFamily A)).1
    (sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
      src dst base A hcard root (allProperCosetFamily A)).2
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1Generator src dst)
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    B
    (sourceLiteralY1SelectedRootAmbientValue
      src dst base A hcard root (allProperCosetFamily A) z.vertex)
    z.vertex
    (z.paper_noOldBEdges src dst base A hcard root B hBP)
    (z.source_noOldBEdges src dst base A hcard root B hBP)
    u v w

end ABO
end PSTSEPPA
