import PSTSEPPA.ABO.SourceLiteralY1SelectedRootType2SignedAugmentationIso
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainStageIso
import PSTSEPPA.ABO.IsolatedCosetCompletion
import PSTSEPPA.ABO.TrivialLoopCompletionIsomorphism

/-!
# Genuine literal-paper T(Y₁) OFF-B type-(2) legally complete signed action

The actual selected original paper rank-two off-B type-(2)
old+new signed EGraph is obtained by gluing a fresh full B-left
coset to its one true old tagged selected quotient root. The
source-side B-left coset anchor is the image of the actual paper
ambient root value under T(Y₁)≃*SourceH₁, which was certified
equal to the true source group value of the transported root.

Both unaugmented old FULL P_A coset quotient EGraphs are locally
paired in the signed-label sense, and the new full B-coset adds
both signs of its generators at every attached point. Thus
the augmented OLD+NEW signed EGraphs remain locally paired, so
the canonical completion by ONLY missing stationary signed
loops is legal. A genuine old/new signed graph isomorphism
then extends to a vertex- and oriented action-edge-bijective
isomorphism of these COMPLETE stages and reflects all signed
chronological paths.

The proof retains real component tags, actual off-B membership
and edge absence, formal inversion and all new fixed loops.
It does NOT supply G₂ word kernel at the type-(2) stage nor
assert exact whole selected Definition-5.3 Z₁ equivalence,
higher rank Condition 5.2/Theorem 4.7 or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Selected literal paper old+fresh off-B signed EGraph has
locally paired positive/negative outgoing labels, including
the attachment root, because its OLD original proper-family
P_A stage is locally paired and the new coset is FULL. -/
theorem literalPaperSelectedOffBAugmented_locallyPaired
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    (literalPaperSelectedOffBAugmentedEGraph
      src dst base A hcard root B hBP z).LocallyPairedLabels :=
  IsolatedCosetGluing.glued_locallyPairedLabels
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root (allProperCosetFamily A))
    (sourceLiteralY1 src dst).transitionSubgroupGenerator B
    (sourceLiteralY1SelectedRootAmbientValue
      src dst base A hcard root (allProperCosetFamily A) z.vertex)
    z.vertex (z.paper_noOldBEdges src dst base A hcard root B hBP)
    (sourceLiteralY1SelectedRootAllProper_locallyPaired src dst base A hcard root)

/-- The actual transported SourceH₁ selected old+fresh off-B
signed augmented EGraph likewise has locally paired labels,
using the genuine old rank-two source P_A stage. -/
theorem literalPaperSelectedOffBSourceAugmented_locallyPaired
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    (literalPaperSelectedOffBSourceAugmentedEGraph
      src dst base A hcard root B hBP z).LocallyPairedLabels :=
  IsolatedCosetGluing.glued_locallyPairedLabels
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root)
      (allProperCosetFamily A))
    (sourceH1Generator src dst) B
    ((sourceH1EquivLiteralY1Transition src dst).symm
      (sourceLiteralY1SelectedRootAmbientValue
        src dst base A hcard root (allProperCosetFamily A) z.vertex))
    ((sourceLiteralY1RootToH1MultiCosetVertexEquiv
      src dst base A hcard root (allProperCosetFamily A)) z.vertex)
    (z.source_noOldBEdges src dst base A hcard root B hBP)
    (sourceH1OriginalRootAllProper_locallyPaired src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root))

/-- The TRUE printed selected off-B type-(2) COMPLETE action,
adding only missing stationary ±loops to its genuine signed
old+fresh B-coset augmentation. -/
noncomputable abbrev literalPaperSelectedOffBCompletedStage
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :=
  (literalPaperSelectedOffBAugmentedEGraph
    src dst base A hcard root B hBP z).trivialLoopCompletion
      (literalPaperSelectedOffBAugmented_locallyPaired
        src dst base A hcard root B hBP z)

/-- The corresponding genuine SourceH₁ selected off-B
type-(2) complete signed action at the correctly transported
new coset anchor and the correctly glued old root. -/
noncomputable abbrev literalPaperSelectedOffBSourceCompletedStage
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :=
  (literalPaperSelectedOffBSourceAugmentedEGraph
    src dst base A hcard root B hBP z).trivialLoopCompletion
      (literalPaperSelectedOffBSourceAugmented_locallyPaired
        src dst base A hcard root B hBP z)

/-- Genuine isomorphism of literal T(Y₁) and SourceH₁ legally
COMPLETE original selected off-B type-(2) actions, including
all old/fresh vertices and all formal signed action-edge
tokens, both added and stationary. -/
noncomputable def literalPaperSelectedOffBCompletedStageHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    LabelledGraphHom
      (literalPaperSelectedOffBCompletedStage
        src dst base A hcard root B hBP z).toEGraph.toLabelledGraph
      (literalPaperSelectedOffBSourceCompletedStage
        src dst base A hcard root B hBP z).toEGraph.toLabelledGraph :=
  (literalPaperSelectedOffBAugmentedEGraph
    src dst base A hcard root B hBP z).trivialLoopCompletionIsoHom
    (literalPaperSelectedOffBSourceAugmentedEGraph
      src dst base A hcard root B hBP z)
    (literalPaperSelectedOffBAugmentedGraphHom
      src dst base A hcard root B hBP z)
    (literalPaperSelectedOffBAugmentedGraphHom_bijective
      src dst base A hcard root B hBP z).1
    (literalPaperSelectedOffBAugmentedGraphHom_bijective
      src dst base A hcard root B hBP z).2
    (literalPaperSelectedOffBAugmented_locallyPaired
      src dst base A hcard root B hBP z)
    (literalPaperSelectedOffBSourceAugmented_locallyPaired
      src dst base A hcard root B hBP z)

/-- Completed printed/source selected type-(2) action
isomorphism is vertex/ORIENTED signed-action-edge bijective,
preserving new coset and inserted fixed loops without merging
different tagged old quotient vertices. -/
theorem literalPaperSelectedOffBCompletedStageHom_bijective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    Function.Bijective
      (literalPaperSelectedOffBCompletedStageHom
        src dst base A hcard root B hBP z).onVertex ∧
    Function.Bijective
      (literalPaperSelectedOffBCompletedStageHom
        src dst base A hcard root B hBP z).onEdge :=
  (literalPaperSelectedOffBAugmentedEGraph
    src dst base A hcard root B hBP z).trivialLoopCompletionIsoHom_bijective
    (literalPaperSelectedOffBSourceAugmentedEGraph
      src dst base A hcard root B hBP z)
    (literalPaperSelectedOffBAugmentedGraphHom
      src dst base A hcard root B hBP z)
    (literalPaperSelectedOffBAugmentedGraphHom_bijective
      src dst base A hcard root B hBP z).1
    (literalPaperSelectedOffBAugmentedGraphHom_bijective
      src dst base A hcard root B hBP z).2
    (literalPaperSelectedOffBAugmented_locallyPaired
      src dst base A hcard root B hBP z)
    (literalPaperSelectedOffBSourceAugmented_locallyPaired
      src dst base A hcard root B hBP z)

end ABO
end PSTSEPPA
