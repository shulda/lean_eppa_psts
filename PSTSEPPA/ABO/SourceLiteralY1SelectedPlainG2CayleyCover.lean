import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainStageIso
import PSTSEPPA.ABO.SourceH1PlainActualG2WordAction
import PSTSEPPA.ABO.CompleteStageWordKernelTransport
import PSTSEPPA.ABO.CompleteStageWordCongruenceReachableCover

/-!
# The ACTUAL finite input-dependent G₂ acts on LITERAL paper T(Y₁) selected plain Z₁ stages

The genuine printed first-rank T(Y₁) old-input A-root (|A|=2)
complete ordinary P_A coset-extension action was proven isomorphic
ON ALL SIGNED EDGES AND VERTICES, including legally inserted
stationary missing-label loops, to its actual original source-H₁
A-root completed stage.

For the latter, the earlier independently certified source rank-two
all-local finite G₂ construction shows that equal chronological
signed G₂ word values induce exactly the same endpoint at EVERY
stage vertex. Transfer this whole signed-word action congruence
through the checked vertex-bijective complete-stage morphism BACK
to the literal printed stage.

Consequently the concrete finite source G₂ has a generator-preserving
action on each genuine printed selected plain stage, and a labelled
Cayley(G₂) graph cover based at EVERY vertex, hitting exactly the
reachable component, including every actual oriented signed action
edge token and missing-label fixed loop.

This is only the corrected Definition-5.3 PLAIN completed Z₁
stage; printed anchored type-(1) and off-B type-(2) augmentations,
full selected Z₁ family equality/equivariance, higher rank,
Condition 5.2, Theorem 4.7, reflecting group and PSTS EPPA
are NOT claimed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Equality of ACTUAL finite source G₂ group values of two signed
chronological words implies identical complete actions on EVERY
vertex of the LITERAL printed T(Y₁) original rank-two A-root
legally completed ordinary P_A stage. -/
theorem sourceG2LiteralY1SelectedPlain_wordValue_congr
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup (sourceAllLocalG2Generator src dst) q) :
    ∀ x,
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).followWord x p =
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).followWord x q := by
  let rootK := (sourceH1EquivLiteralY1Transition src dst).symm root
  let j : SourceOriginalH1CoverIndex src dst :=
    ⟨base, ⟨⟨A, hcard⟩, rootK⟩⟩
  let G := sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root
  let H := sourceH1OriginalRootPlainCompleteStage
    src dst base A hcard rootK
  let F := sourceLiteralY1SelectedRootPlainCompleteStageHom
    src dst base A hcard root
  have hSource : ∀ y, H.followWord y p = H.followWord y q := by
    exact sourceG2OriginalH1Plain_wordValue_congr src dst j p q hpq
  exact (G.wordActionCongr_iff_of_bijectiveHom H F
    (sourceLiteralY1SelectedRootPlainCompleteStageHom_bijective
      src dst base A hcard root).1 p q).mpr hSource

/-- A genuine generator-preserving based labelled Cayley(G₂)
morphism into the ACTUAL printed T(Y₁) legally completed
plain selected A-root action, NOT a model of an invented
X₁-complete old graph or an ambient coset-coordinate map. -/
noncomputable def sourceG2LiteralY1SelectedPlainCayleyHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root
        (allProperCosetFamily A))) :
    LabelledGraphHom
      (cayleyGraph (sourceAllLocalG2Generator src dst)).toEGraph.toLabelledGraph
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).toEGraph.toLabelledGraph :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).cayleyCoverFromWordCongruence
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1SelectedPlain_wordValue_congr
      src dst base A hcard root) u

/-- The true finite G₂-Cayley labelled graph cover begins
at the specified ACTUAL printed stage point. -/
theorem sourceG2LiteralY1SelectedPlainCayleyHom_one
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root
        (allProperCosetFamily A))) :
    (sourceG2LiteralY1SelectedPlainCayleyHom
      src dst base A hcard root u).onVertex 1 = u :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).cayleyCoverFromWordCongruence_one
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1SelectedPlain_wordValue_congr
      src dst base A hcard root) u

/-- The actual G₂-cover reaches precisely every vertex in
the source component of the specified printed selected
rank-one plain stage point, with NO spurious components. -/
theorem sourceG2LiteralY1SelectedPlainCayleyHom_vertex_range
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root
        (allProperCosetFamily A))) :
    Set.range (sourceG2LiteralY1SelectedPlainCayleyHom
      src dst base A hcard root u).onVertex =
    {v | (sourceLiteralY1SelectedRootPlainCompleteStage
      src dst base A hcard root).Reachable u v} :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).cayleyCoverFromWordCongruence_vertex_range
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1SelectedPlain_wordValue_congr
      src dst base A hcard root) u

/-- The Cayley(G₂) morphism maps onto EXACTLY the actual
oriented signed action-edge tokens whose sources are
reachable from its printed root, including fixed loops. -/
theorem sourceG2LiteralY1SelectedPlainCayleyHom_edge_range
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root
        (allProperCosetFamily A))) :
    Set.range (sourceG2LiteralY1SelectedPlainCayleyHom
      src dst base A hcard root u).onEdge =
    {e : ActionEdge (Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root
        (allProperCosetFamily A))) ι |
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).Reachable u
        ((sourceLiteralY1SelectedRootPlainCompleteStage
          src dst base A hcard root).source e)} :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).cayleyCoverFromWordCongruence_edge_range
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1SelectedPlain_wordValue_congr
      src dst base A hcard root) u

end ABO
end PSTSEPPA
