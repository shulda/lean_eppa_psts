import PSTSEPPA.ABO.SourceLiteralY1SelectedRootCompletedEGraphIso
import PSTSEPPA.ABO.RootedSourceAllProperCompletedStageIso
import PSTSEPPA.ABO.LocallyPairedGraphIso
import PSTSEPPA.ABO.TrivialLoopCompletionIsomorphism

/-!
# Legally completed P_A plain rank-one paper T(Y₁) selected Z₁ action

The full corrected ABO P_A family consists of ALL strictly proper
subalphabets B ⊂ A. At rank |A|=2, the completed ordinary
multi-coset extension of each genuine original-input A-root
component is weakly complete, hence has locally paired positive
and negative outgoing signed labels. The source H₁[A]-normalized
rank-two geometry proves this for its actual SourceH₁ root stage.
Our certified literal paper T(Y₁) root completed signed EGraph
isomorphism transfers the exact paired-edge condition backwards.

It is now legal to supply ONLY absent positive/negative labels
by stationary loops (with no extra artificial original X₁ edges).
The original paper selected-root P_A complete signed action
is isomorphic on every vertex and formal oriented signed edge
token to the actual source-H₁ selected-root complete action;
the equivalence preserves and reflects every realised signed
chronological word.

This is the selected first-rank PLAIN (unaugmented) complete
Definition-5.3 Z₁ stage. Anchored type-(1) and off-B type-(2)
augmented stages, exact printed whole Z₁ selection, higher
rank, Condition 5.2/Theorem 4.7 and unconditional PSTS EPPA
remain separate unfinished obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- TRUE source-H₁ original-input rank-two root P_A ordinary
proper-coset quotient has locally paired signed labels. Source-H₁
needs only two-retractability, never global retractability. -/
theorem sourceH1OriginalRootAllProper_locallyPaired
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst) :
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard root (allProperCosetFamily A)).LocallyPairedLabels := by
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let rootV : K.Vertex := ⟨root, by trivial⟩
  change
    (K.rootedAmbientMultiCosetCompletedEGraph A hcard
      (sourceH1_twoRetractable src dst) rootV
      (allProperCosetFamily A)).LocallyPairedLabels
  exact K.rootedAmbientAllProperMultiCoset_locallyPairedLabels
    A hcard (sourceH1_twoRetractable src dst) rootV

/-- ACTUAL printed paper T(Y₁) original signed A-root P_A
proper-coset quotient has paired positive/negative availability.
This is transported from source-H₁ through full signed graph
isomorphism, not assumed from a naive untagged Cayley completion. -/
theorem sourceLiteralY1SelectedRootAllProper_locallyPaired
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root
      (allProperCosetFamily A)).LocallyPairedLabels := by
  let P := allProperCosetFamily A
  let G := sourceLiteralY1SelectedRootCompletedEGraph src dst base A hcard root P
  let H := sourceH1OriginalRankTwoRootCompletedEGraph
    src dst base A hcard
    ((sourceH1EquivLiteralY1Transition src dst).symm root) P
  let F := sourceLiteralY1SelectedRootCompletedEGraphHom src dst base A hcard root P
  have hb := sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
    src dst base A hcard root P
  have hp : H.LocallyPairedLabels :=
    sourceH1OriginalRootAllProper_locallyPaired src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root)
  intro u i
  exact
    (G.signedEdgeExists_iff_of_bijective H F hb.1 hb.2 (.pos i) u).trans
      ((hp (F.onVertex u) i).trans
        (G.signedEdgeExists_iff_of_bijective H F hb.1 hb.2 (.neg i) u).symm)

/-- LITERAL PRINTED rank-one selected P_A plain COMPLETE action:
the genuine source paper ordinary multi-coset EGraph is made total
by inserting only missing positive/negative stationary loops. -/
noncomputable abbrev sourceLiteralY1SelectedRootPlainCompleteStage
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :=
  (sourceLiteralY1SelectedRootCompletedEGraph
    src dst base A hcard root
    (allProperCosetFamily A)).trivialLoopCompletion
      (sourceLiteralY1SelectedRootAllProper_locallyPaired
        src dst base A hcard root)

/-- The corresponding genuine original SOURCE-H₁ selected P_A
complete stage with the same minimal fixed-loop completion. -/
noncomputable abbrev sourceH1OriginalRootPlainCompleteStage
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst) :=
  (sourceH1OriginalRankTwoRootCompletedEGraph
    src dst base A hcard root
    (allProperCosetFamily A)).trivialLoopCompletion
      (sourceH1OriginalRootAllProper_locallyPaired
        src dst base A hcard root)

/-- The actual paper/source original selected rank-one ordinary
Z₁ complete-stage morphism preserves old B-coset transitions
and every newly added legal missing stationary loop, including
both orientations of signed generator labels. -/
noncomputable def sourceLiteralY1SelectedRootPlainCompleteStageHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).toEGraph.toLabelledGraph
      (sourceH1OriginalRootPlainCompleteStage
        src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).toEGraph.toLabelledGraph :=
  (sourceLiteralY1SelectedRootCompletedEGraph
    src dst base A hcard root
    (allProperCosetFamily A)).trivialLoopCompletionIsoHom
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
      (sourceLiteralY1SelectedRootAllProper_locallyPaired
        src dst base A hcard root)
      (sourceH1OriginalRootAllProper_locallyPaired
        src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root))

/-- The TRUE printed/source original selected rank-one P_A
legally complete actions are bijective on vertices AND all
formal oriented signed edge tokens, including inserted loops. -/
theorem sourceLiteralY1SelectedRootPlainCompleteStageHom_bijective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Bijective
      (sourceLiteralY1SelectedRootPlainCompleteStageHom
        src dst base A hcard root).onVertex ∧
    Function.Bijective
      (sourceLiteralY1SelectedRootPlainCompleteStageHom
        src dst base A hcard root).onEdge := by
  exact
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root (allProperCosetFamily A)).trivialLoopCompletionIsoHom_bijective
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
        (sourceLiteralY1SelectedRootAllProper_locallyPaired
          src dst base A hcard root)
        (sourceH1OriginalRootAllProper_locallyPaired
          src dst base A hcard
          ((sourceH1EquivLiteralY1Transition src dst).symm root))

/-- Every signed chronological word/path in the actual
PRINTED selected rank-one ordinary completed P_A stage is
preserved AND reflected in the corresponding genuine
source-H₁ original selected ordinary completed stage. -/
theorem sourceLiteralY1SelectedRootPlainCompleteStageHom_follows_iff
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u v : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root
        (allProperCosetFamily A)))
    (w : LabelWord ι) :
    (sourceLiteralY1SelectedRootPlainCompleteStage
      src dst base A hcard root).toEGraph.Follows u w v ↔
    (sourceH1OriginalRootPlainCompleteStage
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).toEGraph.Follows
      ((sourceLiteralY1SelectedRootPlainCompleteStageHom
        src dst base A hcard root).onVertex u)
      w
      ((sourceLiteralY1SelectedRootPlainCompleteStageHom
        src dst base A hcard root).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (sourceLiteralY1SelectedRootPlainCompleteStageHom src dst base A hcard root)
    (sourceLiteralY1SelectedRootPlainCompleteStageHom_bijective
      src dst base A hcard root).1
    (sourceLiteralY1SelectedRootPlainCompleteStageHom_bijective
      src dst base A hcard root).2
    u v w

end ABO
end PSTSEPPA
