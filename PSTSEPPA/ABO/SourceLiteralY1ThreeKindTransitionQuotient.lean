import PSTSEPPA.ABO.SourceLiteralY1ThreeKindG2Action
import PSTSEPPA.ABO.CompleteStageWordCongruenceCayleyCover
import PSTSEPPA.ABO.SourceH1AllLocalG2

/-!
# Finite G₂ quotient onto the actual printed three-kind first-rank action

We use the entire REAL signed-word congruence already established
for the literal T(Y₁) three-kind completed stage superfamily:
ordinary rooted full proper-coset completions, anchored augmented
clusters, and genuine component-tagged off-B B-coset augmentations.

Its complete transition group is a generator-preserving SURJECTIVE
quotient of the explicitly finite input-derived source G₂.
The target is finite even without an independent finite enumeration
of its dependent stage indices: it is a surjective image of G₂.

This theorem does NOT identify this redundant all-choice family
with a particular equivariantly selected Definition-5.3 Z₁;
it does not establish Condition 5.2, Theorem 4.7,
the higher-rank construction, or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The TRUE group of transitions of every printed plain,
type-(1) and type-(2) completed signed stage, jointly, is
a labelled SURJECTIVE quotient of the concrete finite G₂.
No identification of distinct component-tagged old points
by their (possibly identical) ambient H₁ coordinates is used. -/
noncomputable def sourceLiteralY1ThreeKindActionQuotient
    (src dst : ι → V) :
    LabelledGroupQuotient
      (sourceAllLocalG2Generator src dst)
      (sourceLiteralY1ThreeKindStage src dst).transitionSubgroupGenerator where
  hom :=
    (sourceLiteralY1ThreeKindStage src dst).groupWordActionHom
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceG2LiteralY1ThreeKind_wordValue_congr src dst)
  map_gen := by
    intro i
    exact
      (sourceLiteralY1ThreeKindStage src dst).groupWordActionHom_generator
        (sourceAllLocalG2Generator src dst)
        (sourceAllLocalG2Generator_isGenerated src dst)
        (sourceG2LiteralY1ThreeKind_wordValue_congr src dst) i
  surjective :=
    (sourceLiteralY1ThreeKindStage src dst).groupWordActionHom_surjective
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceG2LiteralY1ThreeKind_wordValue_congr src dst)

/-- The quotient respects the evaluation of EVERY signed word,
including both formal inverse labels and legally added fixed loops. -/
theorem sourceLiteralY1ThreeKindActionQuotient_evalGroup
    (src dst : ι → V) (w : LabelWord ι) :
    (sourceLiteralY1ThreeKindActionQuotient src dst).hom
      (PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) w) =
      PSTS.SignedWord.evalGroup
        (sourceLiteralY1ThreeKindStage src dst).transitionSubgroupGenerator w := by
  exact
    (sourceLiteralY1ThreeKindStage src dst).groupWordActionHom_evalGroup
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceG2LiteralY1ThreeKind_wordValue_congr src dst) w

/-- The ACTUAL printed all-choice three-kind stage transition
group is finite as an IMAGE of finite G₂. Unlike a separate
finite-stage proof, this does not require knowing whether the
dependent index and vertex carrier are explicitly finite. -/
theorem finite_sourceLiteralY1ThreeKindTransitionGroup
    (src dst : ι → V) :
    Finite (sourceLiteralY1ThreeKindStage src dst).transitionGroup := by
  classical
  letI : Finite (sourceAllLocalG2 src dst) :=
    finite_sourceAllLocalG2 src dst
  exact Finite.of_surjective
    (sourceLiteralY1ThreeKindActionQuotient src dst).hom
    (sourceLiteralY1ThreeKindActionQuotient src dst).surjective

end ABO
end PSTSEPPA
