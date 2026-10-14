import PSTSEPPA.ABO.SourceOriginalH1Z1ActualG2CayleyCover

/-!
# The actual finite source G₂ acts through the complete original rank-one stage transition group

The real input-dependent finite group G₂ already controls every chronological
signed-word action on the tagged three-kind original H₁ source-stage family.
The generic word-congruence theorem upgrades that statement to a genuine
generator-preserving SURJECTIVE group homomorphism to the transition subgroup
of the ENTIRE completed original source-stage action.

This gives a precise labelled quotient, not just a pointwise map of word
endpoints or a collection of individually rooted Cayley graph morphisms.
The target is the genuine transition group of the tagged original plain,
anchored type-(1) and root-translated type-(2) augmented completed stages.
No distinct original coset-component tags are identified by equality of their
H₁ ambient coordinates.

This is a rank-one source-stage certificate. Equivalence to the paper's
selected Definition-5.3 Z₁, corrected Condition 5.2, Theorem 4.7 and
higher-rank induction are separate open obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- A literal generator-preserving SURJECTIVE labelled group quotient
from the ACTUAL source G₂ to the true transition group of the entire
original H₁ three-kind signed complete source stage. -/
noncomputable def sourceOriginalH1Z1ActionQuotient
    (src dst : ι → V) :
    LabelledGroupQuotient
      (sourceAllLocalG2Generator src dst)
      (sourceOriginalH1Z1ThreeFamilyStage src dst).transitionSubgroupGenerator where
  hom :=
    (sourceOriginalH1Z1ThreeFamilyStage src dst).groupWordActionHom
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceOriginalH1Z1ThreeFamily_wordValue_congr src dst)
  map_gen := by
    intro i
    exact
      (sourceOriginalH1Z1ThreeFamilyStage src dst).groupWordActionHom_generator
        (sourceAllLocalG2Generator src dst)
        (sourceAllLocalG2Generator_isGenerated src dst)
        (sourceOriginalH1Z1ThreeFamily_wordValue_congr src dst) i
  surjective :=
    (sourceOriginalH1Z1ThreeFamilyStage src dst).groupWordActionHom_surjective
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceOriginalH1Z1ThreeFamily_wordValue_congr src dst)

/-- The quotient sends each ACTUAL signed G₂ word value to the
corresponding genuine completed original source action permutation.
In particular this includes formal negative letters and fixed loops. -/
theorem sourceOriginalH1Z1ActionQuotient_evalGroup
    (src dst : ι → V) (w : LabelWord ι) :
    (sourceOriginalH1Z1ActionQuotient src dst).hom
      (PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) w) =
      PSTS.SignedWord.evalGroup
        (sourceOriginalH1Z1ThreeFamilyStage src dst).transitionSubgroupGenerator w := by
  exact
    (sourceOriginalH1Z1ThreeFamilyStage src dst).groupWordActionHom_evalGroup
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceOriginalH1Z1ThreeFamily_wordValue_congr src dst) w

end ABO
end PSTSEPPA
