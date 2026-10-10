import PSTSEPPA.ABO.RankTwoType2GlobalWordKernel
import PSTSEPPA.ABO.StageStabilityWordKernel

/-!
# Rank-two type-(2) transition-group kernel (corrected ABO R2)

The source's Proposition 5.4 R2 needs a statement about ACTUAL
transition-group values, not merely the completed EGraph's path
relation or a chosen vertex. The rank-two type-(2) whole-vertex
word-kernel theorem, together with the checked equivalence between
triviality of transition-group values and pointwise trivial action,
implies exactly this stronger group-valued claim.

For any selected proper B in an alphabet A of cardinality two,
and any genuinely augmented off-B singleton component,
every B-supported signed word that evaluates to 1 in the
ambient group also evaluates to 1 in the full completed
augmentation's transition group. This includes negative
letters, degenerate labels and all old/new vertices.

This closes the source-facing transition KERNEL test for each
individual stage of this type; identifying and assembling
all stages into the finite Z1 and giving an actual G2→H1
quotient is additional work.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- In the genuine rank-two type-(2) completed augmentation,
an ambient identity-valued signed B-word has identity value in
the ACTUAL labelled transition group. -/
theorem rankTwoOffComponentCompletedStage_wordValue_eq_one
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret)
    (hOff : ¬ ∃ q : K.AttachedCosetVertex B,
      K.multiCosetInclude (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le)
        hgen hret B hBP q = z)
    (w : LabelWord ι)
    (hw : LabelWord.Uses B w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (K.rankTwoOffComponentCompletedStage
      hcard hgen hret B hBP z hOff).wordValue w = 1 := by
  apply ((K.rankTwoOffComponentCompletedStage
    hcard hgen hret B hBP z hOff).wordValue_eq_one_iff_all_vertices_fixed w).mpr
  intro v
  exact K.rankTwoOffComponentCompletedStage_identity_B_word_fixes
    hcard hgen hret B hBP z hOff w hw hval v

end CayleySubgraphSpec
end ABO
end PSTSEPPA
