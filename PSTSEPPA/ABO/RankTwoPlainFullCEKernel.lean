import PSTSEPPA.ABO.RankTwoCompletedWordKernel
import PSTSEPPA.ABO.StageStabilityWordKernel
import PSTSEPPA.ABO.AllProperCosetEdgeSupport
import PSTSEPPA.ABO.RankOneAlphabetDichotomy

/-!
# Complete rank-one kernel for the genuine UNaugmented rank-two full CE stage

The already certified rank-two completed full coset-extension theorem
establishes that words supported by any selected proper alphabet
C⊂A and trivial in the ambient group fix all stage vertices.

Corrected ABO Proposition 5.4 k=1, however, requires checking
ALL singleton labels in the full generator universe, including
labels OUTSIDE A. The true multi-coset EGraph has no original
edges outside A, and legal loop-only completion fixes every
vertex under all such signed labels.

Since |A|=2, any alphabet C of cardinality ≤1 is either
proper in A or disjoint from A. The two genuine stage
theorems therefore combine into the entire rank-one
kernel, both as all-vertex word action and as the actual
transition-group word value.

This is the plain full CE part of the source's Z₁ catalogue;
it does not construct the entire H₁-cover or its new group.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every ambient identity-valued word on ANY ≤1-letter
alphabet fixes EVERY vertex of the actual rank-two
completed full proper-alphabet coset extension,
including letters which lie outside the parent A. -/
theorem rankTwo_completedStage_rankOne_identity_word_fixes
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι)
    (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret) :
    (K.allProperCompletedStage
      (K.admissible_of_card_le_two hcard.le)
      hgen hret hcard.ge).followWord z w = z := by
  rcases small_alphabet_proper_or_disjoint_rank_two
      A C hcard hCcard with hCA | hdis
  · have hCP : C ∈ (allProperCosetFamily A).alphabets :=
      (mem_allProperCosetFamily A C).mpr hCA
    exact K.rankTwo_completedStage_identity_B_word_fixes
      hcard hgen hret C hCP w hw hval z
  · exact K.allProperCompletedStage_disjoint_word_fixes
      (K.admissible_of_card_le_two hcard.le)
      hgen hret hcard.ge C hdis w hw z

/-- The rank-one signed-word kernel of the actual
plain rank-two full coset-extension TRANSITION GROUP.
This is the exact form used to synchronize the
type-(1), type-(2), and unaugmented stage factors. -/
theorem rankTwo_completedStage_rankOne_wordValue_eq_one
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι)
    (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (K.allProperCompletedStage
      (K.admissible_of_card_le_two hcard.le)
      hgen hret hcard.ge).wordValue w = 1 := by
  apply ((K.allProperCompletedStage
      (K.admissible_of_card_le_two hcard.le)
      hgen hret hcard.ge).wordValue_eq_one_iff_all_vertices_fixed w).mpr
  intro z
  exact K.rankTwo_completedStage_rankOne_identity_word_fixes
    hcard hgen hret C hCcard w hw hval z

end CayleySubgraphSpec
end ABO
end PSTSEPPA
