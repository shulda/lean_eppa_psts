import PSTSEPPA.ABO.RankTwoType2AllProperKernel
import PSTSEPPA.ABO.RankTwoType2OutsideAlphabet
import PSTSEPPA.ABO.RankOneAlphabetDichotomy

/-!
# Complete rank-one transition kernel of the ACTUAL type-(2) rank-two stage

Corrected ABO Proposition 5.4 at k=1 needs the word-kernel
test on EVERY subalphabet C with |C|≤1 of the entire
label set ι, not just the attached B or the original
rank-two parent A.

On the actual completed augmentation of the all-proper
multi-coset extension of a rank-two Cayley skeleton,
the preceding verified ingredients establish:

* For C PROPER in A, every C-supported word trivial in
  the ambient group fixes every vertex. The proof
  distinguishes C=B from C disjoint B and uses actual
  component/edge geometry rather than an invented
  action morphism at the attachment root.
* For C DISJOINT from A, every C-letter is absent from
  the genuine old and newly attached edge sets; hence
  arbitrary signed C-words act as the identity through
  the legal loop-only completion, with no need for
  ambient group triviality.
* Since |A|=2, each alphabet on ≤1 letter is exactly
  one of these two kinds.

Combining these proves the FULL per-stage rank-one
identity-word kernel, and by the complete-stage
action/transition-group equivalence, the transition
word value is 1 in the ACTUAL generated permutation
group for every ambient identity-valued singleton word.

This is the corrected R2 kernel for a genuine rank-two
type-(2) off-component singleton augmented stage. It
is NOT yet a finite Z1 family, an H1-cover, a map G2→H1,
or a proof that any such quotient is 1-stable.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- FULL rank-one R2 fixed-vertex criterion, quantified
over ALL alphabets C of size ≤1 in the ambient label set,
including labels outside the rank-two parent alphabet A. -/
theorem rankTwoOffComponentCompletedStage_rankOne_identity_word_fixes
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
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι)
    (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1)
    (v : IsolatedCosetGluing.Vertex
      (K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret)
      gen B
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le)
        hgen hret z)) :
    (K.rankTwoOffComponentCompletedStage
      hcard hgen hret B hBP z hOff).followWord v w = v := by
  rcases small_alphabet_proper_or_disjoint_rank_two
      A C hcard hCcard with hCA | hdis
  · have hCP : C ∈ (allProperCosetFamily A).alphabets :=
      (mem_allProperCosetFamily A C).mpr hCA
    exact K.rankTwoOffComponentCompletedStage_proper_C_identity_word_fixes
      hcard hgen hret B hBP z hOff C hCP w hw hval v
  · exact K.rankTwoOffComponentCompletedStage_outside_A_word_fixes
      hcard hgen hret B hBP z hOff C hdis w hw v

/-- The genuine type-(2) stage's transition-group word
value is identity for every ambient identity-valued word
supported on ANY alphabet of cardinality at most one.
This is the exact rank-one PER-STAGE word-kernel test. -/
theorem rankTwoOffComponentCompletedStage_rankOne_wordValue_eq_one
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
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι)
    (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (K.rankTwoOffComponentCompletedStage
      hcard hgen hret B hBP z hOff).wordValue w = 1 := by
  apply ((K.rankTwoOffComponentCompletedStage
    hcard hgen hret B hBP z hOff).wordValue_eq_one_iff_all_vertices_fixed w).mpr
  intro v
  exact K.rankTwoOffComponentCompletedStage_rankOne_identity_word_fixes
    hcard hgen hret B hBP z hOff C hCcard w hw hval v

end CayleySubgraphSpec
end ABO
end PSTSEPPA
