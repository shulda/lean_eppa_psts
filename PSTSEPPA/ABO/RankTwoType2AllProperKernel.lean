import PSTSEPPA.ABO.IsolatedCosetDisjointCompletedWords
import PSTSEPPA.ABO.RankTwoType2TransitionKernel
import PSTSEPPA.ABO.RankTwoCompletedWordKernel

/-!
# Every proper singleton-alphabet kernel for the ACTUAL rank-two type-(2) stage

The k=1 R2 repair must check all singleton-labelled words,
NOT ONLY those supported by the newly attached B-coset.

For an actual rank-two full coset extension and a singleton
augmentation along an off-B root:
* C disjoint from B: the generic completed C-word action
  transport proves new vertices are fixed and old completed
  actions agree exactly. The old rank-two completed stage
  already has the required identity-valued C-word kernel.
* C meeting B: since |A|=2 and both C,B are PROPER
  subalphabets of A, they share a letter only if C=B.
  The previously certified global attached-B word kernel
  applies directly.

Consequently every ambient identity-valued signed C-word for
EVERY PROPER C⊂A fixes EVERY vertex of the true completed
type-(2) singleton-augmented stage. This closes the per-stage
rank-one word-kernel test for labels INSIDE A, not yet for
generator labels outside A (handled separately by the
no-out-of-alphabet edge invariant).

The actual finite H1-cover Z1 catalogue and G2→H1 quotient
remain additional, independent construction obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- When the requested C alphabet is disjoint from the newly
attached full B-coset, its entire completed word action is
inherited from the old rank-two stage, including at root;
the new points have only trivial C-loops. -/
theorem rankTwoOffComponentCompletedStage_disjoint_C_identity_word_fixes
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
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hdis : Disjoint C B)
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
  let hadm : K.AdmissibleForCosetExtension :=
    K.admissible_of_card_le_two hcard.le
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let g : Γ := K.multiCosetAmbientValue P hadm hgen hret z
  let hpaired : G.LocallyPairedLabels :=
    K.rankTwo_fullProperCE_locallyPaired hcard hgen hret
  have hMissing : ∀ e : K.MultiCosetEdgeVertexIncidenceQuotient
      P hadm hgen hret,
      G.source e = z → signedBase (G.label e) ∉ B := by
    intro e he
    exact K.rank_two_off_selected_B_no_outgoing_edges
      hcard.le hgen hret B hBP z hOff e he
  have hOldKernel :
      ∀ x : K.MultiCosetVertex P hadm hgen hret,
        (G.trivialLoopCompletion hpaired).followWord x w = x := by
    intro x
    exact K.rankTwo_completedStage_identity_B_word_fixes
      hcard hgen hret C hCP w hw hval x
  exact IsolatedCosetGluing.completedStage_disjoint_C_word_kernel
    G gen B g z hMissing hpaired C hdis w hw hOldKernel v

/-- For EVERY selected proper alphabet C⊂A at rank two,
not just the attached B, identity-valued C-words fix ALL
vertices of the genuine completed type-(2) augmentation.
This includes C=∅ and degenerate generator values. -/
theorem rankTwoOffComponentCompletedStage_proper_C_identity_word_fixes
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
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
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
  classical
  by_cases hdis : Disjoint C B
  · exact K.rankTwoOffComponentCompletedStage_disjoint_C_identity_word_fixes
      hcard hgen hret B hBP z hOff C hCP hdis w hw hval v
  · have hmeet : ∃ i : ι, i ∈ C ∧ i ∈ B := by
      by_contra hnone
      apply hdis
      apply Finset.disjoint_left.mpr
      intro i hiC hiB
      exact hnone ⟨i, hiC, hiB⟩
    obtain ⟨i, hiC, hiB⟩ := hmeet
    have hCB : C = B :=
      proper_alphabets_shared_letter_eq_rank_two
        A C B hcard.le
        ((mem_allProperCosetFamily A C).mp hCP)
        ((mem_allProperCosetFamily A B).mp hBP)
        i hiC hiB
    subst C
    exact K.rankTwoOffComponentCompletedStage_identity_B_word_fixes
      hcard hgen hret B hBP z hOff w hw hval v

/-- The preceding global fixed-point theorem is equivalent
to the genuine type-(2) stage's TRANSITION-GROUP word value
being 1, for every selected proper C⊂A. -/
theorem rankTwoOffComponentCompletedStage_proper_C_wordValue_eq_one
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
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (w : LabelWord ι)
    (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (K.rankTwoOffComponentCompletedStage
      hcard hgen hret B hBP z hOff).wordValue w = 1 := by
  apply ((K.rankTwoOffComponentCompletedStage
    hcard hgen hret B hBP z hOff).wordValue_eq_one_iff_all_vertices_fixed w).mpr
  intro v
  exact K.rankTwoOffComponentCompletedStage_proper_C_identity_word_fixes
    hcard hgen hret B hBP z hOff C hCP w hw hval v

end CayleySubgraphSpec
end ABO
end PSTSEPPA
