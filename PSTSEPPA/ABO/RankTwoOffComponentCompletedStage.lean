import PSTSEPPA.ABO.RankTwoOffComponentAugmentation
import PSTSEPPA.ABO.IsolatedCosetCompletion
import PSTSEPPA.ABO.CompletedFullCosetStage

/-!
# The actual COMPLETED rank-two type-(2) full coset augmentation

The source-corrected ABO Proposition 5.4 at k=1 requires literal
complete E-graph stages for Definition 5.3's type-(2) objects.
We already have the actual rank-two full multi-coset EGraph and
the genuine singleton augmentation with no old signed B-edge at
the attaching root. The weak-completeness theorem for all proper
alphabets at |A|=2 proves LOCAL PAIRED signs for the old graph.
Combined with the certified isolated-coset gluing pairing theorem,
this gives a legal completion by adding only missing loops.

We construct that actual completed action on the true quotient
vertices PLUS the fresh tagged full B-coset points. The completion
adds no new vertices or nontrivial connecting edges.

Every B-supported signed word of ambient Γ-value 1 fixes each
vertex of the newly attached B-coset, including its identified
old root, using the genuine lifted B-word path.

The remaining old off-root vertices, and therefore the full
G2→H1 singleton-kernel / R2 stability argument, are separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The genuine rank-two full proper-coset extension is locally
paired in its unsigned ±i availability. This is not automatic for
an arbitrary incomplete E-graph; it follows from actual weak
completeness of selected full coset constituents. -/
theorem rankTwo_fullProperCE_locallyPaired
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    (K.multiCosetEGraph (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le)
      hgen hret).LocallyPairedLabels :=
  K.multiCoset_locallyPairedLabels_of_weakComplete
    (allProperCosetFamily A)
    (K.admissible_of_card_le_two hcard.le)
    hgen hret
    (allProperCosetFamily_weaklyComplete K
      (K.admissible_of_card_le_two hcard.le)
      hgen hret hcard.ge)

/-- A true complete EGraph for the actual rank-two off-component
full coset augmentation. There is no postulated completion:
each missing unsigned generator is inserted as a fixed-point
permutation, justified by paired old/new signed availability. -/
noncomputable def rankTwoOffComponentCompletedStage
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret)
    (hOff : ¬ ∃ q : K.AttachedCosetVertex B,
        K.multiCosetInclude (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard.le)
          hgen hret B hBP q = z) :=
  IsolatedCosetGluing.completedStage
    (K.multiCosetEGraph (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret)
    gen B
    (K.multiCosetAmbientValue (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret z)
    z
    (by
      intro e he
      exact K.rank_two_off_selected_B_no_outgoing_edges
        hcard.le hgen hret B hBP z hOff e he)
    (K.rankTwo_fullProperCE_locallyPaired hcard hgen hret)

/-- The genuine rank-two completed augmentation acts trivially
on every vertex in the attached full B-coset whenever the signed
B-word represents the ambient group identity. Both signed
directions and the attached old root are covered. -/
theorem rankTwoOffComponentCompletedStage_attached_identity_word_fixes
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
    (p : IsolatedCosetGluing.CosetPoint gen B
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le)
        hgen hret z))
    (w : LabelWord ι)
    (hw : LabelWord.Uses B w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (K.rankTwoOffComponentCompletedStage
      hcard hgen hret B hBP z hOff).followWord
      (IsolatedCosetGluing.gluePoint gen B
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard.le)
          hgen hret z) z p) w =
      IsolatedCosetGluing.gluePoint gen B
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard.le)
          hgen hret z) z p := by
  exact IsolatedCosetGluing.completedStage_attached_B_identity_word_fixes
    (K.multiCosetEGraph (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le)
      hgen hret)
    gen B
    (K.multiCosetAmbientValue (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le)
      hgen hret z)
    z
    (by
      intro e he
      exact K.rank_two_off_selected_B_no_outgoing_edges
        hcard.le hgen hret B hBP z hOff e he)
    (K.rankTwo_fullProperCE_locallyPaired hcard hgen hret)
    p w hw hval

end CayleySubgraphSpec
end ABO
end PSTSEPPA
