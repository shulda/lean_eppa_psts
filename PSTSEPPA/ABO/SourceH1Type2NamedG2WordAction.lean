import PSTSEPPA.ABO.SourceH1Type2ActualG2WordAction
import PSTSEPPA.ABO.RootedSourceCompletedAugmentationApiAgreement

/-!
# Concrete finite G₂ action on the NAMED original SourceH₁ type-(2) stage

The certified G₂ word congruence currently applies to the genuine
source rank-two root-TRANSLATED type-(2) completed action.
The independently checked API agreement proves that this stage
and the NAMED original source action are heterogeneously equal,
because the true attached B-coset anchor equals root*localValue(z).

This module transports the signed-word congruence to the named
original source complete action without globally retractable
ambient H₁ and without collapsing distinct tagged quotient points.

The literal printed paper T(Y₁) type-(2) application still needs
the indexed source normalization bridge and the paper/source
completed-stage signed graph equivalence.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The genuine NAMED original SourceH₁ completed type-(2)
B-augmentation obeys equality of all signed word actions
whenever the two words have equal values in the actual
finite input-derived group G₂. All old/fresh vertex tags,
inverse letters and legally inserted fixed loops are preserved. -/
theorem sourceG2OriginalH1Type2Named_wordValue_congr
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst)
    (k :
      ((sourceCoverIndexSkeleton src dst j).restrictAlphabet
        j.2.1.1).rootedLocalOffCosetAugmentationIndex
        j.2.1.1 j.2.1.2
        (sourceH1_twoRetractable src dst)
        (sourceCoverIndexRoot src dst j)
        (allProperCosetFamily j.2.1.1))
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ y,
      (((sourceCoverIndexSkeleton src dst j).restrictAlphabet
        j.2.1.1).rootedSourceOffCosetCompletedStage
        j.2.1.1 j.2.1.2 (sourceH1_twoRetractable src dst)
        (sourceCoverIndexRoot src dst j) k.1.1 k.1.2 k.2.1
        ((((sourceCoverIndexSkeleton src dst j).restrictAlphabet
          j.2.1.1).rootedLocalMultiCosetOffCoset_iff
          j.2.1.1 j.2.1.2 (sourceH1_twoRetractable src dst)
          (sourceCoverIndexRoot src dst j)
          (allProperCosetFamily j.2.1.1)
          k.1.1 k.1.2 k.2.1).mp k.2.2)).followWord y p =
      (((sourceCoverIndexSkeleton src dst j).restrictAlphabet
        j.2.1.1).rootedSourceOffCosetCompletedStage
        j.2.1.1 j.2.1.2 (sourceH1_twoRetractable src dst)
        (sourceCoverIndexRoot src dst j) k.1.1 k.1.2 k.2.1
        ((((sourceCoverIndexSkeleton src dst j).restrictAlphabet
          j.2.1.1).rootedLocalMultiCosetOffCoset_iff
          j.2.1.1 j.2.1.2 (sourceH1_twoRetractable src dst)
          (sourceCoverIndexRoot src dst j)
          (allProperCosetFamily j.2.1.1)
          k.1.1 k.1.2 k.2.1).mp k.2.2)).followWord y q := by
  let A := j.2.1.1
  let hcard := j.2.1.2
  let K := (sourceCoverIndexSkeleton src dst j).restrictAlphabet A
  let hret := sourceH1_twoRetractable src dst
  let root := sourceCoverIndexRoot src dst j
  let hOff := (K.rootedLocalMultiCosetOffCoset_iff
    A hcard hret root (allProperCosetFamily A)
    k.1.1 k.1.2 k.2.1).mp k.2.2
  have htranslated :
      ∀ y,
        (K.rootedTranslatedSourceOffCosetCompletedStage
          A hcard hret root k.1.1 k.1.2 k.2.1 hOff).followWord y p =
        (K.rootedTranslatedSourceOffCosetCompletedStage
          A hcard hret root k.1.1 k.1.2 k.2.1 hOff).followWord y q :=
    sourceG2OriginalH1Type2Translated_wordValue_congr
      src dst j k p q hpq
  have heq :
      HEq (K.rootedSourceOffCosetCompletedStage
        A hcard hret root k.1.1 k.1.2 k.2.1 hOff)
        (K.rootedTranslatedSourceOffCosetCompletedStage
          A hcard hret root k.1.1 k.1.2 k.2.1 hOff) :=
    K.rootedSourceOffCosetCompletedStage_heq_translated
      A hcard hret root k.1.1 k.1.2 k.2.1 hOff
  cases heq
  exact htranslated

end ABO
end PSTSEPPA
