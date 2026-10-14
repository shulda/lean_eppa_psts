import PSTSEPPA.ABO.SourceH1Type2ActualG2WordAction
import PSTSEPPA.ABO.RootedSourceCompletedAugmentationApiAgreement

/-!
# The actual NAMED original source H₁ type-(2) augmented completion inherits G₂ word actions

The original corrected Definition-5.3 source stage attaches a
full B-coset at the genuinely component-tagged quotient point
using `rootedAmbientMultiCosetValue`. Its independently normalized
source/local signed action isomorphism uses the *root-translated*
ambient anchor. These two complete action structures are
heterogeneously equal by proved original quotient-value naturality.

This lifts the independently checked actual finite input-dependent
G₂ signed-word congruence from the root-translated model to the
NAMED, original-source completed action, including vertex-type
dependence on the attached B-coset anchor.

No arbitrary ambient-coordinate quotient or hidden choice of
coset representatives is introduced.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Two chronological signed words representing the same element
in the actual finite G₂ have IDENTICAL endpoints at every point
of every NAMED original H₁ type-(2) source B-augmentation,
including all old component-tagged and fresh B-coset vertices,
negative letters and legal stationary loops. -/
set_option maxHeartbeats 2000000 in
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
  have hval := K.rootedAmbientMultiCosetValue_natural
    A hcard hret root (allProperCosetFamily A) k.2.1
  have hTranslated :
      ∀ y,
        (K.rootedTranslatedSourceOffCosetCompletedStage A hcard hret root
          k.1.1 k.1.2 k.2.1 hOff).followWord y p =
        (K.rootedTranslatedSourceOffCosetCompletedStage A hcard hret root
          k.1.1 k.1.2 k.2.1 hOff).followWord y q :=
    sourceG2OriginalH1Type2Translated_wordValue_congr src dst j k p q hpq
  unfold CayleySubgraphSpec.rootedTranslatedSourceOffCosetCompletedStage
    at hTranslated
  unfold CayleySubgraphSpec.rootedSourceOffCosetCompletedStage
  rw [hval]
  exact hTranslated

end ABO
end PSTSEPPA
