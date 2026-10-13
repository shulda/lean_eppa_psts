import PSTSEPPA.ABO.SourceG2Type2ExactFibreWordAction
import PSTSEPPA.ABO.RootedSourceType2WordActionCongruence
import PSTSEPPA.ABO.SourceH1Type2StageCatalogueIndex
import PSTSEPPA.ABO.RootedLocalType2StageCatalogueAgreement

/-!
# Genuine original H₁ source type-(2) complete augmentation inherits source G₂ word actions

For an ORIGINAL oriented edge-labelled input, take ANY genuine
two-letter connected component of its actual H₁ preimage
skeleton. The exact local subgroup Γ[A] normalization yields
a concrete (A,K) skeleton tag in the input-dependent finite G₂.

For EVERY literal proper B and truly off-B component-tagged old
coset-extension vertex z, the real local completed B-augmentation
is definitionally the exact local G₂ type-(2) catalogue stage.
Equality of group values of two chronological signed words in
the ACTUAL finite source G₂ therefore implies equality at every
local stage vertex. The certified full original H₁ completed
action graph isomorphism transports this equality to every
ROOT-TRANSLATED ORIGINAL source augmented-stage vertex.

This does not identify old tagged vertices sharing ambient
group values. Literal named vs root-translated source stage
equality is certified separately in main; the present goal
concerns the translated model with an exact signed graph
isomorphism, not a choice of coset representatives.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Equality of values of arbitrary signed words in the
ACTUAL finite source G₂ descends to every point of every
true original H₁ rooted type-(2) B-augmented COMPLETED action,
represented in its honest root-translated ambient coordinates.
All genuine B=∅ cases, old/fresh tags, inverse edges and fixed
loops are retained. -/
theorem sourceG2OriginalH1Type2Translated_wordValue_congr
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
        j.2.1.1).rootedTranslatedSourceOffCosetCompletedStage
        j.2.1.1 j.2.1.2 (sourceH1_twoRetractable src dst)
        (sourceCoverIndexRoot src dst j) k.1.1 k.1.2 k.2.1
        ((((sourceCoverIndexSkeleton src dst j).restrictAlphabet
          j.2.1.1).rootedLocalMultiCosetOffCoset_iff
          j.2.1.1 j.2.1.2 (sourceH1_twoRetractable src dst)
          (sourceCoverIndexRoot src dst j)
          (allProperCosetFamily j.2.1.1)
          k.1.1 k.1.2 k.2.1).mp k.2.2)).followWord y p =
      (((sourceCoverIndexSkeleton src dst j).restrictAlphabet
        j.2.1.1).rootedTranslatedSourceOffCosetCompletedStage
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
  have hLocal :
      ∀ x, (K.rootedLocalOffCosetCompletedStage A hcard hret root
        k.1.1 k.1.2 k.2.1 hOff).followWord x p =
        (K.rootedLocalOffCosetCompletedStage A hcard hret root
          k.1.1 k.1.2 k.2.1 hOff).followWord x q := by
    intro x
    change
      ((allLocalRankTwoSkeleton
        (sourceCoverIntoAllLocalIndex src dst j)).rankTwoType2SingletonStage
        (allLocalRankTwoAlphabet_card (sourceCoverIntoAllLocalIndex src dst j))
        (isGenerated_trivialCompletionGenerator
          (sourceH1Generator src dst)
          (allLocalRankTwoAlphabet (sourceCoverIntoAllLocalIndex src dst j)))
        (retractable_trivialCompletionGenerator_of_kRetractable
          (sourceH1Generator src dst) 2
          (sourceH1_twoRetractable src dst)
          (allLocalRankTwoAlphabet (sourceCoverIntoAllLocalIndex src dst j))
          (allLocalRankTwoAlphabet_card
            (sourceCoverIntoAllLocalIndex src dst j)).le)
        k).followWord x p =
      ((allLocalRankTwoSkeleton
        (sourceCoverIntoAllLocalIndex src dst j)).rankTwoType2SingletonStage
        (allLocalRankTwoAlphabet_card (sourceCoverIntoAllLocalIndex src dst j))
        (isGenerated_trivialCompletionGenerator
          (sourceH1Generator src dst)
          (allLocalRankTwoAlphabet (sourceCoverIntoAllLocalIndex src dst j)))
        (retractable_trivialCompletionGenerator_of_kRetractable
          (sourceH1Generator src dst) 2
          (sourceH1_twoRetractable src dst)
          (allLocalRankTwoAlphabet (sourceCoverIntoAllLocalIndex src dst j))
          (allLocalRankTwoAlphabet_card
            (sourceCoverIntoAllLocalIndex src dst j)).le)
        k).followWord x q
    exact sourceG2Type2Singleton_wordValue_congr
      src dst (sourceCoverIntoAllLocalIndex src dst j) k x p q hpq
  exact (K.rootedSourceOffCoset_wordActionCongr_iff
    A hcard hret root k.1.1 k.1.2 k.2.1 hOff p q).mp hLocal

end ABO
end PSTSEPPA
