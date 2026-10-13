import PSTSEPPA.ABO.RootedOriginalSourceCompletedAugmentationTransport
import PSTSEPPA.ABO.CompleteStageWordKernelTransport

/-!
# Whole signed-word action congruence of true rooted type-(2) source augmentations

The corrected Section-5 source uses genuine H₁-cover A-components
with A.card = 2, their full proper-coset extensions and a true B-coset
augmentation at an off-B old component-tagged vertex.

The checked source/local geometric transport is bijective on
vertices and both signed action-edge tokens after legal loop
completion. The general complete-stage word-kernel interface now
identifies the ENTIRE signed-word congruence (two words agree at
every vertex) between the true local stage and the root-translated
original-source complete augmentation.

All signs, loops, old/fresh tags and actual signed paths are
preserved. This does not make any assertion about stages of rank
higher than two, and does not replace the separate exact named
source API identification or the original Z₁ family census.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- True source/local signed completed type-(2) augmentation
isomorphism preserves and reflects equality of two signed word
actions AT EVERY VERTEX (not merely equality of ambient Γ values). -/
theorem rootedSourceOffCoset_wordActionCongr_iff
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z)
    (w₁ w₂ : LabelWord ι) :
    (∀ x,
      (K.rootedLocalOffCosetCompletedStage
        A hcard hret root B hBP z hOffSource).followWord x w₁ =
      (K.rootedLocalOffCosetCompletedStage
        A hcard hret root B hBP z hOffSource).followWord x w₂) ↔
    (∀ y,
      (K.rootedTranslatedSourceOffCosetCompletedStage
        A hcard hret root B hBP z hOffSource).followWord y w₁ =
      (K.rootedTranslatedSourceOffCosetCompletedStage
        A hcard hret root B hBP z hOffSource).followWord y w₂) := by
  exact
    (K.rootedLocalOffCosetCompletedStage
      A hcard hret root B hBP z hOffSource).wordActionCongr_iff_of_bijectiveHom
      (K.rootedTranslatedSourceOffCosetCompletedStage
        A hcard hret root B hBP z hOffSource)
      (K.rootedSourceOffCosetCompletedStageHom
        A hcard hret root B hBP z hOffSource)
      (K.rootedSourceOffCosetCompletedStageHom_bijective
        A hcard hret root B hBP z hOffSource).1 w₁ w₂

end CayleySubgraphSpec
end ABO
end PSTSEPPA
