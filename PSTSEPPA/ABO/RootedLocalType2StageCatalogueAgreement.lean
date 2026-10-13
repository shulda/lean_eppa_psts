import PSTSEPPA.ABO.RootedOriginalSourceCompletedAugmentationTransport
import PSTSEPPA.ABO.RootedSourceType2CatalogueIndex
import PSTSEPPA.ABO.RankTwoType2IndexedFamily

/-!
# Exact local type-(2) completed stage agreement with the REAL G₂ catalogue

The source type-(2) index correspondence is not yet sufficient to
show that the actual action of the completed original H₁ source
augmentation appears in the finite all-local G₂ catalogue.

This file closes the remaining LOCAL stage-API step: at the exact
(B,z) rank-two augmentation index (including empty B and degeneracies),
the independent local rooted construction used in source-normalization
is DEFINITIONALLY the genuine `rankTwoType2SingletonStage` in the
actual finite three-family G₂ catalogue. The OLD proper-coset
vertex quotient, added full-B coset, legal loop completion and
signed action tokens are the SAME model.

The original-source action is separately signed-isomorphic to this
local one (the predecessor's theorem); combining the two produces
the final source-to-finite-G₂ fibrewise action bridge. No global
retractability is imposed on the original ambient Γ.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The ACTUAL type-(2) action at a rooted local catalogue index
is identical to the independently constructed local source
augmentation stage. Neither edge tokens nor vertex tags are
quotiented by their ambient group coordinate. -/
theorem rootedLocalType2CompletedStage_eq_catalogue
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (j : K.rootedLocalOffCosetAugmentationIndex
      A hcard hret root (allProperCosetFamily A)) :
    K.rootedLocalOffCosetCompletedStage
      A hcard hret root j.1.1 j.1.2 j.2.1
      ((K.rootedLocalMultiCosetOffCoset_iff A hcard hret root
        (allProperCosetFamily A) j.1.1 j.1.2 j.2.1).mp j.2.2) =
      (K.intrinsicComponentLocalSlice A root).rankTwoType2SingletonStage
        hcard
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le)
        j := by
  rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
