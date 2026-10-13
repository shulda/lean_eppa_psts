import PSTSEPPA.ABO.RootedOffCosetAugmentationIndexEquiv
import PSTSEPPA.ABO.RankTwoType2IndexedFamily

/-!
# Exact original-source type-(2) index into the REAL local G₂ catalogue

The certified finite rank-two three-family action is not indexed by
abstract group points or an arbitrary chosen representative. Its
TYPE-(2) summand has the LITERAL dependent index:
  rankTwoType2SingletonIndex hcard hgen hret
for a selected Γ[A] local Cayley skeleton.

An original H₁-connected A-component of an incomplete Cayley
source cover is canonically normalized into the exact local
Γ[A] skeleton under only `KRetractable gen 2`. Every original
B-augmentation choice consists of a proper-alphabet tag B⊂A
and one old component-tagged quotient vertex lying OUTSIDE
all full B-constituent images. The source/local full dependent
index equivalence was established in the predecessor module.

This file now identifies that normalized index with the ACTUAL
concrete type-(2) catalogue index used by the already
formalized rank-two three-family G₂ stage. There is no
intermediate arbitrary stage family, group-coordinate quotient,
choice of coset representatives or nonempty-fibre hypothesis.

This proves the exact SOURCE-INDEX matching, NOT yet that the
source and local completed augmented ACTION graphs of each
indexed fibre are isomorphic. That is a separate obligation
addressed by the generic augmentation transport branches.
Global Z₁ coverage also has type-(1) cluster and other cases.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- A genuine local normalized original-source proper-B stage index
is DEFINITIONALLY the index used by the existing actual G₂
rank-two type-(2) family, not merely equivalent after choosing
ambient Γ-coordinate representatives. -/
theorem rootedLocalOffCosetIndex_eq_localCatalogueIndex
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex) :
    K.rootedLocalOffCosetAugmentationIndex A hcard hret root
        (allProperCosetFamily A) =
      (K.intrinsicComponentLocalSlice A root).rankTwoType2SingletonIndex
        hcard
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le) :=
  rfl

/-- Canonical bijection of ALL genuine ORIGINAL source-rooted
off-B augmentation choices to the ACTUAL (B,z) stage-index
type of the local rank-two type-(2) G₂ catalogue.

The ambient Γ is only 2-retractable; root-component vertex tags
and the exact B-coset exclusion are preserved and reflected. -/
noncomputable def rootedSourceType2CatalogueIndexEquiv
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex) :
    K.rootedAmbientOffCosetAugmentationIndex
        A hcard hret root (allProperCosetFamily A) ≃
      (K.intrinsicComponentLocalSlice A root).rankTwoType2SingletonIndex
        hcard
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le) :=
  (K.rootedOffCosetAugmentationIndexEquiv
    A hcard hret root (allProperCosetFamily A)).symm

/-- The exact source-to-G₂ type-(2) catalogue equivalence
does not change the selected proper B-alphabet tag. -/
@[simp] theorem rootedSourceType2CatalogueIndexEquiv_alphabet
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (j : K.rootedAmbientOffCosetAugmentationIndex
      A hcard hret root (allProperCosetFamily A)) :
    (K.rootedSourceType2CatalogueIndexEquiv A hcard hret root j).1 = j.1 :=
  rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
