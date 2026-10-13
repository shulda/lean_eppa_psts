import PSTSEPPA.ABO.RootedOriginalSourceCompletedAugmentationTransport
import PSTSEPPA.ABO.RootedSourceOffCosetAugmentedStage
import PSTSEPPA.ABO.RootedSourceMultiCosetAmbientValue

/-!
# The named original-source type-(2) action agrees with root-translated normalization

The true original H₁ B-augmented completed stage is constructed from
a selected old component-tagged multi-coset quotient vertex z,
attaching a full B-coset based at its ACTUAL ambient group value
`rootedAmbientMultiCosetValue(z)`, and adding only legally missing loops.

The source/local completed-action isomorphism is stated for a
ROOT-TRANSLATED augmented stage whose coset basepoint is
`root.value * localMultiCosetAmbientValue(z)`. These two ambient
basepoints are PROVABLY EQUAL by the certified source-glued
quotient value naturality theorem (#394). That equality does
NOT imply any identification of old tagged quotient vertices:
it only identifies the new attached full-coset anchor.

Because the vertex type of an isolated-coset augmentation depends
on its basepoint, the most honest model-agreement statement is
heterogeneous equality of the two *actual completed actions*.
This file checks that the two independently defined objects
have literally the same signed transitions after rewriting their
rooted-coset basepoint equality, rather than postulating an
arbitrary (and potentially incorrect) coordinate bijection.

It is the needed API gate before applying the certified
source/local complete-augmentation isomorphism directly to
the named corrected Definition-5.3 source object.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The named complete original source augmentation and the
root-translated complete source action used in the normalized
geometric isomorphism are LITERALLY the same signed structure
after identification of their true attached B-coset basepoints.

The `HEq` (instead of homogeneous equality) is intentional:
both original construction APIs have a vertex type depending
on their written ambient coset anchor. No equality of two
distinct original component tags is used. -/
theorem rootedSourceOffCosetCompletedStage_heq_translated
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z) :
    HEq
      (K.rootedSourceOffCosetCompletedStage
        A hcard hret root B hBP z hOffSource)
      (K.rootedTranslatedSourceOffCosetCompletedStage
        A hcard hret root B hBP z hOffSource) := by
  have hval := K.rootedAmbientMultiCosetValue_natural
    A hcard hret root (allProperCosetFamily A) z
  unfold rootedSourceOffCosetCompletedStage
    rootedTranslatedSourceOffCosetCompletedStage
  rw [hval]

end CayleySubgraphSpec
end ABO
end PSTSEPPA
