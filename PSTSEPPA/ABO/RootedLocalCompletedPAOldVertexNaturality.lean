import PSTSEPPA.ABO.RootedSourceAllProperCompletedStageIso
import PSTSEPPA.ABO.RootedTaggedAttachedCosetEquiv
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Original old vertices under exact rooted H[A] normalization

The previously certified signed local-to-ambient P_A stage
isomorphism must preserve the literal old-component tags,
not merely ambient group values. This theorem proves that
the diagram for embedding one true old local skeleton point
in an arbitrary selected proper B-constituent commutes
with the old inverse-root translation, the natural map of
tagged attached B-cosets, and the complete signed-stage
isomorphism. This includes B=empty and inverse-labelled
geometric old loops. It is the remaining original old-root
anchor check before instantiating corrected Theorem 4.7(ii).
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

/-- Genuine source-tagged old vertex is transported exactly from
the normalized generated subgroup to the original rooted component. -/
theorem rootedAllProperCompletedStageHom_oldVertex
    (K : CayleySubgraphSpec gen S)
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (x : (K.intrinsicComponentLocalSlice A root).Vertex) :
    (K.rootedAllProperCompletedStageHom A hcard hret root).onVertex
      (Quotient.mk
        ((K.intrinsicComponentLocalSlice A root).multiCosetSetoid
          (allProperCosetFamily A)
          ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
          (isGenerated_trivialCompletionGenerator gen A)
          (retractable_trivialCompletionGenerator_of_kRetractable
            gen 2 hret A hcard.le))
        (⟨⟨B, hBP⟩,
          (K.intrinsicComponentLocalSlice A root).attachedOfSkeletonVertex B x⟩ :
          (K.intrinsicComponentLocalSlice A root).MultiCosetRawVertex
            (allProperCosetFamily A))) =
      Quotient.mk
        (K.rootedAmbientMultiCosetSetoid A hcard hret root
          (allProperCosetFamily A))
        (⟨⟨B, hBP⟩,
          (K.subalphabetComponentSubgraph A root).attachedOfSkeletonVertex B
            ((K.intrinsicComponentLocalHom A root).onVertex x)⟩ :
          (K.subalphabetComponentSubgraph A root).MultiCosetRawVertex
            (allProperCosetFamily A)) := by
  have hBA : B ⊆ A :=
    ((allProperCosetFamily A).proper B hBP).subset
  change
    Quotient.mk
      (K.rootedAmbientMultiCosetSetoid A hcard hret root
        (allProperCosetFamily A))
      (⟨⟨B, hBP⟩,
        K.rootedLocalAttachedCosetMap A B hBA root
          ((K.intrinsicComponentLocalSlice A root).attachedOfSkeletonVertex B x)⟩ :
        (K.subalphabetComponentSubgraph A root).MultiCosetRawVertex
          (allProperCosetFamily A)) =
    Quotient.mk
      (K.rootedAmbientMultiCosetSetoid A hcard hret root
        (allProperCosetFamily A))
      (⟨⟨B, hBP⟩,
        (K.subalphabetComponentSubgraph A root).attachedOfSkeletonVertex B
          ((K.intrinsicComponentLocalHom A root).onVertex x)⟩ :
        (K.subalphabetComponentSubgraph A root).MultiCosetRawVertex
          (allProperCosetFamily A))
  exact congrArg
    (fun p : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B =>
      Quotient.mk
        (K.rootedAmbientMultiCosetSetoid A hcard hret root
          (allProperCosetFamily A))
        (⟨⟨B, hBP⟩, p⟩ :
          (K.subalphabetComponentSubgraph A root).MultiCosetRawVertex
            (allProperCosetFamily A)))
    (K.rootedLocalAttachedCosetMap_oldVertex A B hBA root x)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
