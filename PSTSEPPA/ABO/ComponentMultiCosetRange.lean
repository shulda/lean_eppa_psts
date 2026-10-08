import PSTSEPPA.ABO.ComponentMultiCosetVertexMap
import PSTSEPPA.ABO.ComponentParentIndexControl
import PSTSEPPA.ABO.ComponentAttachmentRange
import PSTSEPPA.ABO.MultiCosetParentFold

/-!
# Exact image of a local multi-coset quotient in a global family

The natural map from the multi-coset vertex quotient of the literal
B-component of K to the global quotient is not generally surjective.
Its image is characterized intrinsically: an attached global quotient
point belongs to the image iff its canonical enlargement to a B-coset
is tagged by the selected intrinsic B-component.

This retains real component tags; ambient group-coordinate equality
would give a false characterization. The result holds for every proper
lower alphabet family, including the empty family.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every alphabet of a local proper family is contained in its
selected parent B, also when viewed as an A-family. -/
theorem componentFamily_subset_parent
    (B : Finset ι) (hBA : B ⊂ A) (P : CosetFamilySpec B) :
    ∀ C ∈ (P.intoLarger hBA).alphabets, C ⊆ B := by
  intro C hCP
  exact (P.proper C hCP).subset

/-- All vertices arising from the local B-component have the
selected parent-component tag after folding to B-attached cosets. -/
theorem componentMultiCosetVertexMap_parent_index
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (x : (K.subalphabetComponentSubgraph B root).MultiCosetVertex
      P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
      hgen hret) :
    K.attachedIndex B
      (K.multiCosetVertexToParent (P.intoLarger hBA) hadm hgen hret B
        (componentFamily_subset_parent B hBA P)
        (K.componentMultiCosetVertexMap B hBA root P hadm hgen hret x)) =
      K.componentClass B root := by
  induction x using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨C, p⟩
      exact K.componentSubgraphAttachedMap_parent B C.1
        (P.proper C.1 C.2).subset root p

/-- A globally attached quotient vertex whose parent B-coset has
the chosen intrinsic B-component tag has a local multi-CE preimage. -/
theorem componentMultiCosetVertexMap_surj_of_parent
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (P.intoLarger hBA) hadm hgen hret)
    (hparent : K.attachedIndex B
      (K.multiCosetVertexToParent (P.intoLarger hBA) hadm hgen hret B
        (componentFamily_subset_parent B hBA P) z) =
        K.componentClass B root) :
    ∃ x : (K.subalphabetComponentSubgraph B root).MultiCosetVertex
      P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
      hgen hret,
      K.componentMultiCosetVertexMap B hBA root P hadm hgen hret x = z := by
  induction z using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨C, p⟩
      change K.componentIndexMap C.1 B
        (P.proper C.1 C.2).subset p.1 =
        K.componentClass B root at hparent
      obtain ⟨q, hq⟩ :=
        K.componentSubgraphAttachedMap_surj_of_parent
          B C.1 (P.proper C.1 C.2).subset root p hparent
      refine ⟨
        (K.subalphabetComponentSubgraph B root).multiCosetInclude
          P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
          hgen hret C.1 C.2 q, ?_⟩
      change
        K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret C.1 C.2
          (K.componentSubgraphAttachedMap B C.1
            (P.proper C.1 C.2).subset root q) =
        K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret C.1 C.2 p
      exact congrArg
        (K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret C.1 C.2)
        hq

/-- Exact range description. In conjunction with local vertex
injectivity this identifies the component multi-CE with a literal
subset of the global multi-CE, indexed by the parent component. -/
theorem componentMultiCosetVertexMap_range_iff
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (P.intoLarger hBA) hadm hgen hret) :
    (∃ x : (K.subalphabetComponentSubgraph B root).MultiCosetVertex
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret,
        K.componentMultiCosetVertexMap B hBA root P hadm hgen hret x = z) ↔
      K.attachedIndex B
        (K.multiCosetVertexToParent (P.intoLarger hBA) hadm hgen hret B
          (componentFamily_subset_parent B hBA P) z) =
        K.componentClass B root := by
  constructor
  · rintro ⟨x, rfl⟩
    exact K.componentMultiCosetVertexMap_parent_index
      B hBA root P hadm hgen hret x
  · exact K.componentMultiCosetVertexMap_surj_of_parent
      B hBA root P hadm hgen hret z

end CayleySubgraphSpec
end ABO
end PSTSEPPA
