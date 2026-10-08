import PSTSEPPA.ABO.ComponentSubgraphIndices
import PSTSEPPA.ABO.MultiCosetOverlap

/-!
# Naturality of coset attachments for intrinsic component subgraphs

Let L be a literal B-component of K, and let C⊆D⊆B.
The component-index and attached-coset injections from L into K
commute with alphabet enlargement C→D.

Consequently a literal shared (C∩D)-coset support witness in L
maps to an actual shared support witness in K. This is the
compatibility needed to define the canonical map from local
multi-alphabet coset extension CE(G,L;P) into CE(G,K;P).

Unlike an argument based only on ambient group coordinates, this
preserves the full intrinsic component tags of the gluing relation.
Equal, nested and empty alphabet parameters are permitted.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The inclusion of intrinsic lower component indices commutes
with enlargement C→D inside the chosen B-component. -/
theorem componentSubgraphIndexMap_natural
    (B C D : Finset ι)
    (hCD : C ⊆ D) (hDB : D ⊆ B)
    (root : K.Vertex)
    (c : (K.subalphabetComponentSubgraph B root).ComponentIndex C) :
    K.componentSubgraphIndexMap B D hDB root
        ((K.subalphabetComponentSubgraph B root).componentIndexMap C D hCD c) =
      K.componentIndexMap C D hCD
        (K.componentSubgraphIndexMap B C (hCD.trans hDB) root c) := by
  induction c using Quotient.inductionOn with
  | h x =>
      rfl

/-- Component-tagged attached coset maps likewise commute with
alphabet enlargement, without global ambient-map injectivity. -/
theorem componentSubgraphAttachedMap_natural
    (B C D : Finset ι)
    (hCD : C ⊆ D) (hDB : D ⊆ B)
    (root : K.Vertex)
    (p : (K.subalphabetComponentSubgraph B root).AttachedCosetVertex C) :
    K.componentSubgraphAttachedMap B D hDB root
        ((K.subalphabetComponentSubgraph B root).attachedSubalphabetMap C D hCD p) =
      K.attachedSubalphabetMap C D hCD
        (K.componentSubgraphAttachedMap B C (hCD.trans hDB) root p) := by
  apply K.attachedValue_injective_of_same_index D
  · exact K.componentSubgraphIndexMap_natural B C D hCD hDB root p.1
  · rfl

/-- A literal common intersection-support witness in a local
B-component also witnesses the corresponding gluing in K. -/
theorem componentSubgraphShareIntersectionSupport_map
    (B C D : Finset ι)
    (hCB : C ⊆ B) (hDB : D ⊆ B)
    (root : K.Vertex)
    (p : (K.subalphabetComponentSubgraph B root).AttachedCosetVertex C)
    (q : (K.subalphabetComponentSubgraph B root).AttachedCosetVertex D)
    (hshare :
      (K.subalphabetComponentSubgraph B root).ShareIntersectionSupport
        C D p q) :
    K.ShareIntersectionSupport C D
      (K.componentSubgraphAttachedMap B C hCB root p)
      (K.componentSubgraphAttachedMap B D hDB root q) := by
  let L := K.subalphabetComponentSubgraph B root
  obtain ⟨r, hrp, hrq⟩ := hshare
  have hIB : C ∩ D ⊆ B := Finset.inter_subset_left.trans hCB
  refine ⟨K.componentSubgraphAttachedMap B (C ∩ D) hIB root r,
    ?_, ?_⟩
  · calc
      K.attachedSubalphabetMap (C ∩ D) C
          Finset.inter_subset_left
          (K.componentSubgraphAttachedMap B (C ∩ D) hIB root r) =
        K.componentSubgraphAttachedMap B C hCB root
          (L.attachedSubalphabetMap (C ∩ D) C
            Finset.inter_subset_left r) :=
        (K.componentSubgraphAttachedMap_natural
          B (C ∩ D) C Finset.inter_subset_left hCB root r).symm
      _ = K.componentSubgraphAttachedMap B C hCB root p :=
        congrArg (K.componentSubgraphAttachedMap B C hCB root) hrp
  · calc
      K.attachedSubalphabetMap (C ∩ D) D
          Finset.inter_subset_right
          (K.componentSubgraphAttachedMap B (C ∩ D) hIB root r) =
        K.componentSubgraphAttachedMap B D hDB root
          (L.attachedSubalphabetMap (C ∩ D) D
            Finset.inter_subset_right r) :=
        (K.componentSubgraphAttachedMap_natural
          B (C ∩ D) D Finset.inter_subset_right hDB root r).symm
      _ = K.componentSubgraphAttachedMap B D hDB root q :=
        congrArg (K.componentSubgraphAttachedMap B D hDB root) hrq

end CayleySubgraphSpec
end ABO
end PSTSEPPA
