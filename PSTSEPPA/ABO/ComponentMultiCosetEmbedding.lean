import PSTSEPPA.ABO.ComponentMultiCosetVertexMap
import PSTSEPPA.ABO.ComponentParentIndexControl
import PSTSEPPA.ABO.ComponentAttachmentRange

/-!
# Reflection of coset gluing inside an intrinsic B-component

The inclusion of the actual B-component L of K preserves intersection
support of its tagged lower coset attachments. We prove the converse:
a global (C ∩ D)-support of two attachments from L must itself lie
over the selected B-component and hence lift to a local attached coset.

This is stronger than equality of ambient group coordinates. In
particular it proves the local multi-alphabet quotient vertex map
injective, even when distinct intrinsic components share an ambient
coset, with equal/nested/empty lower alphabets and trivial generators.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Global intersection support of two points from the literal B-component
reflects to a true common (C ∩ D)-support in that component. No claim
of global injectivity of the ambient Cayley projection is used. -/
theorem componentSubgraphShareIntersectionSupport_reflect
    (B C D : Finset ι)
    (hCB : C ⊆ B) (hDB : D ⊆ B)
    (root : K.Vertex)
    (p : (K.subalphabetComponentSubgraph B root).AttachedCosetVertex C)
    (q : (K.subalphabetComponentSubgraph B root).AttachedCosetVertex D)
    (hshare : K.ShareIntersectionSupport C D
      (K.componentSubgraphAttachedMap B C hCB root p)
      (K.componentSubgraphAttachedMap B D hDB root q)) :
    (K.subalphabetComponentSubgraph B root).ShareIntersectionSupport
      C D p q := by
  let L := K.subalphabetComponentSubgraph B root
  obtain ⟨r, hrp, hrq⟩ := hshare
  have hIB : C ∩ D ⊆ B := Finset.inter_subset_left.trans hCB
  have hparent :
      K.componentIndexMap (C ∩ D) B hIB r.1 =
        K.componentClass B root := by
    calc
      K.componentIndexMap (C ∩ D) B hIB r.1 =
          K.componentIndexMap C B hCB
            (K.componentIndexMap (C ∩ D) C
              Finset.inter_subset_left r.1) :=
        (K.componentIndexMap_comp (C ∩ D) C B
          Finset.inter_subset_left hCB r.1).symm
      _ = K.componentIndexMap C B hCB
            (K.attachedIndex C
              (K.componentSubgraphAttachedMap B C hCB root p)) :=
        congrArg (K.componentIndexMap C B hCB)
          (congrArg (K.attachedIndex C) hrp)
      _ = K.componentClass B root :=
        K.componentSubgraphAttachedMap_parent B C hCB root p
  obtain ⟨s, hs⟩ :=
    K.componentSubgraphAttachedMap_surj_of_parent
      B (C ∩ D) hIB root r hparent
  refine ⟨s, ?_, ?_⟩
  · apply K.componentSubgraphAttachedMap_injective B C hCB root
    calc
      K.componentSubgraphAttachedMap B C hCB root
          (L.attachedSubalphabetMap (C ∩ D) C
            Finset.inter_subset_left s) =
        K.attachedSubalphabetMap (C ∩ D) C Finset.inter_subset_left
          (K.componentSubgraphAttachedMap B (C ∩ D) hIB root s) :=
        K.componentSubgraphAttachedMap_natural
          B (C ∩ D) C Finset.inter_subset_left hCB root s
      _ = K.attachedSubalphabetMap (C ∩ D) C
            Finset.inter_subset_left r :=
        congrArg
          (K.attachedSubalphabetMap (C ∩ D) C
            Finset.inter_subset_left) hs
      _ = K.componentSubgraphAttachedMap B C hCB root p := hrp
  · apply K.componentSubgraphAttachedMap_injective B D hDB root
    calc
      K.componentSubgraphAttachedMap B D hDB root
          (L.attachedSubalphabetMap (C ∩ D) D
            Finset.inter_subset_right s) =
        K.attachedSubalphabetMap (C ∩ D) D Finset.inter_subset_right
          (K.componentSubgraphAttachedMap B (C ∩ D) hIB root s) :=
        K.componentSubgraphAttachedMap_natural
          B (C ∩ D) D Finset.inter_subset_right hDB root s
      _ = K.attachedSubalphabetMap (C ∩ D) D
            Finset.inter_subset_right r :=
        congrArg
          (K.attachedSubalphabetMap (C ∩ D) D
            Finset.inter_subset_right) hs
      _ = K.componentSubgraphAttachedMap B D hDB root q := hrq

/-- The actual local multi-coset quotient maps injectively into the
global multi-coset quotient over the same family of alphabets. This
proves the vertex-embedding clause needed for ABO Lemma 3.20. -/
theorem componentMultiCosetVertexMap_injective
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Function.Injective
      (K.componentMultiCosetVertexMap B hBA root P hadm hgen hret) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h p =>
      induction y using Quotient.inductionOn with
      | h q =>
          apply Quotient.sound
          change (K.subalphabetComponentSubgraph B root).ShareIntersectionSupport
            p.1.1 q.1.1 p.2 q.2
          have hglobal :
              K.ShareIntersectionSupport p.1.1 q.1.1
                (K.componentSubgraphAttachedMap B p.1.1
                  (P.proper p.1.1 p.1.2).subset root p.2)
                (K.componentSubgraphAttachedMap B q.1.1
                  (P.proper q.1.1 q.1.2).subset root q.2) := by
            have h := Quotient.exact hxy
            change K.ShareIntersectionSupport p.1.1 q.1.1
              (K.componentSubgraphAttachedMap B p.1.1
                (P.proper p.1.1 p.1.2).subset root p.2)
              (K.componentSubgraphAttachedMap B q.1.1
                (P.proper q.1.1 q.1.2).subset root q.2) at h
            exact h
          exact K.componentSubgraphShareIntersectionSupport_reflect
            B p.1.1 q.1.1
            (P.proper p.1.1 p.1.2).subset
            (P.proper q.1.1 q.1.2).subset
            root p.2 q.2 hglobal

end CayleySubgraphSpec
end ABO
end PSTSEPPA
