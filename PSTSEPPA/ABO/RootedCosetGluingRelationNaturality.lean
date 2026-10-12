import PSTSEPPA.ABO.RootedTaggedAttachedCosetEquiv
import PSTSEPPA.ABO.MultiCosetOverlap

/-!
# Rooted source/local coset-extension gluing relation is preserved and reflected

The vertex quotient in the ABO multi-coset extension identifies two
component-tagged attached coset points only if they have a COMMON
INTERSECTION SUPPORT in their (B intersect C)-coset copy. Equality
of their ambient group coordinates ALONE is not enough, because
distinct intrinsic component tags can lie above the same coset.

For the source-cover rooted translation into Γ[A], #367 constructs
true equivalences of the entire tagged attached B-coset types for
every B⊆A, preserving old skeleton copies and every alphabet
enlargement. Here we prove that these equivalences preserve AND
REFLECT the literal ShareIntersectionSupport relation for all
B,C⊆A, including empty and equal alphabets.

Thus the exact quotient GLUING RELATION on raw pairs of attached
coset pieces is invariant under the source/local translation.
This is the key well-definedness step for building the full
multi-coset glued vertex quotient isomorphism. Actual quotient
vertex and directed-edge maps, trivial completion and all
B-augmentations remain to be constructed; no source Condition
5.2 or unconditional PSTS EPPA is claimed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The TRUE intersection-of-components gluing support is
transported in BOTH directions by the source/local attached
coset equivalences. The proof uses a genuine tagged point r
in the (B ∩ C)-copy, not merely an equality in Γ. -/
theorem rootedLocal_shareIntersectionSupport_iff
    (A B C : Finset ι)
    (hBA : B ⊆ A) (hCA : C ⊆ A)
    (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex B)
    (q : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex C) :
    (K.intrinsicComponentLocalSlice A root).ShareIntersectionSupport B C p q ↔
    (K.subalphabetComponentSubgraph A root).ShareIntersectionSupport B C
      (K.rootedLocalAttachedCosetMap A B hBA root p)
      (K.rootedLocalAttachedCosetMap A C hCA root q) := by
  let L := K.intrinsicComponentLocalSlice A root
  let M := K.subalphabetComponentSubgraph A root
  have hIA : B ∩ C ⊆ A :=
    Finset.inter_subset_left.trans hBA
  constructor
  · rintro ⟨r, hrp, hrq⟩
    refine ⟨K.rootedLocalAttachedCosetMap A (B ∩ C) hIA root r, ?_, ?_⟩
    · calc
        M.attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left
            (K.rootedLocalAttachedCosetMap A (B ∩ C) hIA root r) =
          K.rootedLocalAttachedCosetMap A B hBA root
            (L.attachedSubalphabetMap (B ∩ C) B
              Finset.inter_subset_left r) :=
          (K.rootedLocalAttachedCosetMap_natural
            A (B ∩ C) B hIA Finset.inter_subset_left hBA root r).symm
        _ = K.rootedLocalAttachedCosetMap A B hBA root p :=
          congrArg _ hrp
    · calc
        M.attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right
            (K.rootedLocalAttachedCosetMap A (B ∩ C) hIA root r) =
          K.rootedLocalAttachedCosetMap A C hCA root
            (L.attachedSubalphabetMap (B ∩ C) C
              Finset.inter_subset_right r) :=
          (K.rootedLocalAttachedCosetMap_natural
            A (B ∩ C) C hIA Finset.inter_subset_right hCA root r).symm
        _ = K.rootedLocalAttachedCosetMap A C hCA root q :=
          congrArg _ hrq
  · rintro ⟨r, hrp, hrq⟩
    let R := K.rootedLocalAttachedCosetEquiv A (B ∩ C) hIA root
    let s : L.AttachedCosetVertex (B ∩ C) := R.symm r
    have hs : K.rootedLocalAttachedCosetMap A (B ∩ C) hIA root s = r :=
      R.apply_symm_apply r
    refine ⟨s, ?_, ?_⟩
    · apply (K.rootedLocalAttachedCosetEquiv A B hBA root).injective
      calc
        K.rootedLocalAttachedCosetMap A B hBA root
            (L.attachedSubalphabetMap (B ∩ C) B
              Finset.inter_subset_left s) =
          M.attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left
            (K.rootedLocalAttachedCosetMap A (B ∩ C) hIA root s) :=
          K.rootedLocalAttachedCosetMap_natural
            A (B ∩ C) B hIA Finset.inter_subset_left hBA root s
        _ = M.attachedSubalphabetMap (B ∩ C) B
              Finset.inter_subset_left r := by rw [hs]
        _ = K.rootedLocalAttachedCosetMap A B hBA root p := hrp
    · apply (K.rootedLocalAttachedCosetEquiv A C hCA root).injective
      calc
        K.rootedLocalAttachedCosetMap A C hCA root
            (L.attachedSubalphabetMap (B ∩ C) C
              Finset.inter_subset_right s) =
          M.attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right
            (K.rootedLocalAttachedCosetMap A (B ∩ C) hIA root s) :=
          K.rootedLocalAttachedCosetMap_natural
            A (B ∩ C) C hIA Finset.inter_subset_right hCA root s
        _ = M.attachedSubalphabetMap (B ∩ C) C
              Finset.inter_subset_right r := by rw [hs]
        _ = K.rootedLocalAttachedCosetMap A C hCA root q := hrq

end CayleySubgraphSpec
end ABO
end PSTSEPPA
