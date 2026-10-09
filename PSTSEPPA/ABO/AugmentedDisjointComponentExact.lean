import PSTSEPPA.ABO.ClusterComponentPaths
import PSTSEPPA.ABO.AugmentedClusterPathInclusion
import PSTSEPPA.ABO.AugmentedIntersectionCosetPaths
import PSTSEPPA.ABO.AugmentedDisjointPathSeparation

/-!
# Exact two-piece intrinsic C-component classification for augmentations

Suppose the attached B-coset intersects the ambient C-coset at z
but is disjoint from the *original cluster's C-slice*.
The augmented C-slice is then the disjoint union of that old
C-slice and the new zG[B∩C] coset.

This file gives the full path-component statement: two augmented
vertices in that ambient C-coset admit a realised C-word path
exactly when they belong to the *same one of these two pieces*.

In the positive directions, old/old paths are inherited from
the retractable cluster and new/new paths use genuine attached
(B∩C)-edges. In the negative direction, the previously checked
edge separation is promoted to a path invariant.

Thus the set-theoretic disjoint-union classification from
ABO Corollary 3.15 is a classification of actual connected
subalphabet components.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- Disjoint two-piece criterion for actual C-path reachability
within the augmented C-slice. The old piece may be empty, in
which case only the attached intersection-coset piece occurs. -/
theorem augmented_disjoint_C_reachable_iff_same_piece
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C u)
    (hdisj :
      P.ComponentSlice gen C u ∩
        generatedLeftCoset gen B v = ∅)
    (x y : (P.augmentedCayleySubgraph gen B hBA v).Vertex)
    (hxC : x.1 ∈ generatedLeftCoset gen C u)
    (hyC : y.1 ∈ generatedLeftCoset gen C u) :
    (P.augmentedCayleySubgraph gen B hBA v).SubalphabetReachable C x y ↔
      ((x.1 ∈ P.ComponentSlice gen C u ∧
        y.1 ∈ P.ComponentSlice gen C u) ∨
      (x.1 ∈ generatedLeftCoset gen (B ∩ C) z ∧
        y.1 ∈ generatedLeftCoset gen (B ∩ C) z)) := by
  let K := P.augmentedCayleySubgraph gen B hBA v
  have hinter :=
    generatedLeftCoset_inter gen hgen hret B C v u z hzB hzC
  constructor
  · rintro ⟨w, hw, hpath⟩
    rcases x.2 with hxOld | hxAdded
    · left
      have hxSlice : x.1 ∈ P.ComponentSlice gen C u :=
        ⟨hxOld, hxC⟩
      have hySlice :=
        P.augmented_old_C_slice_path_invariant
          gen hgen hret B hBA v C u z hzB hzC hdisj
          hpath hw hxSlice
      exact ⟨hxSlice, hySlice⟩
    · have hxSmall :
          x.1 ∈ generatedLeftCoset gen (B ∩ C) z := by
        rw [← hinter]
        exact ⟨hxAdded, hxC⟩
      rcases y.2 with hyOld | hyAdded
      · have hySlice : y.1 ∈ P.ComponentSlice gen C u :=
          ⟨hyOld, hyC⟩
        have hback : K.SubalphabetReachable C y x :=
          K.subalphabetReachable_symm C ⟨w, hw, hpath⟩
        have hf :=
          P.augmented_disjoint_old_new_not_C_reachable
            gen hgen hret B hBA v C u z hzB hzC hdisj
            y x hySlice hxSmall hback
        exact hf.elim
      · right
        have hySmall :
            y.1 ∈ generatedLeftCoset gen (B ∩ C) z := by
          rw [← hinter]
          exact ⟨hyAdded, hyC⟩
        exact ⟨hxSmall, hySmall⟩
  · rintro (⟨hxOld, hyOld⟩ | ⟨hxNew, hyNew⟩)
    · let xOld : (P.toCayleySubgraph gen).Vertex :=
        ⟨x.1, hxOld.1⟩
      let yOld : (P.toCayleySubgraph gen).Vertex :=
        ⟨y.1, hyOld.1⟩
      have hp :=
        P.componentSlice_actual_reachable gen hgen hret
          C u xOld yOld hxOld.2 hyOld.2
      have hmap :=
        P.cluster_reachable_in_augmented gen B hBA v
          C xOld yOld hp
      have hxEq :
          (P.clusterSkeletonToAugmentedHom gen B hBA v).onVertex xOld =
            x := by
        apply Subtype.ext
        rfl
      have hyEq :
          (P.clusterSkeletonToAugmentedHom gen B hBA v).onVertex yOld =
            y := by
        apply Subtype.ext
        rfl
      rw [hxEq, hyEq] at hmap
      exact hmap
    · exact P.augmented_intersectionCoset_reachable
        gen hgen hret B hBA v C u z hzB hzC x y hxNew hyNew

end ClusterSpec
end ABO
end PSTSEPPA
