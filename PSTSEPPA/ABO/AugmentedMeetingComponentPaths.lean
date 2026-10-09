import PSTSEPPA.ABO.ClusterComponentPaths
import PSTSEPPA.ABO.AugmentedClusterPathInclusion
import PSTSEPPA.ABO.AugmentedIntersectionCosetPaths

/-!
# Realised C-components of augmented clusters: the meeting case

Suppose the attached full B-coset meets the original cluster's
C-slice inside a chosen ambient C-coset. We prove that the entire
C-slice of the *augmented* graph is genuinely C-path-connected.

The old part is connected by actual cluster C-paths (proved using
the retractability/active-constituent common point theorem).
The added part is connected to any intersection point through
actual (B∩C)-labelled edges, not just by group coset equality.
Since the old and added pieces share a real vertex, concatenation
of paths connects arbitrary points of the whole augmented slice.

This upgrades the existing exact vertex/edge set classification
from ABO Corollary 3.15 in the nontrivial meeting case to the
intrinsic graph-component assertion.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- Whenever the old C-slice and the attached B-coset share the
literal vertex z, all augmented vertices inside their ambient
C-coset are joined by actual C-labelled paths. -/
theorem augmented_meeting_component_reachable
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzOld : z ∈ P.ComponentSlice gen C u)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (x y : (P.augmentedCayleySubgraph gen B hBA v).Vertex)
    (hxC : x.1 ∈ generatedLeftCoset gen C u)
    (hyC : y.1 ∈ generatedLeftCoset gen C u) :
    (P.augmentedCayleySubgraph gen B hBA v).SubalphabetReachable
      C x y := by
  let K := P.augmentedCayleySubgraph gen B hBA v
  let zAug : K.Vertex := ⟨z, Or.inl hzOld.1⟩
  have hbridge (t : K.Vertex)
      (htC : t.1 ∈ generatedLeftCoset gen C u) :
      K.SubalphabetReachable C zAug t := by
    rcases t.2 with htOld | htAttached
    · let zOld : (P.toCayleySubgraph gen).Vertex := ⟨z, hzOld.1⟩
      let tOld : (P.toCayleySubgraph gen).Vertex := ⟨t.1, htOld⟩
      have hOldPath :=
        P.componentSlice_actual_reachable gen hgen hret
          C u zOld tOld hzOld.2 htC
      have hAugPath :=
        P.cluster_reachable_in_augmented gen B hBA v
          C zOld tOld hOldPath
      have hzEq :
          (P.clusterSkeletonToAugmentedHom gen B hBA v).onVertex zOld =
            zAug := by
        apply Subtype.ext
        rfl
      have htEq :
          (P.clusterSkeletonToAugmentedHom gen B hBA v).onVertex tOld =
            t := by
        apply Subtype.ext
        rfl
      rw [hzEq, htEq] at hAugPath
      exact hAugPath
    · have hinter :=
        generatedLeftCoset_inter gen hgen hret
          B C v u z hzB hzOld.2
      have htSmall :
          t.1 ∈ generatedLeftCoset gen (B ∩ C) z := by
        rw [← hinter]
        exact ⟨htAttached, htC⟩
      have hzSmall :
          z ∈ generatedLeftCoset gen (B ∩ C) z :=
        self_mem_generatedLeftCoset gen (B ∩ C) z
      exact P.augmented_intersectionCoset_reachable
        gen hgen hret B hBA v C u z hzB hzOld.2
        zAug t hzSmall htSmall
  have hzx := hbridge x hxC
  have hzy := hbridge y hyC
  exact K.subalphabetReachable_trans C
    (K.subalphabetReachable_symm C hzx) hzy

/-- Nonempty intersection formulation of the genuine connected
meeting case of ABO Corollary 3.15. The common basepoint is
chosen existentially, avoiding any canonical representative. -/
theorem augmented_meeting_component_connected
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (C : Finset ι) (u : Γ)
    (hmeet :
      (P.ComponentSlice gen C u ∩
        generatedLeftCoset gen B v).Nonempty)
    (x y : (P.augmentedCayleySubgraph gen B hBA v).Vertex)
    (hxC : x.1 ∈ generatedLeftCoset gen C u)
    (hyC : y.1 ∈ generatedLeftCoset gen C u) :
    (P.augmentedCayleySubgraph gen B hBA v).SubalphabetReachable
      C x y := by
  obtain ⟨z, hzOld, hzB⟩ := hmeet
  exact P.augmented_meeting_component_reachable
    gen hgen hret B hBA v C u z hzOld hzB x y hxC hyC

end ClusterSpec
end ABO
end PSTSEPPA
