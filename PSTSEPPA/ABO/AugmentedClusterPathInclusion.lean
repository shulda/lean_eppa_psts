import PSTSEPPA.ABO.ClusterCayleySkeleton
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Intrinsic paths inherited by augmented cluster skeletons

An ABO augmented cluster is the literal union of an existing
cluster and a completed B-coset. To compare actual C-components,
we need the original cluster's C-paths to remain genuine paths
inside the augmentation.

This file constructs the exact labelled graph inclusion on both
vertices and signed oriented edge tokens, proves its injectivity,
and transports arbitrary realised subalphabet paths. It also
records the literal inclusion of the full attached B-coset's
oriented edge set, for the subsequent connectivity comparison.

No connectivity of the ambient Cayley coset is silently assumed;
path existence is transported only when already witnessed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- Old cluster edges and vertices are embedded literally into
the A-labelled skeleton of the B-augmentation. -/
noncomputable def clusterSkeletonToAugmentedHom
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    LabelledGraphHom
      (P.toCayleySubgraph gen).toLabelledGraph
      (P.augmentedCayleySubgraph gen B hBA v).toLabelledGraph where
  onVertex x := ⟨x.1, Or.inl x.2⟩
  onEdge e := ⟨e.1, Or.inl e.2⟩
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

/-- The augmentation retains distinct original cluster vertices. -/
theorem clusterSkeletonToAugmentedHom_vertex_injective
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    Function.Injective
      (P.clusterSkeletonToAugmentedHom gen B hBA v).onVertex := by
  intro x y h
  apply Subtype.ext
  exact congrArg Subtype.val h

/-- It also retains the actual signed directed edge tokens, including
formal inverses and the two directed tokens of geometric loops. -/
theorem clusterSkeletonToAugmentedHom_edge_injective
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    Function.Injective
      (P.clusterSkeletonToAugmentedHom gen B hBA v).onEdge := by
  intro e f h
  apply Subtype.ext
  exact congrArg Subtype.val h

/-- Every actual C-labelled word path of the original cluster is
still a path of the augmented cluster between the included vertices. -/
theorem cluster_reachable_in_augmented
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (C : Finset ι)
    (x y : (P.toCayleySubgraph gen).Vertex)
    (hxy : (P.toCayleySubgraph gen).SubalphabetReachable C x y) :
    (P.augmentedCayleySubgraph gen B hBA v).SubalphabetReachable C
      ((P.clusterSkeletonToAugmentedHom gen B hBA v).onVertex x)
      ((P.clusterSkeletonToAugmentedHom gen B hBA v).onVertex y) := by
  obtain ⟨w, hw, hpath⟩ := hxy
  exact ⟨w, hw,
    hpath.map (P.clusterSkeletonToAugmentedHom gen B hBA v)⟩

/-- Every completed B-labelled edge in the attached coset belongs
literally to the augmented Cayley subgraph, with no quotienting. -/
theorem fullCosetEdge_mem_augmented
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (e : ActionEdge Γ ι)
    (he : e ∈ FullCosetEdgeSet gen B v) :
    e ∈ (P.augmentedCayleySubgraph gen B hBA v).edges :=
  Or.inr he

end ClusterSpec
end ABO
end PSTSEPPA
