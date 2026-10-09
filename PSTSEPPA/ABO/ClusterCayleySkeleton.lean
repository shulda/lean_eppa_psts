import PSTSEPPA.ABO.CayleySubgraph
import PSTSEPPA.ABO.AugmentedCluster

/-!
# Literal cluster and augmented-cluster Cayley skeletons

The cluster and augmented-cluster constructions have already been
formalized as unions of vertex sets and signed Cayley edge-token sets.
To reason about *intrinsic path components*, rather than merely about
ambient cosets, we expose those same unions as CayleySubgraphSpec.

For an A-cluster all constituent alphabet labels lie in A.
For a B-augmentation we additionally require B ⊆ A. No group
retractability, connectivity or generation hypothesis is necessary
just to construct these literal labelled subgraphs.

These are definitions of exactly the previously checked vertex and
edge sets; they add no edges and make no ambient-coset identifications.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- The literal union-of-subgroups cluster regarded as an arbitrary
incomplete Cayley skeleton, with exactly the old edge tokens. -/
noncomputable def toCayleySubgraph
    (gen : ι → Γ) (P : ClusterSpec A) :
    CayleySubgraphSpec gen A where
  vertices := P.VertexSet gen
  edges := P.EdgeSet gen
  source_mem := by
    intro e he
    exact P.edge_source_mem gen he
  inv_mem := by
    intro e he
    exact P.edge_inv_mem gen he
  label_mem := by
    intro e he
    obtain ⟨C, hCP, _hsource, hlabel⟩ := he
    exact (P.proper C hCP).subset hlabel

/-- The vertex set of the Cayley skeleton is exactly that of the
original cluster, without choosing representatives or completions. -/
theorem toCayleySubgraph_vertices
    (gen : ι → Γ) (P : ClusterSpec A) :
    (P.toCayleySubgraph gen).vertices = P.VertexSet gen :=
  rfl

/-- Its directed edge set is the same literal signed-edge set. -/
theorem toCayleySubgraph_edges
    (gen : ι → Γ) (P : ClusterSpec A) :
    (P.toCayleySubgraph gen).edges = P.EdgeSet gen :=
  rfl

/-- Augmenting with a subalphabet B ⊆ A also produces a literal
A-labelled Cayley skeleton, with all old cluster edges and the
completed B-coset edges, but no other edges. -/
noncomputable def augmentedCayleySubgraph
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    CayleySubgraphSpec gen A where
  vertices := P.AugmentedVertexSet gen B v
  edges := P.AugmentedEdgeSet gen B v
  source_mem := by
    intro e he
    exact P.augmented_edge_source_mem gen B v he
  inv_mem := by
    intro e he
    exact P.augmented_edge_inv_mem gen B v he
  label_mem := by
    intro e he
    rcases he with heOld | heAdded
    · obtain ⟨C, hCP, _, hl⟩ := heOld
      exact (P.proper C hCP).subset hl
    · exact hBA heAdded.2

/-- The augmented skeleton retains precisely the union's vertices. -/
theorem augmentedCayleySubgraph_vertices
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    (P.augmentedCayleySubgraph gen B hBA v).vertices =
      P.AugmentedVertexSet gen B v :=
  rfl

/-- The augmented skeleton retains precisely the union's directed
edge tokens, including inverse tokens at geometric loops. -/
theorem augmentedCayleySubgraph_edges
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    (P.augmentedCayleySubgraph gen B hBA v).edges =
      P.AugmentedEdgeSet gen B v :=
  rfl

end ClusterSpec
end ABO
end PSTSEPPA
