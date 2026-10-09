import PSTSEPPA.ABO.ClusterCayleySkeleton
import PSTSEPPA.ABO.CayleySubgraphFullCosetPaths
import PSTSEPPA.ABO.ComponentIndexMonotonicity
import PSTSEPPA.ABO.ClusterComponents

/-!
# Genuine subalphabet components of retractable ABO clusters

For a cluster CL(G[A], P), the familiar intersection with an ambient
C-coset is an exact *graph component*, not merely a set of group
coordinates: under retractability, all vertices of that slice are
connected by actual C-labelled paths of the cluster.

The proof selects the common point of every active constituent,
provided by the earlier Helly/coset intersection argument. Any
vertex of the slice lies in a (D∩C)-coset based at that same point.
Every edge of that small coset is a literal cluster edge because
the common point belongs to G[D]. The full-coset path lifting lemma
then connects the common point to every vertex using realised edges.

No completion or implicit identification of ambient group points is
involved; both endpoints and all path edges are in the original
cluster Cayley skeleton.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- A translated E-coset based at z∈G[D] is fully present as
E-labelled directed edges in a D-constituent, provided E⊆D.
This is the precise bridge from subgroup/coset algebra to the
literal graph edge set. -/
theorem fullCosetEdge_mem_of_piece
    (gen : ι → Γ) (P : ClusterSpec A)
    (D E : Finset ι) (hDP : D ∈ P.pieces) (hED : E ⊆ D)
    (z : Γ) (hzD : z ∈ generatedSubgroup gen D)
    (e : ActionEdge Γ ι)
    (he : e ∈ FullCosetEdgeSet gen E z) :
    e ∈ (P.toCayleySubgraph gen).edges := by
  have hstepD :
      z⁻¹ * (cayleyGraph gen).source e ∈
        generatedSubgroup gen D :=
    generatedSubgroup_mono gen hED he.1
  have hsD :
      (cayleyGraph gen).source e ∈
        generatedSubgroup gen D := by
    have hprod :=
      (generatedSubgroup gen D).mul_mem hzD hstepD
    simpa [mul_assoc] using hprod
  exact P.constituent_edge_mem gen hDP hsD (hED he.2)

/-- A vertex in the chosen D-constituent and ambient C-coset is
connected to any common point z of that constituent and coset,
using only actual C-labelled edges of the cluster. -/
theorem reachable_in_piece_inter_coset
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (C : Finset ι) (u : Γ)
    (D : Finset ι) (hDP : D ∈ P.pieces)
    (z x : (P.toCayleySubgraph gen).Vertex)
    (hzD : z.1 ∈ generatedSubgroup gen D)
    (hzC : z.1 ∈ generatedLeftCoset gen C u)
    (hxD : x.1 ∈ generatedSubgroup gen D)
    (hxC : x.1 ∈ generatedLeftCoset gen C u) :
    (P.toCayleySubgraph gen).SubalphabetReachable C z x := by
  let K := P.toCayleySubgraph gen
  have hinter :=
    constituent_inter_coset_eq
      gen hgen hret D C u z.1 hzD hzC
  have hxSmall :
      x.1 ∈ generatedLeftCoset gen (D ∩ C) z.1 := by
    rw [← hinter]
    exact ⟨hxD, hxC⟩
  have hstart :
      z.1 ∈ generatedLeftCoset gen (D ∩ C) z.1 :=
    self_mem_generatedLeftCoset gen (D ∩ C) z.1
  have hreachable :
      K.SubalphabetReachable (D ∩ C) z x := by
    apply K.reachable_in_fullCoset (D ∩ C) z.1
      (fun e he =>
        P.fullCosetEdge_mem_of_piece gen D (D ∩ C)
          hDP Finset.inter_subset_left z.1 hzD e he)
      z x hstart hxSmall
  exact K.subalphabetReachable_mono
    (D ∩ C) C Finset.inter_subset_right hreachable

/-- Every ambient C-coset slice of a retractable ordinary cluster
is intrinsically C-path-connected on its actual cluster vertices.
The statement is vacuous when that slice is empty. -/
theorem componentSlice_actual_reachable
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (C : Finset ι) (u : Γ)
    (x y : (P.toCayleySubgraph gen).Vertex)
    (hxC : x.1 ∈ generatedLeftCoset gen C u)
    (hyC : y.1 ∈ generatedLeftCoset gen C u) :
    (P.toCayleySubgraph gen).SubalphabetReachable C x y := by
  let K := P.toCayleySubgraph gen
  obtain ⟨z, hzC, hzPieces⟩ :=
    P.activePieces_common_point gen hgen hret C u
  obtain ⟨D, hDP, hxD⟩ := x.2
  have hActiveD : D ∈ P.ActivePieces gen C u :=
    (P.mem_activePieces_iff gen C u D).2
      ⟨hDP, ⟨x.1, hxD, hxC⟩⟩
  have hzD := hzPieces D hActiveD
  let zv : K.Vertex :=
    ⟨z, P.constituent_vertex_mem gen hDP hzD⟩
  have hzx : K.SubalphabetReachable C zv x :=
    P.reachable_in_piece_inter_coset
      gen hgen hret C u D hDP zv x hzD hzC hxD hxC
  obtain ⟨E, hEP, hyE⟩ := y.2
  have hActiveE : E ∈ P.ActivePieces gen C u :=
    (P.mem_activePieces_iff gen C u E).2
      ⟨hEP, ⟨y.1, hyE, hyC⟩⟩
  have hzE := hzPieces E hActiveE
  have hzy : K.SubalphabetReachable C zv y :=
    P.reachable_in_piece_inter_coset
      gen hgen hret C u E hEP zv y hzE hzC hyE hyC
  exact K.subalphabetReachable_trans C
    (K.subalphabetReachable_symm C hzx) hzy

/-- Exact intrinsic C-component criterion for ordinary clusters:
two cluster vertices are joined by a realised C-word path if and
only if they lie in the same ambient C-coset. Unlike the general
Cayley-skeleton case, the converse holds for retractable clusters. -/
theorem cluster_reachable_iff_ambient_coset
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (C : Finset ι)
    (x y : (P.toCayleySubgraph gen).Vertex) :
    (P.toCayleySubgraph gen).SubalphabetReachable C x y ↔
      y.1 ∈ generatedLeftCoset gen C x.1 := by
  constructor
  · intro hxy
    exact (P.toCayleySubgraph gen).subalphabetReachable_implies_coset
      C x y hxy
  · intro hy
    exact P.componentSlice_actual_reachable gen hgen hret
      C x.1 x y (self_mem_generatedLeftCoset gen C x.1) hy

end ClusterSpec
end ABO
end PSTSEPPA
