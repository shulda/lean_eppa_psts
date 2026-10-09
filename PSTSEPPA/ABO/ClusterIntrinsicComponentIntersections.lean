import PSTSEPPA.ABO.ClusterComponentPaths
import PSTSEPPA.ABO.ClusterComponentIntersections
import PSTSEPPA.ABO.SubgroupIntersections
import PSTSEPPA.ABO.ComponentIndexMonotonicity

/-!
# Intrinsic intersection of B- and C-components of an ordinary cluster

The earlier Corollary 3.13 layer identifies intersections of ambient
B- and C-coset slices on literal vertices and signed edge tokens.
The new ordinary-cluster path theorem proves that those slices are
*actual* subalphabet path components, not merely set descriptions.

Here we upgrade their intersection classification to a genuine
(B ∩ C)-reachability theorem. The proof is short but mathematically
substantive: retractability gives
    G[B] ∩ G[C] = G[B∩C],
and the cluster-specific path-reflection theorem realises every
resulting (B∩C)-word by edges in the original incomplete cluster.

This is the intrinsic path-component form of ABO Corollary 3.13,
and supplies the cluster case later invoked inside Proposition 3.23.
It also handles B=C, nested alphabets and empty intersections.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- Two vertices belonging to both the same intrinsic B-component
and the same intrinsic C-component of a retractable cluster are
joined by an actual (B∩C)-supported path inside that cluster. -/
theorem cluster_component_intersection_actual_reachable
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A)
    (B C : Finset ι)
    (b c x y : (P.toCayleySubgraph gen).Vertex)
    (hbx : (P.toCayleySubgraph gen).SubalphabetReachable B b x)
    (hby : (P.toCayleySubgraph gen).SubalphabetReachable B b y)
    (hcx : (P.toCayleySubgraph gen).SubalphabetReachable C c x)
    (hcy : (P.toCayleySubgraph gen).SubalphabetReachable C c y) :
    (P.toCayleySubgraph gen).SubalphabetReachable (B ∩ C) x y := by
  let K := P.toCayleySubgraph gen
  have hxyB : K.SubalphabetReachable B x y :=
    K.subalphabetReachable_trans B
      (K.subalphabetReachable_symm B hbx) hby
  have hxyC : K.SubalphabetReachable C x y :=
    K.subalphabetReachable_trans C
      (K.subalphabetReachable_symm C hcx) hcy
  have hcosetB : y.1 ∈ generatedLeftCoset gen B x.1 :=
    K.subalphabetReachable_implies_coset B x y hxyB
  have hcosetC : y.1 ∈ generatedLeftCoset gen C x.1 :=
    K.subalphabetReachable_implies_coset C x y hxyC
  have hcosetBC : y.1 ∈ generatedLeftCoset gen (B ∩ C) x.1 := by
    change x.1⁻¹ * y.1 ∈ generatedSubgroup gen (B ∩ C)
    rw [← generatedSubgroup_inf gen hgen hret B C]
    exact ⟨hcosetB, hcosetC⟩
  exact (P.cluster_reachable_iff_ambient_coset gen hgen hret
    (B ∩ C) x y).2 hcosetBC

/-- Literal set equality on *actual vertices* of the retractable
cluster: a nonempty intersection of intrinsic B- and C-components
is precisely one intrinsic (B∩C)-component. This does not
require either original component to be an entire ambient coset. -/
theorem cluster_intrinsic_component_inter_eq
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A)
    (B C : Finset ι)
    (b c x : (P.toCayleySubgraph gen).Vertex)
    (hbx : (P.toCayleySubgraph gen).SubalphabetReachable B b x)
    (hcx : (P.toCayleySubgraph gen).SubalphabetReachable C c x) :
    {y : (P.toCayleySubgraph gen).Vertex |
      (P.toCayleySubgraph gen).SubalphabetReachable B b y ∧
      (P.toCayleySubgraph gen).SubalphabetReachable C c y} =
    {y : (P.toCayleySubgraph gen).Vertex |
      (P.toCayleySubgraph gen).SubalphabetReachable (B ∩ C) x y} := by
  let K := P.toCayleySubgraph gen
  ext y
  constructor
  · rintro ⟨hby, hcy⟩
    exact P.cluster_component_intersection_actual_reachable
      gen hgen hret B C b c x y hbx hby hcx hcy
  · intro hxy
    have hxyB : K.SubalphabetReachable B x y :=
      K.subalphabetReachable_mono (B ∩ C) B
        Finset.inter_subset_left hxy
    have hxyC : K.SubalphabetReachable C x y :=
      K.subalphabetReachable_mono (B ∩ C) C
        Finset.inter_subset_right hxy
    exact ⟨K.subalphabetReachable_trans B hbx hxyB,
      K.subalphabetReachable_trans C hcx hxyC⟩

end ClusterSpec
end ABO
end PSTSEPPA
