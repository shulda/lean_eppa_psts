import PSTSEPPA.ABO.AugmentedClusterIndexedFamily
import PSTSEPPA.ABO.AugmentedClusterLocalSubgroupMembership

/-!
# Exact original-source type-(1) augmented-cluster stage index normalization

The original ambient Γ type-(1) Definition-5.3 source indices
record (P,D,v): a cluster P of proper A-subalphabets, a proper
attachment D⊂A and the ACTUAL anchored point v in P.

Because P is a union of proper A-generated subgroups, every
ambient anchor v already lies in Γ[A]. The subgroup-membership
reflection theorem then identifies the ORIGINAL ambient
(P,D,v) indices with the corresponding TRUE local Γ[A]
augmented-cluster indices, without choosing representatives.

Both the cluster and attachment tags remain literally unchanged;
anchors are mapped only via the honest Γ[A] inclusion.
The action-fibre isomorphism is separate, not assumed here.
-/

namespace PSTSEPPA
namespace ABO

namespace ClusterSpec

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {A : Finset ι}

/-- Every anchored vertex of a proper A-cluster in the ambient
group lies in Γ[A], independently of retractability. -/
theorem vertexSet_mem_parentSubgroup
    (gen : ι → Γ) (P : ClusterSpec A)
    (x : Γ) (hx : x ∈ P.VertexSet gen) :
    x ∈ generatedSubgroup gen A := by
  rcases hx with ⟨C, hCP, hxC⟩
  exact generatedSubgroup_mono gen (P.proper C hCP).subset hxC

/-- Exact fibrewise equivalence between ALL genuine ambient
type-(1) source augmentation indices and their local Γ[A]
indices. Retains the ACTUAL cluster, D-subalphabet and
anchored vertex rather than only their cardinalities. -/
noncomputable def localType1StageIndexEquiv
    (gen : ι → Γ) (A : Finset ι) :
    augmentedType1Index (trivialCompletionGenerator gen A) A ≃
      augmentedType1Index gen A where
  toFun j :=
    ⟨j.1, j.2.1,
      ⟨(j.2.2.1 : Γ),
        (j.1.localVertexSet_iff_ambient gen j.2.2.1).mp j.2.2.2⟩⟩
  invFun j :=
    ⟨j.1, j.2.1,
      ⟨(⟨j.2.2.1,
        j.1.vertexSet_mem_parentSubgroup
          gen j.2.2.1 j.2.2.2⟩ : generatedSubgroup gen A),
        (j.1.localVertexSet_iff_ambient gen
          ⟨j.2.2.1,
            j.1.vertexSet_mem_parentSubgroup
              gen j.2.2.1 j.2.2.2⟩).mpr j.2.2.2⟩⟩
  left_inv := by
    rintro ⟨P, D, ⟨v, hv⟩⟩
    rfl
  right_inv := by
    rintro ⟨P, D, ⟨v, hv⟩⟩
    rfl

/-- Cluster and D-augmentation tags are exactly preserved
by the canonical ambient/local type-(1) index equivalence. -/
@[simp] theorem localType1StageIndexEquiv_tags
    (gen : ι → Γ) (A : Finset ι)
    (j : augmentedType1Index
      (trivialCompletionGenerator gen A) A) :
    (localType1StageIndexEquiv gen A j).1 = j.1 ∧
    (localType1StageIndexEquiv gen A j).2.1 = j.2.1 :=
  ⟨rfl, rfl⟩

end ClusterSpec
end ABO
end PSTSEPPA
