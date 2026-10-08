import PSTSEPPA.ABO.ComponentSubgraphPaths
import PSTSEPPA.ABO.LocalComponentAdmissibility

/-!
# ABO Lemma 3.20: admissibility of a literal B-component subgraph

A B-component of an admissible A-skeleton can be viewed as a
CayleySubgraphSpec whose vertices and directed edge tokens are the
actual B-path component of K. We prove this lower-rank B-skeleton is
itself admissible for its proper subalphabet coset extensions.

The proof does not replace intrinsic paths with ambient group
coset membership. It maps any lower-alphabet path to the parent
skeleton, invokes inherited admissibility there, and then uses the
checked path-lifting theorem to bring both lower-alphabet witness
paths back into the literal B-component subgraph.

This proves the *admissibility* clause of ABO Lemma 3.20, not yet
the independent claim that its full lower coset extension embeds
into the subgroup Cayley graph.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Any vertex of the literal B-component subgraph is represented
by an original skeleton vertex reachable from root by a B-path. -/
theorem componentSubgraph_vertex_reachable
    (B : Finset ι) (root : K.Vertex)
    (x : (K.subalphabetComponentSubgraph B root).Vertex) :
    K.SubalphabetReachable B root
      ((K.subalphabetComponentSubgraphHom B root).onVertex x) := by
  rcases x.2 with ⟨u, hu, hreach⟩
  have hEq :
      u = (K.subalphabetComponentSubgraphHom B root).onVertex x := by
    apply Subtype.ext
    exact hu
  rwa [hEq] at hreach

/-- The explicit B-component graph inherits the admissibility
property from the ambient A-skeleton. No additional cardinality
assumption is needed for this implication. -/
theorem subalphabetComponentSubgraph_admissible
    (hadm : K.AdmissibleForCosetExtension)
    (B : Finset ι) (hBA : B ⊂ A) (root : K.Vertex) :
    (K.subalphabetComponentSubgraph B root).AdmissibleForCosetExtension := by
  intro D D₁ D₂ hDB hD₁ hD₂ x y hxy hcoset
  let ix : K.Vertex :=
    (K.subalphabetComponentSubgraphHom B root).onVertex x
  let iy : K.Vertex :=
    (K.subalphabetComponentSubgraphHom B root).onVertex y
  have hxRoot : K.SubalphabetReachable B root ix :=
    K.componentSubgraph_vertex_reachable B root x
  have hyRoot : K.SubalphabetReachable B root iy :=
    K.componentSubgraph_vertex_reachable B root y
  obtain ⟨w, hw, hp⟩ := hxy
  have hparent : K.SubalphabetReachable D ix iy :=
    ⟨w, hw, hp.map (K.subalphabetComponentSubgraphHom B root)⟩
  have hparentCoset :
      (generatedLeftCoset gen D₁ ix.1 ∩
        generatedLeftCoset gen D₂ iy.1).Nonempty :=
    hcoset
  obtain ⟨z, hzRoot, hxz, hyz⟩ :=
    K.admissible_witness_within_component
      hadm B hBA root D D₁ D₂ hDB hD₁ hD₂
      ix iy hxRoot hyRoot hparent hparentCoset
  let zSub : (K.subalphabetComponentSubgraph B root).Vertex :=
    K.componentLiftVertex B root z hzRoot
  have hD₁B : D₁ ⊆ B := hD₁.subset.trans hDB.subset
  have hD₂B : D₂ ⊆ B := hD₂.subset.trans hDB.subset
  obtain ⟨hzX, hxzSub⟩ :=
    K.reachable_lift_component B D₁ hD₁B root ix z hxRoot hxz
  obtain ⟨hzY, hyzSub⟩ :=
    K.reachable_lift_component B D₂ hD₂B root iy z hyRoot hyz
  refine ⟨zSub, ?_, ?_⟩
  · have hStart : K.componentLiftVertex B root ix hxRoot = x := by
      apply Subtype.ext
      rfl
    have hEnd : K.componentLiftVertex B root z hzX = zSub := by
      apply Subtype.ext
      rfl
    rw [hStart, hEnd] at hxzSub
    exact hxzSub
  · have hStart : K.componentLiftVertex B root iy hyRoot = y := by
      apply Subtype.ext
      rfl
    have hEnd : K.componentLiftVertex B root z hzY = zSub := by
      apply Subtype.ext
      rfl
    rw [hStart, hEnd] at hyzSub
    exact hyzSub

end CayleySubgraphSpec
end ABO
end PSTSEPPA
