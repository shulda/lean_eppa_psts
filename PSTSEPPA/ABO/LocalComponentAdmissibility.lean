import PSTSEPPA.ABO.AdmissibleComponentIntersections

/-!
# Admissibility inherited by intrinsic subalphabet components

This is the local admissibility part of ABO Lemma 3.20, formulated
directly on the vertices and realised paths of the original skeleton.
It deliberately makes no claim yet about the injectivity of the
full lower coset extension into the ambient subgroup Cayley graph.

Let B ⊂ A and fix the intrinsic B-component of a vertex root. Any
D⊂B-labelled path stays inside this component. Moreover, for any
D₁,D₂ ⊂ D ⊂ B, an admissibility witness produced by the parent
A-skeleton stays in that same B-component. Thus no new forbidden
coset-overlap pattern can arise by restricting to the B-component.

This is the actual inheritance argument in Lemma 3.20, including
equal lower alphabets and empty D₁ or D₂.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Any D-path with D ⊆ B from a vertex in an intrinsic B-component
remains in the same intrinsic B-component. -/
theorem subalphabetComponent_path_closed
    (B D : Finset ι) (hDB : D ⊆ B)
    (root x y : K.Vertex)
    (hx : x ∈ K.SubalphabetComponent B root)
    (hxy : K.SubalphabetReachable D x y) :
    y ∈ K.SubalphabetComponent B root :=
  K.subalphabetReachable_trans B hx
    (K.subalphabetReachable_mono D B hDB hxy)

/-- Witnesses to admissibility inside a B-component of K stay
inside that B-component. This is the local inheritance clause
needed for ABO Lemma 3.20.

All D,D₁,D₂ are proper at their respective rank; D₁ and D₂ may be
equal, and either may be empty. No assumption on |B| is needed for
this logical inheritance step. -/
theorem admissible_witness_within_component
    (hadm : K.AdmissibleForCosetExtension)
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (D D₁ D₂ : Finset ι)
    (hDB : D ⊂ B) (hD₁ : D₁ ⊂ D) (hD₂ : D₂ ⊂ D)
    (x y : K.Vertex)
    (hx : x ∈ K.SubalphabetComponent B root)
    (_hy : y ∈ K.SubalphabetComponent B root)
    (hxy : K.SubalphabetReachable D x y)
    (hcoset :
      (generatedLeftCoset gen D₁ x.1 ∩
        generatedLeftCoset gen D₂ y.1).Nonempty) :
    ∃ z : K.Vertex,
      z ∈ K.SubalphabetComponent B root ∧
      K.SubalphabetReachable D₁ x z ∧
      K.SubalphabetReachable D₂ y z := by
  have hDA : D ⊂ A := lt_trans hDB hBA
  obtain ⟨z, hxz, hyz⟩ :=
    hadm D D₁ D₂ hDA hD₁ hD₂ x y hxy hcoset
  have hD₁B : D₁ ⊆ B := hD₁.subset.trans hDB.subset
  exact ⟨z,
    K.subalphabetComponent_path_closed B D₁ hD₁B root x z hx hxz,
    hxz, hyz⟩

/-- For any lower alphabet D⊂B, intersecting a D-component with
the chosen B-component never cuts it into pieces. -/
theorem lowerComponent_subset_of_member
    (B D : Finset ι) (hDB : D ⊆ B)
    (root x : K.Vertex)
    (hx : x ∈ K.SubalphabetComponent B root) :
    K.SubalphabetComponent D x ⊆
      K.SubalphabetComponent B root := by
  intro y hy
  exact K.subalphabetComponent_path_closed B D hDB root x y hx hy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
