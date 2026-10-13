import PSTSEPPA.ABO.AugmentedCluster
import PSTSEPPA.ABO.LocalSubgroupCosetNaturality
import PSTSEPPA.ABO.SubgroupIntersections

/-!
# True type-(1) cluster / augmentation geometry in H₁[A] and ambient H₁

For a finite alphabet A, the proper-constituent cluster and
a B⊆A augmentation over the actual subgroup H₁[A] have
EXACTLY the same vertices and signed edge-membership conditions
as their original ambient H₁ models, under the honest subgroup
inclusion H₁[A] ↪ H₁.

Neither global retractability nor a Cayley-coordinate collapse
is used. All comparisons use the genuine subalphabet-generated
subgroups and left B-cosets, including repeated/trivial generators
and both signs of the directed edge labels.

These exact memberships are the prerequisite for constructing
the complete source/local type-(1) labelled-graph isomorphism
and linking original Definition-5.3 type-(1) Z₁ to the concrete
finite source G₂ local action catalogue.
-/

namespace PSTSEPPA
namespace ABO

namespace ClusterSpec

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {A : Finset ι}

/-- A proper-alphabet CLUSTER has exactly the same vertices
inside the generated subgroup Γ[A] and in the ambient Γ. -/
theorem localVertexSet_iff_ambient
    (gen : ι → Γ) (P : ClusterSpec A)
    (x : generatedSubgroup gen A) :
    x ∈ P.VertexSet (trivialCompletionGenerator gen A) ↔
      (x : Γ) ∈ P.VertexSet gen := by
  constructor
  · rintro ⟨C, hCP, hxC⟩
    exact ⟨C, hCP,
      (mem_localGeneratedSubgroup_iff_ambient
        gen C A (P.proper C hCP).subset x).mp hxC⟩
  · rintro ⟨C, hCP, hxC⟩
    exact ⟨C, hCP,
      (mem_localGeneratedSubgroup_iff_ambient
        gen C A (P.proper C hCP).subset x).mpr hxC⟩

/-- Signed CLUSTER edge membership is also exactly reflected
under the inclusion Γ[A]↪Γ, for every positive/negative label. -/
theorem localEdgeSet_iff_ambient
    (gen : ι → Γ) (P : ClusterSpec A)
    (x : generatedSubgroup gen A) (s : SignedLabel ι) :
    ((x, s) : ActionEdge (generatedSubgroup gen A) ι) ∈
        P.EdgeSet (trivialCompletionGenerator gen A) ↔
      (((x : Γ), s) : ActionEdge Γ ι) ∈ P.EdgeSet gen := by
  change
    (∃ C ∈ P.pieces,
      x ∈ generatedSubgroup (trivialCompletionGenerator gen A) C ∧
        signedBase s ∈ C) ↔
    (∃ C ∈ P.pieces,
      (x : Γ) ∈ generatedSubgroup gen C ∧ signedBase s ∈ C)
  constructor
  · rintro ⟨C, hCP, hxC, hsC⟩
    exact ⟨C, hCP,
      (mem_localGeneratedSubgroup_iff_ambient
        gen C A (P.proper C hCP).subset x).mp hxC, hsC⟩
  · rintro ⟨C, hCP, hxC, hsC⟩
    exact ⟨C, hCP,
      (mem_localGeneratedSubgroup_iff_ambient
        gen C A (P.proper C hCP).subset x).mpr hxC, hsC⟩

/-- An added full B-coset has precisely the same vertices
locally in Γ[A] and in ambient Γ, whenever B⊆A. -/
theorem localAugmentedVertexSet_iff_ambient
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v x : generatedSubgroup gen A) :
    x ∈ P.AugmentedVertexSet
        (trivialCompletionGenerator gen A) B v ↔
      (x : Γ) ∈ P.AugmentedVertexSet gen B (v : Γ) := by
  change
    (x ∈ P.VertexSet (trivialCompletionGenerator gen A) ∨
      x ∈ generatedLeftCoset (trivialCompletionGenerator gen A) B v) ↔
    ((x : Γ) ∈ P.VertexSet gen ∨
      (x : Γ) ∈ generatedLeftCoset gen B (v : Γ))
  constructor
  · rintro (hx | hx)
    · exact Or.inl ((P.localVertexSet_iff_ambient gen x).mp hx)
    · exact Or.inr
        ((mem_localGeneratedLeftCoset_iff_ambient
          gen B A hBA v x).mp hx)
  · rintro (hx | hx)
    · exact Or.inl ((P.localVertexSet_iff_ambient gen x).mpr hx)
    · exact Or.inr
        ((mem_localGeneratedLeftCoset_iff_ambient
          gen B A hBA v x).mpr hx)

/-- Full signed directed augmented-cluster edge membership
preserves and reflects the subgroup inclusion, including
all NEW B-coset edges as well as every OLD constituent edge. -/
theorem localAugmentedEdgeSet_iff_ambient
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v x : generatedSubgroup gen A) (s : SignedLabel ι) :
    ((x, s) : ActionEdge (generatedSubgroup gen A) ι) ∈
        P.AugmentedEdgeSet (trivialCompletionGenerator gen A) B v ↔
      (((x : Γ), s) : ActionEdge Γ ι) ∈
        P.AugmentedEdgeSet gen B (v : Γ) := by
  change
    ((∃ C ∈ P.pieces,
      x ∈ generatedSubgroup (trivialCompletionGenerator gen A) C ∧
        signedBase s ∈ C) ∨
      (x ∈ generatedLeftCoset
        (trivialCompletionGenerator gen A) B v ∧ signedBase s ∈ B)) ↔
    ((∃ C ∈ P.pieces,
      (x : Γ) ∈ generatedSubgroup gen C ∧ signedBase s ∈ C) ∨
      ((x : Γ) ∈ generatedLeftCoset gen B (v : Γ) ∧ signedBase s ∈ B))
  constructor
  · rintro (⟨C, hCP, hxC, hsC⟩ | ⟨hxB, hsB⟩)
    · exact Or.inl ⟨C, hCP,
        (mem_localGeneratedSubgroup_iff_ambient
          gen C A (P.proper C hCP).subset x).mp hxC, hsC⟩
    · exact Or.inr ⟨
        (mem_localGeneratedLeftCoset_iff_ambient
          gen B A hBA v x).mp hxB, hsB⟩
  · rintro (⟨C, hCP, hxC, hsC⟩ | ⟨hxB, hsB⟩)
    · exact Or.inl ⟨C, hCP,
        (mem_localGeneratedSubgroup_iff_ambient
          gen C A (P.proper C hCP).subset x).mpr hxC, hsC⟩
    · exact Or.inr ⟨
        (mem_localGeneratedLeftCoset_iff_ambient
          gen B A hBA v x).mpr hxB, hsB⟩

/-- Ambient augmented vertices cannot escape Γ[A]:
all old cluster constituents and the new B-coset lie
within the generated A-subgroup. -/
theorem augmentedVertex_mem_parentSubgroup
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : generatedSubgroup gen A) (x : Γ)
    (hx : x ∈ P.AugmentedVertexSet gen B (v : Γ)) :
    x ∈ generatedSubgroup gen A := by
  rcases hx with hOld | hNew
  · rcases hOld with ⟨C, hCP, hxC⟩
    exact generatedSubgroup_mono gen (P.proper C hCP).subset hxC
  · have hB : (v : Γ)⁻¹ * x ∈ generatedSubgroup gen B := hNew
    have hA : (v : Γ)⁻¹ * x ∈ generatedSubgroup gen A :=
      generatedSubgroup_mono gen hBA hB
    have hv : (v : Γ) ∈ generatedSubgroup gen A := v.2
    have hx' := (generatedSubgroup gen A).mul_mem hv hA
    have hxEq : (v : Γ) * ((v : Γ)⁻¹ * x) = x := by
      simp only [← mul_assoc, mul_inv_cancel, one_mul]
    rw [hxEq] at hx'
    exact hx'

end ClusterSpec
end ABO
end PSTSEPPA
