import PSTSEPPA.ABO.ProperClusterLocalSubgroupSignedIso
import PSTSEPPA.ABO.ClusterComponentGraph

/-!
# ABO Theorem 4.5: ROOT-TRANSLATED concrete proper B-clusters

The source proper B-cluster alternative is a LEFT TRANSLATE of
a union of actual generated proper-D subgroups and their
positive/negative signed oriented edge tokens. The already
certified H[C] inclusion theorem identifies the UNTRANSLATED
proper B-cluster in H[C] with its counterpart in Γ, assuming
B⊆C. The source's anchored old C-component requires an arbitrary
ROOT TRANSLATION g∈Γ before these groups can be compared.

We establish the literal source vertex and directed signed
edge membership iff, with original Γ coordinates x ↦ g*x,
at every g and parent subalphabet C. All ambient translated
cluster vertices/edge sources have a UNIQUE preimage in H[C].
This yields genuine dependent equivalences on the entire
root-translated proper cluster vertex and edge carriers,
including empty proper-cluster families, inverse signs,
trivial generators and geometric loops.

These are the carrier data for the actual labelled-graph
morphism to the source translated proper B-cluster; the
remaining incidence/edge-inversion naturality is separate.
No global retractability of Γ or collapse of old-component
tags by ambient Cayley coordinates is assumed.
-/

namespace PSTSEPPA
namespace ABO
namespace ClusterSpec

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {B : Finset ι}

/-- TRUE signed proper B-cluster vertex membership commutes with
the translation x ↦ g*x of the generated subgroup H[C] to Γ. -/
theorem localTranslatedVertex_parent_iff_ambient
    (gen : ι → Γ) (P : ClusterSpec B)
    (C : Finset ι) (hBC : B ⊆ C) (g : Γ)
    (x : generatedSubgroup gen C) :
    x ∈ P.VertexSet (trivialCompletionGenerator gen C) ↔
      g * (x : Γ) ∈
        ClusterSpec.LeftTranslateSet g (P.VertexSet gen) := by
  simpa [ClusterSpec.LeftTranslateSet, mul_assoc] using
    (P.localVertexSet_parent_iff_ambient gen C hBC x)

/-- Exact preservation and reflection of ACTUAL oriented signed
proper B-cluster edges, with arbitrary original ROOT translation
and no generated-group surjectivity assumption. -/
theorem localTranslatedEdge_parent_iff_ambient
    (gen : ι → Γ) (P : ClusterSpec B)
    (C : Finset ι) (hBC : B ⊆ C) (g : Γ)
    (x : generatedSubgroup gen C) (s : SignedLabel ι) :
    ((x, s) : ActionEdge (generatedSubgroup gen C) ι) ∈
      P.EdgeSet (trivialCompletionGenerator gen C) ↔
    ((g * (x : Γ), s) : ActionEdge Γ ι) ∈
      ClusterSpec.LeftTranslateEdgeSet g (P.EdgeSet gen) := by
  simpa [ClusterSpec.LeftTranslateEdgeSet, mul_assoc] using
    (P.localEdgeSet_parent_iff_ambient gen C hBC x s)

/-- Every source proper-cluster vertex in the translated
Γ cluster has a UNIQUE actual local H[C] group coordinate,
so the root-translation map is a genuine carrier EQUIVALENCE. -/
noncomputable def localTranslatedVertexEquivOfParent
    (gen : ι → Γ) (P : ClusterSpec B)
    (C : Finset ι) (hBC : B ⊆ C) (g : Γ) :
    P.Vertex (trivialCompletionGenerator gen C) ≃
      {y : Γ // y ∈ ClusterSpec.LeftTranslateSet g (P.VertexSet gen)} where
  toFun x :=
    ⟨g * (x.1 : Γ),
      (P.localTranslatedVertex_parent_iff_ambient
        gen C hBC g x.1).mp x.2⟩
  invFun y := by
    have hy : g⁻¹ * y.1 ∈ P.VertexSet gen := y.2
    let x : generatedSubgroup gen C :=
      ⟨g⁻¹ * y.1,
        P.vertex_mem_parentSubgroup gen C hBC _ hy⟩
    exact ⟨x,
      (P.localTranslatedVertex_parent_iff_ambient
        gen C hBC g x).mpr (by
        change g⁻¹ * (g * (x : Γ)) ∈ P.VertexSet gen
        simpa [x, mul_assoc] using hy)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    simp [mul_assoc]
  right_inv := by
    intro y
    apply Subtype.ext
    simp [mul_assoc]

/-- The SAME concrete root translation is an EQUIVALENCE of
all oriented signed edge-token carriers. This does not
replace an edge by an ambient Cayley edge which was absent
in the original proper cluster. -/
noncomputable def localTranslatedEdgeEquivOfParent
    (gen : ι → Γ) (P : ClusterSpec B)
    (C : Finset ι) (hBC : B ⊆ C) (g : Γ) :
    P.Edge (trivialCompletionGenerator gen C) ≃
      {e : ActionEdge Γ ι //
        e ∈ ClusterSpec.LeftTranslateEdgeSet g (P.EdgeSet gen)} where
  toFun e :=
    ⟨(g * (e.1.1 : Γ), e.1.2),
      (P.localTranslatedEdge_parent_iff_ambient
        gen C hBC g e.1.1 e.1.2).mp e.2⟩
  invFun e := by
    have he : (g⁻¹ * e.1.1, e.1.2) ∈ P.EdgeSet gen := e.2
    let x : generatedSubgroup gen C :=
      ⟨g⁻¹ * e.1.1,
        P.vertex_mem_parentSubgroup gen C hBC _
          (P.edge_source_mem gen he)⟩
    exact ⟨(x, e.1.2),
      (P.localTranslatedEdge_parent_iff_ambient
        gen C hBC g x e.1.2).mpr (by
          change (g⁻¹ * (g * (x : Γ)), e.1.2) ∈ P.EdgeSet gen
          simpa [x, mul_assoc] using he)⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simp [mul_assoc]
    · rfl
  right_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · simp [mul_assoc]
    · rfl

end ClusterSpec
end ABO
end PSTSEPPA
