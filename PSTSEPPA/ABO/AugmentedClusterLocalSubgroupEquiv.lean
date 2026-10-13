import PSTSEPPA.ABO.AugmentedClusterLocalSubgroupMembership

/-!
# Actual old+new vertex and oriented-edge equivalences for type-(1) stages

We now identify the genuinely ambient augmented cluster of Γ
with its local Γ[A] copy, for a cluster of proper A-subalphabets
and a B⊆A coset augmentation based in Γ[A].

The previous signed-membership theorems show that both local
vertex and signed oriented-edge records map into the ambient
structure, and that EVERY ambient vertex/edge of the augmented
cluster comes from the local subgroup. This builds honest
Bijections on the exact subtype vertex/edge carriers without
quotienting distinct points by arbitrary group coordinates.

A separate labelled-EGraph-isomorphism proof will check the
inverse edge/target operations and then the legal completion;
these equivalences are the required data-level foundations.
-/

namespace PSTSEPPA
namespace ABO

namespace ClusterSpec

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {A : Finset ι}

/-- Full old/new augmented-cluster vertex equivalence between
the actual Γ[A]-subgroup model and its original ambient Γ model.
The inclusion is injective AND surjective onto the real cluster,
because all proper constituents and the added B-coset lie in Γ[A]. -/
noncomputable def localAugmentedVertexEquiv
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : generatedSubgroup gen A) :
    P.AugmentedVertex (trivialCompletionGenerator gen A) B v ≃
      P.AugmentedVertex gen B (v : Γ) where
  toFun x :=
    ⟨(x.1 : Γ),
      (P.localAugmentedVertexSet_iff_ambient gen B hBA v x.1).mp x.2⟩
  invFun x :=
    ⟨(⟨x.1,
        P.augmentedVertex_mem_parentSubgroup
          gen B hBA v x.1 x.2⟩ : generatedSubgroup gen A),
      (P.localAugmentedVertexSet_iff_ambient
        gen B hBA v
        ⟨x.1, P.augmentedVertex_mem_parentSubgroup
          gen B hBA v x.1 x.2⟩).mpr x.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

/-- The local-to-original augmented vertex bijection is literally
the honest coordinate inclusion into Γ, not a choice of representative. -/
@[simp] theorem localAugmentedVertexEquiv_value
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : generatedSubgroup gen A)
    (x : P.AugmentedVertex (trivialCompletionGenerator gen A) B v) :
    ((P.localAugmentedVertexEquiv gen B hBA v x).1 : Γ) = x.1.1 := rfl

/-- The same exact equivalence for ORIGINAL oriented signed edge
TOKENS; both signs remain distinct, even for fixed-point loops.
The inverse sends an ambient edge back to its genuine source
in the parent-generated subgroup. -/
noncomputable def localAugmentedEdgeEquiv
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : generatedSubgroup gen A) :
    P.AugmentedEdge (trivialCompletionGenerator gen A) B v ≃
      P.AugmentedEdge gen B (v : Γ) where
  toFun e :=
    ⟨(((e.1.1 : Γ), e.1.2) : ActionEdge Γ ι),
      (P.localAugmentedEdgeSet_iff_ambient
        gen B hBA v e.1.1 e.1.2).mp e.2⟩
  invFun e :=
    let u : generatedSubgroup gen A :=
      ⟨e.1.1,
        P.augmentedVertex_mem_parentSubgroup
          gen B hBA v e.1.1
          (P.augmented_edge_source_mem gen B (v : Γ) e.2)⟩
    ⟨((u, e.1.2) : ActionEdge (generatedSubgroup gen A) ι),
      (P.localAugmentedEdgeSet_iff_ambient
        gen B hBA v u e.1.2).mpr e.2⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  right_inv := by
    intro e
    apply Subtype.ext
    rfl

/-- The true ambient signed edge token of a local augmented
cluster vertex/edge has the same signed label and source value. -/
@[simp] theorem localAugmentedEdgeEquiv_value
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : generatedSubgroup gen A)
    (e : P.AugmentedEdge (trivialCompletionGenerator gen A) B v) :
    (P.localAugmentedEdgeEquiv gen B hBA v e).1 =
      (((e.1.1 : Γ), e.1.2) : ActionEdge Γ ι) := rfl

end ClusterSpec
end ABO
end PSTSEPPA
