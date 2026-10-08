import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Signed skeleton edges and intrinsic subalphabet components

An actual edge whose signed label belongs to B witnesses a B-path from its
source to its target, so those vertices lie in the same intrinsic B-component.
The result holds in non-complete skeletons and with trivial generators;
formal inverse edge tokens are respected automatically.

This is used to embed the original skeleton into the single-B coset extension
without silently replacing intrinsic components by ambient B-cosets.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every directed skeleton edge labelled in B is a realised B-path. -/
theorem edge_subalphabetReachable
    (B : Finset ι) (e : K.Edge)
    (he : signedBase ((K.toEGraph).label e) ∈ B) :
    K.SubalphabetReachable B ((K.toEGraph).source e)
      ((K.toEGraph).target e) := by
  refine ⟨[(K.toEGraph).label e], ?_, ?_⟩
  · exact ⟨he, trivial⟩
  · exact EGraph.Follows.cons e rfl rfl (EGraph.Follows.nil _)

/-- Consequently every B-labelled skeleton edge stays in one intrinsic
B-component, rather than merely a common ambient B-coset. -/
theorem componentClass_source_eq_target
    (B : Finset ι) (e : K.Edge)
    (he : signedBase ((K.toEGraph).label e) ∈ B) :
    K.componentClass B ((K.toEGraph).source e) =
      K.componentClass B ((K.toEGraph).target e) := by
  apply (K.componentClass_eq_iff B _ _).2
  exact K.edge_subalphabetReachable B e he

/-- In particular, the two endpoints of a B-edge lie in the same tagged
ambient B-coset copy. -/
theorem edge_endpoint_mem_componentAmbientCoset
    (B : Finset ι) (e : K.Edge)
    (he : signedBase ((K.toEGraph).label e) ∈ B) :
    ((K.toEGraph).target e).1 ∈
      K.componentAmbientCoset B
        (K.componentClass B ((K.toEGraph).source e)) := by
  have hreach := K.edge_subalphabetReachable B e he
  change
    ((K.toEGraph).target e).1 ∈
      generatedLeftCoset gen B ((K.toEGraph).source e).1
  exact K.subalphabetReachable_implies_coset B _ _ hreach

end CayleySubgraphSpec

end ABO
end PSTSEPPA
