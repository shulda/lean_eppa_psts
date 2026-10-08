import PSTSEPPA.ABO.ComponentSubgraphPaths

/-!
# Genuine B-connectivity of the intrinsic B-component subgraph

The literal B-component subgraph of an incomplete Cayley skeleton is
connected *by realised B-labelled paths*, not just because its ambient
group vertices lie in one left B-coset.

Every vertex in the selected component comes with an actual B-path
from the root in the parent skeleton. Path reflection yields an
actual path inside the constructed B-component subgraph.

Consequently every two vertices of that subgraph are joined by
an actual B-path. This certifies the connectedness hypothesis
needed when reusing the lower B-component as a skeleton in
ABO Lemma 3.20.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The distinguished root as an actual vertex in its intrinsic
B-component subgraph. -/
def componentSubgraphRoot
    (B : Finset ι) (root : K.Vertex) :
    (K.subalphabetComponentSubgraph B root).Vertex :=
  K.componentLiftVertex B root root (K.subalphabetReachable_refl B root)

/-- Every vertex in the literal B-component is reachable from its
distinguished root by an actual B-path *inside the component*. -/
theorem componentSubgraph_reachable_from_root
    (B : Finset ι) (root : K.Vertex)
    (x : (K.subalphabetComponentSubgraph B root).Vertex) :
    (K.subalphabetComponentSubgraph B root).SubalphabetReachable
      B (K.componentSubgraphRoot B root) x := by
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨u, rfl, hu⟩
  obtain ⟨hu', hpath⟩ :=
    K.reachable_lift_component B B (Finset.Subset.rfl)
      root root u (K.subalphabetReachable_refl B root) hu
  change
    (K.subalphabetComponentSubgraph B root).SubalphabetReachable
      B (K.componentLiftVertex B root root
          (K.subalphabetReachable_refl B root))
      (⟨u.1, ⟨u, rfl, hu⟩⟩ :
        (K.subalphabetComponentSubgraph B root).Vertex)
  have htarget :
      K.componentLiftVertex B root u hu' =
        (⟨u.1, ⟨u, rfl, hu⟩⟩ :
          (K.subalphabetComponentSubgraph B root).Vertex) := by
    apply Subtype.ext
    rfl
  rw [htarget] at hpath
  exact hpath

/-- The literal B-component subgraph is B-path-connected:
every pair of its vertices is joined by an actual B-labelled word. -/
theorem componentSubgraph_connected
    (B : Finset ι) (root : K.Vertex)
    (x y : (K.subalphabetComponentSubgraph B root).Vertex) :
    (K.subalphabetComponentSubgraph B root).SubalphabetReachable
      B x y := by
  have hx :=
    K.componentSubgraph_reachable_from_root B root x
  have hy :=
    K.componentSubgraph_reachable_from_root B root y
  exact (K.subalphabetComponentSubgraph B root).subalphabetReachable_trans
    B
    ((K.subalphabetComponentSubgraph B root).subalphabetReachable_symm B hx)
    hy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
