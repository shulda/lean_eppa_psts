import PSTSEPPA.ABO.ComponentSubgraphAdmissibility

/-!
# ABO Theorem 4.5: flattening ACTUAL nested old signed components

The source forward induction applies itself recursively to
genuine D-components INSIDE genuine B-components of the ORIGINAL
incomplete Cayley skeleton. In order to reuse the original uniform
bridge-freeness hypothesis at all lower ranks, one needs to show that
those nested components are exactly the original D-components, not
new objects created by the nesting.

We prove the first two essential SOURCE facts for arbitrary
incomplete signed Γ-Cayley skeleton K and D⊆B:
(1) every ACTUAL signed D-path between vertices of a rooted B-component
    exists inside that same B-component iff it exists in K;
(2) the rooted D-component of that local B-component has EXACTLY the
    same Γ-valued old vertex set as the corresponding original rooted
    D-component in K.

This is not a statement about ambient D-coset equality. Every
membership witness uses actual old signed directed paths; missing
edges remain missing, formal inverses are preserved, and all
component tags remain intrinsic.

Still separate: literal edge-set equality of the nested D-component,
the signed-graph equivalence and its extension to FULL tagged
proper D-coset completions. Those are needed to propagate lower
bridgefreeness throughout the entire Theorem 4.5 rank induction.
No globally injective ambient Cayley map or additional axioms.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact realization of EVERY D-supported signed path in a rooted
B-component. The reverse implication lifts the ACTUAL path from K,
which remains in the B-component since D⊆B; no absent Cayley edge
is inserted. -/
theorem componentSubgraph_subalphabetReachable_iff
    (B D : Finset ι) (hDB : D ⊆ B) (root : K.Vertex)
    (x y : (K.subalphabetComponentSubgraph B root).Vertex) :
    (K.subalphabetComponentSubgraph B root).SubalphabetReachable D x y ↔
    K.SubalphabetReachable D
      ((K.subalphabetComponentSubgraphHom B root).onVertex x)
      ((K.subalphabetComponentSubgraphHom B root).onVertex y) := by
  constructor
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw, hp.map (K.subalphabetComponentSubgraphHom B root)⟩
  · intro hp
    let ix : K.Vertex :=
      (K.subalphabetComponentSubgraphHom B root).onVertex x
    let iy : K.Vertex :=
      (K.subalphabetComponentSubgraphHom B root).onVertex y
    have hRootX : K.SubalphabetReachable B root ix :=
      K.componentSubgraph_vertex_reachable B root x
    obtain ⟨hRootY, hLift⟩ :=
      K.reachable_lift_component B D hDB root ix iy hRootX hp
    have hX : K.componentLiftVertex B root ix hRootX = x := by
      apply Subtype.ext
      rfl
    have hY : K.componentLiftVertex B root iy hRootY = y := by
      apply Subtype.ext
      rfl
    simpa only [hX, hY] using hLift

/-- A D-component nested INSIDE the actual rooted B-component
has the exact same original Γ-valued vertex set as the rooted
D-component of the corresponding old K-vertex.

This is the precise first flattening step required to identify
nested components in the forward-induction hypotheses. -/
theorem nestedComponent_vertices_iff
    (B D : Finset ι) (hDB : D ⊆ B) (root : K.Vertex)
    (x : (K.subalphabetComponentSubgraph B root).Vertex)
    (v : Γ) :
    v ∈ ((K.subalphabetComponentSubgraph B root).subalphabetComponentSubgraph
        D x).vertices ↔
    v ∈ (K.subalphabetComponentSubgraph D
      ((K.subalphabetComponentSubgraphHom B root).onVertex x)).vertices := by
  constructor
  · rintro ⟨u, hu, hXu⟩
    refine ⟨(K.subalphabetComponentSubgraphHom B root).onVertex u, hu, ?_⟩
    exact (K.componentSubgraph_subalphabetReachable_iff
      B D hDB root x u).mp hXu
  · rintro ⟨u, hu, hXu⟩
    have hRootX : K.SubalphabetReachable B root
        ((K.subalphabetComponentSubgraphHom B root).onVertex x) :=
      K.componentSubgraph_vertex_reachable B root x
    have hRootU : K.SubalphabetReachable B root u :=
      K.subalphabetReachable_trans B hRootX
        (K.subalphabetReachable_mono D B hDB hXu)
    let y := K.componentLiftVertex B root u hRootU
    refine ⟨y, hu, ?_⟩
    apply (K.componentSubgraph_subalphabetReachable_iff
      B D hDB root x y).mpr
    change K.SubalphabetReachable D
      ((K.subalphabetComponentSubgraphHom B root).onVertex x)
      ((K.subalphabetComponentSubgraphHom B root).onVertex y)
    rw [K.subalphabetComponentSubgraphHom_liftVertex B root u hRootU]
    exact hXu

end CayleySubgraphSpec
end ABO
end PSTSEPPA
