import PSTSEPPA.ABO.NestedComponentFlattening

/-!
# ABO Theorem 4.5: flatten the ACTUAL signed old edge tokens of nested components

The first flattening theorem showed that a true D-component
INSIDE a true rooted B-component has the very same Γ-vertex set
as the original D-component, for D⊆B.

Here we prove the missing FULL directed SIGNED EDGE comparison.
The nested D-component includes precisely the ORIGINAL D-labelled
edges whose true source lies in the original rooted D-component:
no additional old edges, no ambient coset completion, and no
identification of different original component tags.

Both directions use literal signed directed edge tokens and
original D-word paths; the converse invokes actual lifting of
the edge and its D-source path into the rooted B-component.

Therefore the two nested component Cayley subgraphs agree on
BOTH vertex and directed signed edge sets. This is the main
old-skeleton structural ingredient for comparing the nested
proper-D-coset extensions in source Theorem 4.5.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The directed signed edge set of a D-component nested inside
a rooted B-component is literally the same as that of the true
rooted ORIGINAL D-component. Every edge on each side is an
actual original old token; both formal inverse directions
remain distinct even for loops and repeated generators. -/
theorem nestedComponent_edges_iff
    (B D : Finset ι) (hDB : D ⊆ B) (root : K.Vertex)
    (x : (K.subalphabetComponentSubgraph B root).Vertex)
    (e : ActionEdge Γ ι) :
    e ∈ ((K.subalphabetComponentSubgraph B root).subalphabetComponentSubgraph
        D x).edges ↔
    e ∈ (K.subalphabetComponentSubgraph D
      ((K.subalphabetComponentSubgraphHom B root).onVertex x)).edges := by
  let L := K.subalphabetComponentSubgraph B root
  let f := K.subalphabetComponentSubgraphHom B root
  constructor
  · rintro ⟨t, ht, heD, hLocalReach⟩
    let tK : K.Edge := f.onEdge t
    have hSource :
        f.onVertex ((L.toEGraph).source t) =
          (K.toEGraph).source tK :=
      f.map_source t
    have hParentReach : K.SubalphabetReachable D
        (f.onVertex x) ((K.toEGraph).source tK) := by
      have hp :=
        (K.componentSubgraph_subalphabetReachable_iff
          B D hDB root x ((L.toEGraph).source t)).mp hLocalReach
      rw [hSource] at hp
      exact hp
    exact ⟨tK, ht, heD, hParentReach⟩
  · rintro ⟨tK, ht, heD, hParentReach⟩
    have hRootX : K.SubalphabetReachable B root (f.onVertex x) :=
      K.componentSubgraph_vertex_reachable B root x
    have hRootSrc :
        K.SubalphabetReachable B root ((K.toEGraph).source tK) :=
      K.subalphabetReachable_trans B hRootX
        (K.subalphabetReachable_mono D B hDB hParentReach)
    let tL : L.Edge :=
      K.componentLiftEdge B root tK (hDB heD) hRootSrc
    have hSource :
        (L.toEGraph).source tL =
          K.componentLiftVertex B root
            ((K.toEGraph).source tK) hRootSrc := by
      apply Subtype.ext
      rfl
    have hLocalReach : L.SubalphabetReachable D x
        ((L.toEGraph).source tL) := by
      rw [hSource]
      apply (K.componentSubgraph_subalphabetReachable_iff
        B D hDB root x
          (K.componentLiftVertex B root
            ((K.toEGraph).source tK) hRootSrc)).mpr
      rw [K.subalphabetComponentSubgraphHom_liftVertex
        B root ((K.toEGraph).source tK) hRootSrc]
      exact hParentReach
    exact ⟨tL, ht, heD, hLocalReach⟩

/-- Literal equality of BOTH old vertex and directed signed edge
sets for actual nested D⊆B-components versus the corresponding
original rooted D-component. This is precisely the source
component-flattening identity needed for the forward induction. -/
theorem nestedComponent_vertex_edge_sets
    (B D : Finset ι) (hDB : D ⊆ B) (root : K.Vertex)
    (x : (K.subalphabetComponentSubgraph B root).Vertex) :
    ((K.subalphabetComponentSubgraph B root).subalphabetComponentSubgraph
        D x).vertices =
      (K.subalphabetComponentSubgraph D
        ((K.subalphabetComponentSubgraphHom B root).onVertex x)).vertices ∧
    ((K.subalphabetComponentSubgraph B root).subalphabetComponentSubgraph
        D x).edges =
      (K.subalphabetComponentSubgraph D
        ((K.subalphabetComponentSubgraphHom B root).onVertex x)).edges := by
  constructor
  · ext v
    exact K.nestedComponent_vertices_iff B D hDB root x v
  · ext e
    exact K.nestedComponent_edges_iff B D hDB root x e

end CayleySubgraphSpec
end ABO
end PSTSEPPA
