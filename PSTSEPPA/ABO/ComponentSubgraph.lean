import PSTSEPPA.ABO.CayleySubgraphEdgeComponents
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# An intrinsic B-component as a literal Cayley subgraph

For B ⊆ A and a vertex v of an arbitrary incomplete A-skeleton K,
construct the induced B-labelled connected component as an actual
CayleySubgraphSpec over alphabet B.

Vertices are the group points reachable from v by realised B-paths
inside K. Edges are precisely the original B-labelled directed edge
tokens whose source lies in that component. Both formal inverse
tokens are retained, even for loops and repeated/trivial generators.

This is the canonical lower-rank skeleton needed for the exact version
of ABO Lemma 3.20. It embeds as a literal vertex/edge subgraph of K.
No ambient-coset equality is assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Literal B-component subgraph of K based at root, with the actual
B-labelled edge tokens inherited from K. -/
def subalphabetComponentSubgraph
    (B : Finset ι) (root : K.Vertex) :
    CayleySubgraphSpec gen B where
  vertices :=
    {x : Γ | ∃ u : K.Vertex,
      u.1 = x ∧ K.SubalphabetReachable B root u}
  edges :=
    {e : ActionEdge Γ ι | ∃ f : K.Edge,
      f.1 = e ∧ signedBase e.2 ∈ B ∧
        K.SubalphabetReachable B root ((K.toEGraph).source f)}
  source_mem := by
    intro e he
    rcases he with ⟨f, rfl, _hfB, href⟩
    exact ⟨(K.toEGraph).source f, rfl, href⟩
  inv_mem := by
    intro e he
    rcases he with ⟨f, rfl, hfB, href⟩
    refine ⟨(K.toEGraph).inv f, rfl, ?_, ?_⟩
    · change
        signedBase
          ((cayleyGraph gen).label ((cayleyGraph gen).inv f.1)) ∈ B
      rw [(cayleyGraph gen).label_inv_eq]
      simpa only [signedBase_inv] using hfB
    · exact K.subalphabetReachable_trans B
        href (K.edge_subalphabetReachable B f hfB)
  label_mem := by
    intro e he
    rcases he with ⟨f, rfl, hfB, _href⟩
    exact hfB

/-- Exactly the vertices of the intrinsic B-component are selected. -/
theorem mem_subalphabetComponentSubgraph_vertices
    (B : Finset ι) (root : K.Vertex) (x : Γ) :
    x ∈ (K.subalphabetComponentSubgraph B root).vertices ↔
      ∃ u : K.Vertex,
        u.1 = x ∧ K.SubalphabetReachable B root u :=
  Iff.rfl

/-- Exactly the inherited B-labelled original directed edge tokens
with source reachable from root are selected. -/
theorem mem_subalphabetComponentSubgraph_edges
    (B : Finset ι) (root : K.Vertex) (e : ActionEdge Γ ι) :
    e ∈ (K.subalphabetComponentSubgraph B root).edges ↔
      ∃ f : K.Edge,
        f.1 = e ∧ signedBase e.2 ∈ B ∧
        K.SubalphabetReachable B root ((K.toEGraph).source f) :=
  Iff.rfl

/-- Literal inclusion of the B-component graph into the parent
skeleton K. No choice of ambient coset representative is involved. -/
noncomputable def subalphabetComponentSubgraphHom
    (B : Finset ι) (root : K.Vertex) :
    LabelledGraphHom
      ((K.subalphabetComponentSubgraph B root).toEGraph).toLabelledGraph
      (K.toEGraph).toLabelledGraph where
  onVertex x :=
    ⟨x.1, by
      rcases x.2 with ⟨u, hu, _href⟩
      simpa only [← hu] using u.2⟩
  onEdge e :=
    ⟨e.1, by
      rcases e.2 with ⟨f, hf, _hfB, _href⟩
      simpa only [← hf] using f.2⟩
  map_source e := by
    apply Subtype.ext
    rfl
  map_inv e := by
    apply Subtype.ext
    rfl
  map_label e := rfl

/-- The literal B-component subgraph inclusion is vertex-injective. -/
theorem subalphabetComponentSubgraphHom_vertex_injective
    (B : Finset ι) (root : K.Vertex) :
    Function.Injective
      (K.subalphabetComponentSubgraphHom B root).onVertex := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg Subtype.val hxy

/-- The literal B-component subgraph inclusion is also injective on
formal directed edge tokens, including geometric loops. -/
theorem subalphabetComponentSubgraphHom_edge_injective
    (B : Finset ι) (root : K.Vertex) :
    Function.Injective
      (K.subalphabetComponentSubgraphHom B root).onEdge := by
  intro e f hef
  apply Subtype.ext
  exact congrArg Subtype.val hef

end CayleySubgraphSpec
end ABO
end PSTSEPPA
