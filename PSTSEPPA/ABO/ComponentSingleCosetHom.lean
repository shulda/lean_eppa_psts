import PSTSEPPA.ABO.ComponentSubgraphIndices
import PSTSEPPA.ABO.SingleCosetSkeletonEmbedding
import PSTSEPPA.ABO.GraphHomInjectivity

/-!
# Embedding the single-C coset extension of a B-component into that of K

Let L be the literal B-component subgraph of K and let C⊆B.
Intrinsic C-components of L inject into those of K; the
corresponding attached C-coset points preserve their component tags
and ambient group coordinates.

This map extends to an actual labelled graph embedding
  CE(G,L;C) → CE(G,K;C).
A completed C-edge maps to the corresponding completed C-edge.
An original outside-C edge maps to the same signed original edge
in K. Formal reversal is respected, including at geometric loops.

The source E-graph is deterministic, so checked vertex
injectivity forces directed-edge injectivity. This supplies
the single-alphabet local functoriality needed for the lower
coset extension in ABO Lemma 3.20.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The attached C-coset map commutes with the completed signed
C-action, including trivial generators and loop edges. -/
theorem componentSubgraphAttachedMap_cosetStep
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex)
    (p :
      (K.subalphabetComponentSubgraph B root).AttachedCosetVertex C)
    (s : {s : SignedLabel ι // signedBase s ∈ C}) :
    K.componentSubgraphAttachedMap B C hCB root
        ((K.subalphabetComponentSubgraph B root).cosetStep C p s) =
      K.cosetStep C
        (K.componentSubgraphAttachedMap B C hCB root p) s := by
  apply K.attachedValue_injective_of_same_index C
  · rfl
  · rfl

/-- Map the signed edges of CE(G,L;C) to the corresponding edges
of CE(G,K;C), preserving their old/completed distinction. -/
noncomputable def componentSubgraphSingleCosetEdgeMap
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex) :
    (K.subalphabetComponentSubgraph B root).SingleCosetEdge C →
      K.SingleCosetEdge C
  | .inl e =>
      .inl
        ⟨(K.subalphabetComponentSubgraphHom B root).onEdge e.1,
          by
            change signedBase e.1.1.2 ∉ C
            exact e.2⟩
  | .inr e =>
      .inr (K.componentSubgraphAttachedMap B C hCB root e.1, e.2)

/-- Incidence of outgoing edges is preserved. -/
theorem componentSubgraphSingleCosetEdgeMap_source
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex)
    (e : (K.subalphabetComponentSubgraph B root).SingleCosetEdge C) :
    (K.singleCosetEGraph C).source
        (K.componentSubgraphSingleCosetEdgeMap B C hCB root e) =
      K.componentSubgraphAttachedMap B C hCB root
        (((K.subalphabetComponentSubgraph B root).singleCosetEGraph C).source e) := by
  cases e with
  | inl e =>
      change
        K.attachedOfSkeletonVertex C
          ((K.toEGraph).source
            ((K.subalphabetComponentSubgraphHom B root).onEdge e.1)) =
        K.componentSubgraphAttachedMap B C hCB root
          ((K.subalphabetComponentSubgraph B root).attachedOfSkeletonVertex C
            (((K.subalphabetComponentSubgraph B root).toEGraph).source e.1))
      rw [(K.subalphabetComponentSubgraphHom B root).map_source e.1]
      exact (K.componentSubgraphAttachedMap_skeleton B C hCB root
        (((K.subalphabetComponentSubgraph B root).toEGraph).source e.1)).symm
  | inr e =>
      rfl

/-- Signed labels are preserved by the local extension map. -/
theorem componentSubgraphSingleCosetEdgeMap_label
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex)
    (e : (K.subalphabetComponentSubgraph B root).SingleCosetEdge C) :
    (K.singleCosetEGraph C).label
        (K.componentSubgraphSingleCosetEdgeMap B C hCB root e) =
      ((K.subalphabetComponentSubgraph B root).singleCosetEGraph C).label e := by
  cases e with
  | inl e =>
      exact (K.subalphabetComponentSubgraphHom B root).map_label e.1
  | inr e =>
      rfl

/-- The local embedding respects literal formal edge reversal. -/
theorem componentSubgraphSingleCosetEdgeMap_inv
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex)
    (e : (K.subalphabetComponentSubgraph B root).SingleCosetEdge C) :
    K.componentSubgraphSingleCosetEdgeMap B C hCB root
        (((K.subalphabetComponentSubgraph B root).singleCosetEGraph C).inv e) =
      (K.singleCosetEGraph C).inv
        (K.componentSubgraphSingleCosetEdgeMap B C hCB root e) := by
  cases e with
  | inl e =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact (K.subalphabetComponentSubgraphHom B root).map_inv e.1
  | inr e =>
      apply congrArg Sum.inr
      apply Prod.ext
      · exact K.componentSubgraphAttachedMap_cosetStep B C hCB root e.1 e.2
      · apply Subtype.ext
        rfl

/-- Full labelled graph morphism on the single-C coset extensions. -/
noncomputable def componentSubgraphSingleCosetHom
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex) :
    LabelledGraphHom
      ((K.subalphabetComponentSubgraph B root).singleCosetEGraph C).toLabelledGraph
      (K.singleCosetEGraph C).toLabelledGraph where
  onVertex := K.componentSubgraphAttachedMap B C hCB root
  onEdge := K.componentSubgraphSingleCosetEdgeMap B C hCB root
  map_source e := K.componentSubgraphSingleCosetEdgeMap_source B C hCB root e
  map_inv e := K.componentSubgraphSingleCosetEdgeMap_inv B C hCB root e
  map_label e := K.componentSubgraphSingleCosetEdgeMap_label B C hCB root e

/-- Local component inclusion embeds every tagged C-coset vertex. -/
theorem componentSubgraphSingleCosetHom_vertex_injective
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex) :
    Function.Injective
      (K.componentSubgraphSingleCosetHom B C hCB root).onVertex :=
  K.componentSubgraphAttachedMap_injective B C hCB root

/-- It also embeds every signed directed C-edge token. -/
theorem componentSubgraphSingleCosetHom_edge_injective
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex) :
    Function.Injective
      (K.componentSubgraphSingleCosetHom B C hCB root).onEdge :=
  LabelledGraphHom.edge_injective_of_vertex_injective
    (K.componentSubgraphSingleCosetHom B C hCB root)
    (K.componentSubgraphSingleCosetHom_vertex_injective B C hCB root)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
