import PSTSEPPA.ABO.ComponentSubgraphConnected
import PSTSEPPA.ABO.SingleCosetEGraph
import PSTSEPPA.ABO.GraphHomInjectivity

/-!
# Full B-coset embedding of an intrinsic B-component (ABO Lemma 3.20)

Let L be the literal intrinsic B-connected component of a Cayley
skeleton K, regarded as a B-labelled CayleySubgraphSpec.

Since L is actually B-path-connected, it has precisely ONE intrinsic
B-component index. Consequently CE(G,L;B) attaches just one copy
of the corresponding ambient left B-coset, rather than multiple
component-tagged copies which might overlap in the ambient group.

The canonical labelled graph morphism CE(G,L;B) → Cayley(G)
is therefore injective on vertices and signed directed edge tokens.
Its vertex image lies in the left B-coset of the original root.
Further, all edges of CE(G,L;B) are its completed B-coset edges;
there are no old edges with labels outside B, since L itself is
a B-labelled subgraph.

This is the local full-coset embedding step in ABO Lemma 3.20.
No global injectivity of CE(G,K;P) → Cayley(G) is asserted.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every pair of vertices of the literal B-component subgraph
belongs to the same intrinsic B-component index. -/
theorem componentSubgraph_one_component
    (B : Finset ι) (root : K.Vertex)
    (x y : (K.subalphabetComponentSubgraph B root).Vertex) :
    (K.subalphabetComponentSubgraph B root).componentClass B x =
      (K.subalphabetComponentSubgraph B root).componentClass B y :=
  ((K.subalphabetComponentSubgraph B root).componentClass_eq_iff B x y).2
    (K.componentSubgraph_connected B root x y)

/-- All component tags in the single-B extension of the literal
B-component subgraph agree. This uses genuine B-path connectedness,
not accidental equality of ambient cosets. -/
theorem componentSubgraph_attached_index_unique
    (B : Finset ι) (root : K.Vertex)
    (p q :
      (K.subalphabetComponentSubgraph B root).AttachedCosetVertex B) :
    p.1 = q.1 := by
  induction p.1 using Quotient.inductionOn with
  | h x =>
    induction q.1 using Quotient.inductionOn with
    | h y =>
      exact K.componentSubgraph_one_component B root x y

/-- The canonical map from CE(G,L;B) to ambient Cayley(G)
is injective on vertices when L is a literal B-component of K.
Unlike the corresponding global map for K, it cannot identify
distinct component-tagged copies because L has only one copy. -/
theorem componentSubgraph_fullCosetAmbient_vertex_injective
    (B : Finset ι) (root : K.Vertex) :
    Function.Injective
      ((K.subalphabetComponentSubgraph B root).singleCosetAmbientHom B).onVertex := by
  intro p q hpq
  exact (K.subalphabetComponentSubgraph B root).attachedValue_injective_of_same_index
    B (K.componentSubgraph_attached_index_unique B root p q) hpq

/-- Injectivity on signed directed edge tokens follows as well,
including geometric loops and trivial generators. -/
theorem componentSubgraph_fullCosetAmbient_edge_injective
    (B : Finset ι) (root : K.Vertex) :
    Function.Injective
      ((K.subalphabetComponentSubgraph B root).singleCosetAmbientHom B).onEdge :=
  LabelledGraphHom.edge_injective_of_vertex_injective
    (G := (K.subalphabetComponentSubgraph B root).singleCosetEGraph B)
    ((K.subalphabetComponentSubgraph B root).singleCosetAmbientHom B)
    (K.componentSubgraph_fullCosetAmbient_vertex_injective B root)

/-- Every vertex in the full B-coset extension of the literal
B-component projects to the left B-coset of root in Γ. -/
theorem componentSubgraph_fullCosetAmbient_value_mem
    (B : Finset ι) (root : K.Vertex)
    (p :
      (K.subalphabetComponentSubgraph B root).AttachedCosetVertex B) :
    p.2.1 ∈ generatedLeftCoset gen B root.1 := by
  let L := K.subalphabetComponentSubgraph B root
  let r := K.componentSubgraphRoot B root
  have hidx : p.1 = L.componentClass B r := by
    let q : L.AttachedCosetVertex B := L.attachedOfSkeletonVertex B r
    exact K.componentSubgraph_attached_index_unique B root p q
  have hcoset :
      L.componentAmbientCoset B p.1 =
        generatedLeftCoset gen B root.1 := by
    calc
      L.componentAmbientCoset B p.1 =
          L.componentAmbientCoset B (L.componentClass B r) :=
        congrArg (L.componentAmbientCoset B) hidx
      _ = generatedLeftCoset gen B root.1 := rfl
  have hp : p.2.1 ∈ L.componentAmbientCoset B p.1 := p.2.2
  rw [hcoset] at hp
  exact hp

/-- The image of the completed B-extension is exactly the ambient
left B-coset of the root (on vertices). -/
theorem componentSubgraph_fullCosetAmbient_range
    (B : Finset ι) (root : K.Vertex) (g : Γ) :
    g ∈ generatedLeftCoset gen B root.1 ↔
      ∃ p :
        (K.subalphabetComponentSubgraph B root).AttachedCosetVertex B,
        ((K.subalphabetComponentSubgraph B root).singleCosetAmbientHom B).onVertex p = g := by
  let L := K.subalphabetComponentSubgraph B root
  let r := K.componentSubgraphRoot B root
  constructor
  · intro hg
    let p : L.AttachedCosetVertex B :=
      ⟨L.componentClass B r, ⟨g, by
        change g ∈ generatedLeftCoset gen B root.1
        exact hg⟩⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, hp⟩
    have hm := K.componentSubgraph_fullCosetAmbient_value_mem B root p
    change p.2.1 = g at hp
    rwa [hp] at hm

/-- Every directed edge in CE(G,L;B) is a completed B-coset
edge; there are no surviving old edges outside the alphabet of L. -/
theorem componentSubgraph_fullCosetEdges
    (B : Finset ι) (root : K.Vertex)
    (e : (K.subalphabetComponentSubgraph B root).SingleCosetEdge B) :
    ∃ (p : (K.subalphabetComponentSubgraph B root).AttachedCosetVertex B)
      (s : {s : SignedLabel ι // signedBase s ∈ B}),
      e = Sum.inr (p,s) := by
  let L := K.subalphabetComponentSubgraph B root
  cases e with
  | inl e =>
      have hB : signedBase e.1.1.2 ∈ B := L.label_mem e.1.1 e.1.2
      exact (e.2 hB).elim
  | inr e =>
      exact ⟨e.1, e.2, rfl⟩

/-- Every signed B-letter is available as an outgoing edge at
every vertex of the full coset extension of a B-component. -/
theorem componentSubgraph_fullCosetCompleteOnB
    (B : Finset ι) (root : K.Vertex)
    (p : (K.subalphabetComponentSubgraph B root).AttachedCosetVertex B)
    (s : SignedLabel ι) (hs : signedBase s ∈ B) :
    ∃ e : (K.subalphabetComponentSubgraph B root).SingleCosetEdge B,
      ((K.subalphabetComponentSubgraph B root).singleCosetEGraph B).source e = p ∧
      ((K.subalphabetComponentSubgraph B root).singleCosetEGraph B).label e = s := by
  refine ⟨Sum.inr (p, ⟨s, hs⟩), rfl, rfl⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
