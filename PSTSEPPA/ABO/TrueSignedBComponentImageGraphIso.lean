import PSTSEPPA.ABO.CosetConnectivity
import PSTSEPPA.ABO.Morphisms

/-!
# Genuine oriented signed B-component image as a labelled graph

ABO Lemma 4.3 concludes with an isomorphism of true labelled
graphs, not merely a coincidence of Cayley vertex sets.
This file provides the generic, source-faithful graph mechanism.

For ANY original deterministic signed EGraph G, alphabet B
and original vertex anchor, we form the ACTUAL subgraph:
  vertices: endpoints reachable by a REAL signed B-word;
  edges: ORIGINAL oriented signed B-edge tokens whose
         ACTUAL source is B-reachable from anchor.

We prove this is a true signed EGraph: it is closed under
formal inversion (including two signed tokens of a geometric
loop) because every realised B-edge stays in the chosen
intrinsic B-component. No missing original edges are added.

For any ACTUAL labelled morphism F:G→H into another EGraph,
construct the corresponding image graph whose vertices and
oriented signed edges are EXACTLY the image of the above
true B-component, with all incidence/reversal/label relations
inherited from H. There is a canonical labelled morphism
from the original component to this image graph.

If F is injective ON THAT ORIGINAL COMPONENT'S vertices
and original B-edge tokens (not necessarily globally),
then this morphism is bijective on BOTH vertex and signed
edge types. Hence the two genuine labelled graphs are
isomorphic in the graph-morphism sense used in the paper.

This generic statement is the exact final interface for
the independently checked ABO-specific source facts:
  - #743 true component ambient vertex faithfulness;
  - #746 true component ambient vertex image equality;
  - #749 true original oriented signed edge image equality;
  - #751 true component oriented signed edge faithfulness.

It makes no global Cayley embedding claim, no cluster
shape hypothesis, and no extra old-edge completion.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V E W F ι : Type*} [Fintype ι] [DecidableEq ι]

/-- TRUE original signed B-path-component vertex set. -/
def BComponentVertexSet
    (G : EGraph V E ι) (B : Finset ι) (anchor : V) : Set V :=
  {v | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
    G.Follows anchor w v}

/-- TRUE original oriented signed B-edge tokens whose actual
source belongs to the original B-path-component. -/
def BComponentEdgeSet
    (G : EGraph V E ι) (B : Finset ι) (anchor : V) : Set E :=
  {e | signedBase (G.label e) ∈ B ∧
    G.source e ∈ G.BComponentVertexSet B anchor}

/-- The terminal vertex of each TRUE B-labelled original edge
starting inside the B-component is also B-reachable in the
ORIGINAL EGraph, by appending that real signed edge. -/
theorem BComponentEdge_target_mem
    (G : EGraph V E ι) (B : Finset ι) (anchor : V)
    (e : E) (he : e ∈ G.BComponentEdgeSet B anchor) :
    G.target e ∈ G.BComponentVertexSet B anchor := by
  obtain ⟨hl, w, hw, hp⟩ := he
  refine ⟨w ++ [G.label e], ?_, ?_⟩
  · exact (LabelWord.uses_append B _ _).mpr
      ⟨hw, ⟨hl, trivial⟩⟩
  · exact G.follows_append hp
      (EGraph.Follows.cons e rfl rfl
        (EGraph.Follows.nil (G.target e)))

/-- TRUE B-edge-token membership survives FORMAL signed inversion,
using the original target-in-component lemma and the fact that
the inverse signed letter has the SAME underlying base letter. -/
theorem BComponentEdge_inv_mem
    (G : EGraph V E ι) (B : Finset ι) (anchor : V)
    (e : E) (he : e ∈ G.BComponentEdgeSet B anchor) :
    G.inv e ∈ G.BComponentEdgeSet B anchor := by
  constructor
  · have hBase :
        signedBase (G.label (G.inv e)) =
          signedBase (G.label e) := by
      rw [G.label_inv e]
      cases h : G.label e with
      | pos i => rfl
      | neg i => rfl
    rw [hBase]
    exact he.1
  · change G.target e ∈ G.BComponentVertexSet B anchor
    exact G.BComponentEdge_target_mem B anchor e he

/-- The literal genuine ORIGINAL signed EGraph of one B-component,
with exactly the real oriented edges and inverse edge tokens.
Neither the artificial later trivial completion nor arbitrary
ambient Cayley edges occur. -/
noncomputable def BComponentEGraph
    (G : EGraph V E ι) (B : Finset ι) (anchor : V) :
    EGraph
      {v : V // v ∈ G.BComponentVertexSet B anchor}
      {e : E // e ∈ G.BComponentEdgeSet B anchor} ι where
  toLabelledGraph := {
    source e := ⟨G.source e.1, e.2.2⟩
    inv e := ⟨G.inv e.1,
      G.BComponentEdge_inv_mem B anchor e.1 e.2⟩
    inv_inv e := by
      apply Subtype.ext
      exact G.inv_inv e.1
    inv_ne e h := by
      apply G.inv_ne e.1
      exact congrArg Subtype.val h
    label e := G.label e.1
    label_inv e := G.label_inv e.1
  }
  deterministic := by
    intro e f hs hl
    apply Subtype.ext
    exact G.deterministic (congrArg Subtype.val hs) hl

/-- Literal ambient IMAGE of true original B-component vertices
under any source-preserving signed labelled morphism. -/
def BComponentImageVertexSet
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (B : Finset ι) (anchor : V) : Set W :=
  {w | ∃ v : V, v ∈ G.BComponentVertexSet B anchor ∧
    f.onVertex v = w}

/-- Literal ambient IMAGE of true ORIGINAL oriented signed
B-edge tokens under the same labelled morphism. -/
def BComponentImageEdgeSet
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (B : Finset ι) (anchor : V) : Set F :=
  {d | ∃ e : E, e ∈ G.BComponentEdgeSet B anchor ∧
    f.onEdge e = d}

/-- The actual signed B-component image VERTEX and EDGE sets
form a genuine target signed EGraph under an arbitrary
labelled morphism, even without injectivity. -/
noncomputable def BComponentImageEGraph
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (B : Finset ι) (anchor : V) :
    EGraph
      {w : W // w ∈ G.BComponentImageVertexSet H f B anchor}
      {d : F // d ∈ G.BComponentImageEdgeSet H f B anchor} ι where
  toLabelledGraph := {
    source d := ⟨H.source d.1, by
      obtain ⟨e, he, hd⟩ := d.2
      refine ⟨G.source e, he.2, ?_⟩
      calc
        f.onVertex (G.source e) = H.source (f.onEdge e) :=
          (f.map_source e).symm
        _ = H.source d.1 := congrArg H.source hd⟩
    inv d := ⟨H.inv d.1, by
      obtain ⟨e, he, hd⟩ := d.2
      refine ⟨G.inv e,
        G.BComponentEdge_inv_mem B anchor e he, ?_⟩
      calc
        f.onEdge (G.inv e) = H.inv (f.onEdge e) :=
          f.map_inv e
        _ = H.inv d.1 := congrArg H.inv hd⟩
    inv_inv d := by
      apply Subtype.ext
      exact H.inv_inv d.1
    inv_ne d h := by
      apply H.inv_ne d.1
      exact congrArg Subtype.val h
    label d := H.label d.1
    label_inv d := H.label_inv d.1
  }
  deterministic := by
    intro d e hs hl
    apply Subtype.ext
    exact H.deterministic (congrArg Subtype.val hs) hl

/-- The canonical TRUE signed labelled graph morphism
from the ORIGINAL B-component to its target image.
The two maps are literal restrictions of the original
vertex and original oriented-edge maps of f. -/
noncomputable def BComponentImageHom
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (B : Finset ι) (anchor : V) :
    LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      (G.BComponentImageEGraph H f B anchor).toLabelledGraph where
  onVertex v := ⟨f.onVertex v.1, ⟨v.1, v.2, rfl⟩⟩
  onEdge e := ⟨f.onEdge e.1, ⟨e.1, e.2, rfl⟩⟩
  map_source e := by
    apply Subtype.ext
    exact f.map_source e.1
  map_inv e := by
    apply Subtype.ext
    exact f.map_inv e.1
  map_label e := f.map_label e.1

/-- Generic TRUE signed graph-isomorphism criterion:
a labelled morphism injective on the REAL vertices and
REAL oriented B-edge tokens of one original B-component
is automatically BIJECTIVE onto its genuine signed image
graph. This does NOT require injectivity anywhere else.

All original incidence/reversal/signed-label equations
are part of the canonical `BComponentImageHom` itself. -/
theorem BComponentImageHom_bijective
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (B : Finset ι) (anchor : V)
    (hv : Set.InjOn f.onVertex (G.BComponentVertexSet B anchor))
    (he : Set.InjOn f.onEdge (G.BComponentEdgeSet B anchor)) :
    Function.Bijective
      (G.BComponentImageHom H f B anchor).onVertex ∧
    Function.Bijective
      (G.BComponentImageHom H f B anchor).onEdge := by
  constructor
  · constructor
    · intro x y hxy
      apply Subtype.ext
      exact hv x.2 y.2 (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, hxy⟩ := y.2
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
  · constructor
    · intro x y hxy
      apply Subtype.ext
      exact he x.2 y.2 (congrArg Subtype.val hxy)
    · intro d
      obtain ⟨e, he', hed⟩ := d.2
      refine ⟨⟨e, he'⟩, ?_⟩
      apply Subtype.ext
      exact hed

end EGraph
end ABO
end PSTSEPPA
