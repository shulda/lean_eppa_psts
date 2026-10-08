import PSTSEPPA.ABO.Graph

/-!
# Morphisms of ABO labelled graphs

A labelled graph morphism maps vertices and directed edge tokens, preserving
source, formal edge reversal, and labels.  Target preservation is then forced.
For E-graphs, such morphisms preserve all labelled paths; between complete
E-graphs they commute with the canonical word-following operation.
-/

namespace PSTSEPPA
namespace ABO

/-- Morphism of labelled graphs. -/
structure LabelledGraphHom
    {V₁ E₁ V₂ E₂ ι : Type*}
    (G : LabelledGraph V₁ E₁ ι)
    (H : LabelledGraph V₂ E₂ ι) where
  onVertex : V₁ → V₂
  onEdge : E₁ → E₂
  map_source : ∀ e, H.source (onEdge e) = onVertex (G.source e)
  map_inv : ∀ e, onEdge (G.inv e) = H.inv (onEdge e)
  map_label : ∀ e, H.label (onEdge e) = G.label e

namespace LabelledGraphHom

variable
  {V₁ E₁ V₂ E₂ V₃ E₃ ι : Type*}
  {G : LabelledGraph V₁ E₁ ι}
  {H : LabelledGraph V₂ E₂ ι}
  {K : LabelledGraph V₃ E₃ ι}

/-- Target preservation follows from source preservation and compatibility
with formal edge reversal. -/
theorem map_target (f : LabelledGraphHom G H) (e : E₁) :
    H.target (f.onEdge e) = f.onVertex (G.target e) := by
  calc
    H.target (f.onEdge e) = H.source (H.inv (f.onEdge e)) := rfl
    _ = H.source (f.onEdge (G.inv e)) := by rw [← f.map_inv e]
    _ = f.onVertex (G.source (G.inv e)) := f.map_source _
    _ = f.onVertex (G.target e) := rfl

/-- Identity labelled graph morphism. -/
def id (G : LabelledGraph V₁ E₁ ι) :
    LabelledGraphHom G G where
  onVertex := fun x => x
  onEdge := fun e => e
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

/-- Composition of labelled graph morphisms. -/
def comp (g : LabelledGraphHom H K) (f : LabelledGraphHom G H) :
    LabelledGraphHom G K where
  onVertex := g.onVertex ∘ f.onVertex
  onEdge := g.onEdge ∘ f.onEdge
  map_source e := by
    change K.source (g.onEdge (f.onEdge e)) =
      g.onVertex (f.onVertex (G.source e))
    rw [g.map_source, f.map_source]
  map_inv e := by
    change g.onEdge (f.onEdge (G.inv e)) =
      K.inv (g.onEdge (f.onEdge e))
    rw [f.map_inv, g.map_inv]
  map_label e := by
    change K.label (g.onEdge (f.onEdge e)) = G.label e
    rw [g.map_label, f.map_label]

@[simp]
theorem id_onVertex (x : V₁) :
    (LabelledGraphHom.id G).onVertex x = x :=
  rfl

@[simp]
theorem id_onEdge (e : E₁) :
    (LabelledGraphHom.id G).onEdge e = e :=
  rfl

end LabelledGraphHom

namespace EGraph

variable
  {V₁ E₁ V₂ E₂ ι : Type*}
  {G : EGraph V₁ E₁ ι}
  {H : EGraph V₂ E₂ ι}

/-- A labelled graph morphism preserves every realised labelled path. -/
theorem Follows.map
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    {u v : V₁} {w : LabelWord ι}
    (h : G.Follows u w v) :
    H.Follows (f.onVertex u) w (f.onVertex v) := by
  induction h with
  | nil u =>
      exact Follows.nil _
  | @cons u v s w e hs hl hrest ih =>
      refine Follows.cons (f.onEdge e) ?_ ?_ ?_
      · exact (f.map_source e).trans (congrArg f.onVertex hs)
      · exact (f.map_label e).trans hl
      · change H.Follows (f.onVertex (G.target e)) w (f.onVertex v)
        exact ih

end EGraph

namespace CompleteEGraph

variable
  {V₁ E₁ V₂ E₂ ι : Type*}
  (G : CompleteEGraph V₁ E₁ ι)
  (H : CompleteEGraph V₂ E₂ ι)

/-- Between complete E-graphs, a labelled morphism sends the selected outgoing
edge to the selected outgoing edge with the same label. -/
theorem hom_edgeAt
    (f : LabelledGraphHom
      G.toEGraph.toLabelledGraph H.toEGraph.toLabelledGraph)
    (u : V₁) (s : SignedLabel ι) :
    H.edgeAt (f.onVertex u) s = f.onEdge (G.edgeAt u s) := by
  apply H.edgeAt_eq
  · exact (f.map_source _).trans (congrArg f.onVertex (G.edgeAt_source u s))
  · exact (f.map_label _).trans (G.edgeAt_label u s)

/-- Word following is natural with respect to labelled morphisms of complete
E-graphs. -/
theorem hom_followWord
    (f : LabelledGraphHom
      G.toEGraph.toLabelledGraph H.toEGraph.toLabelledGraph)
    (u : V₁) (w : LabelWord ι) :
    H.followWord (f.onVertex u) w =
      f.onVertex (G.followWord u w) := by
  have hMapped :
      H.toEGraph.Follows (f.onVertex u) w
        (f.onVertex (G.followWord u w)) :=
    (G.follows_followWord u w).map f
  have hCanonical :
      H.toEGraph.Follows (f.onVertex u) w
        (H.followWord (f.onVertex u) w) :=
    H.follows_followWord _ _
  exact H.toEGraph.follows_right_unique hCanonical hMapped

end CompleteEGraph

end ABO
end PSTSEPPA
