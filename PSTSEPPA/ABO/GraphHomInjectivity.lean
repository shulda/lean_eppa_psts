import PSTSEPPA.ABO.Morphisms

/-!
# Injectivity of labelled E-graph morphisms

For deterministic source E-graphs, a label-preserving graph morphism
which is injective on vertices is automatically injective on directed
edge tokens. This includes geometric loops: formal edge inverses
remain two distinct tokens because their signed labels are inverse.

We use this as a reusable embedding principle for lower coset
extensions, rather than separately unfolding each edge quotient.
-/

namespace PSTSEPPA
namespace ABO

namespace LabelledGraphHom

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable {G : EGraph V₁ E₁ ι} {H : LabelledGraph V₂ E₂ ι}

/-- Injectivity on vertices forces injectivity on actual signed
edge tokens whenever the source E-graph is deterministic. -/
theorem edge_injective_of_vertex_injective
    (f : LabelledGraphHom G.toLabelledGraph H)
    (hv : Function.Injective f.onVertex) :
    Function.Injective f.onEdge := by
  intro e e' he
  apply G.deterministic
  · apply hv
    calc
      f.onVertex (G.source e) = H.source (f.onEdge e) :=
        (f.map_source e).symm
      _ = H.source (f.onEdge e') := by rw [he]
      _ = f.onVertex (G.source e') := f.map_source e'
  · calc
      G.label e = H.label (f.onEdge e) :=
        (f.map_label e).symm
      _ = H.label (f.onEdge e') := by rw [he]
      _ = G.label e' := f.map_label e'

/-- A labelled morphism out of a deterministic E-graph embeds all
vertex and signed-edge tokens as soon as it embeds vertices. -/
theorem bijective_on_image_of_vertex_injective
    (f : LabelledGraphHom G.toLabelledGraph H)
    (hv : Function.Injective f.onVertex) :
    Function.Injective f.onVertex ∧ Function.Injective f.onEdge :=
  ⟨hv, f.edge_injective_of_vertex_injective hv⟩

end LabelledGraphHom
end ABO
end PSTSEPPA
