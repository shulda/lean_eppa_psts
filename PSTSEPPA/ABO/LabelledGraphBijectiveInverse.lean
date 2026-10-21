import PSTSEPPA.ABO.Morphisms

/-!
# Inverses of actual signed labelled-graph isomorphisms

An isomorphism of our *incomplete*, deterministic signed graphs is
represented by a labelled-graph homomorphism bijective on both vertices
and actual oriented edge tokens. These are separate bijectivity
conditions: paths may contain original old edges, added edges, loops
and formal inverses, so a bijection on ambient Cayley coordinates
alone is insufficient.

The inverse below is itself a genuine labelled-graph morphism; it
preserves real sources, full signed labels, formal edge reversal and
therefore targets. This lets source-local rooted B-component graph
isomorphisms be reversed and composed with genuine signed cluster
isomorphisms in the final k-local ABO 4.5 transfer.
-/

namespace PSTSEPPA
namespace ABO

namespace LabelledGraphHom

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable {G : LabelledGraph V₁ E₁ ι}
variable {H : LabelledGraph V₂ E₂ ι}

/-- Invert a bijective labelled graph homomorphism on ACTUAL vertex and
oriented signed edge types (no completeness assumption). -/
noncomputable def inverseOfBijective
    (f : LabelledGraphHom G H)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge) :
    LabelledGraphHom H G := by
  let v : V₁ ≃ V₂ := Equiv.ofBijective f.onVertex hv
  let e : E₁ ≃ E₂ := Equiv.ofBijective f.onEdge he
  refine
    { onVertex := v.symm
      onEdge := e.symm
      map_source := ?_
      map_inv := ?_
      map_label := ?_ }
  · intro t
    apply v.injective
    calc
      v (G.source (e.symm t)) =
          H.source (f.onEdge (e.symm t)) := (f.map_source _).symm
      _ = H.source t := by
        rw [show f.onEdge (e.symm t) = t from e.apply_symm_apply t]
      _ = v (v.symm (H.source t)) := (v.apply_symm_apply _).symm
  · intro t
    apply e.injective
    calc
      e (e.symm (H.inv t)) = H.inv t := e.apply_symm_apply _
      _ = H.inv (f.onEdge (e.symm t)) := by
        rw [show f.onEdge (e.symm t) = t from e.apply_symm_apply t]
      _ = f.onEdge (G.inv (e.symm t)) := (f.map_inv _).symm
  · intro t
    calc
      G.label (e.symm t) =
          H.label (f.onEdge (e.symm t)) := (f.map_label _).symm
      _ = H.label t := by
        rw [show f.onEdge (e.symm t) = t from e.apply_symm_apply t]

/-- The inverse is bijective on both original vertices and ALL
actual positive/inverse edge classes. -/
theorem inverseOfBijective_bijective
    (f : LabelledGraphHom G H)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge) :
    Function.Bijective (f.inverseOfBijective hv he).onVertex ∧
    Function.Bijective (f.inverseOfBijective hv he).onEdge :=
  ⟨(Equiv.ofBijective f.onVertex hv).symm.bijective,
   (Equiv.ofBijective f.onEdge he).symm.bijective⟩

/-- Exact inverse on all labelled-graph vertices. -/
theorem inverseOfBijective_apply_vertex
    (f : LabelledGraphHom G H)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (x : V₁) :
    (f.inverseOfBijective hv he).onVertex (f.onVertex x) = x :=
  (Equiv.ofBijective f.onVertex hv).symm_apply_apply x

/-- Exact inverse on all original and completed oriented edge tokens. -/
theorem inverseOfBijective_apply_edge
    (f : LabelledGraphHom G H)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (a : E₁) :
    (f.inverseOfBijective hv he).onEdge (f.onEdge a) = a :=
  (Equiv.ofBijective f.onEdge he).symm_apply_apply a

end LabelledGraphHom
end ABO
end PSTSEPPA
