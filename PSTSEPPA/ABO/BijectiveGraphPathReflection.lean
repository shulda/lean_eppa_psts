import PSTSEPPA.ABO.Morphisms

/-!
# Genuine signed-path reflection by bijective labelled graph morphisms

Bijectivity on BOTH vertices and directed signed-edge tokens turns a
labelled graph morphism into an actual graph isomorphism, even for
incomplete graphs, parallel labels, formal inverse edges and loops.
The inverse morphism preserves sources, inverses and labels exactly,
and hence reflects every genuinely realised signed path.

This is a required intermediate step towards transporting all
proper-alphabet component tags under the rooted source-H1
component-to-local-H1[A] graph isomorphism (#352), before the
full coset extensions and augmentations can be compared.
-/

namespace PSTSEPPA
namespace ABO

namespace LabelledGraphHom

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable {G : LabelledGraph V₁ E₁ ι}
variable {H : LabelledGraph V₂ E₂ ι}

/-- The exact vertex bijection of a bijective graph morphism. -/
noncomputable def vertexEquivOfBijective
    (f : LabelledGraphHom G H)
    (hv : Function.Bijective f.onVertex) : V₁ ≃ V₂ :=
  Equiv.ofBijective f.onVertex hv

/-- The exact oriented signed edge-token bijection. -/
noncomputable def edgeEquivOfBijective
    (f : LabelledGraphHom G H)
    (he : Function.Bijective f.onEdge) : E₁ ≃ E₂ :=
  Equiv.ofBijective f.onEdge he

/-- The inverse of a bijective labelled graph morphism is
itself a genuine labelled graph morphism. -/
noncomputable def inverseOfBijective
    (f : LabelledGraphHom G H)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge) :
    LabelledGraphHom H G where
  onVertex := (vertexEquivOfBijective f hv).symm
  onEdge := (edgeEquivOfBijective f he).symm
  map_source e := by
    apply (vertexEquivOfBijective f hv).injective
    change f.onVertex
      (G.source ((edgeEquivOfBijective f he).symm e)) =
      f.onVertex ((vertexEquivOfBijective f hv).symm (H.source e))
    calc
      f.onVertex (G.source ((edgeEquivOfBijective f he).symm e)) =
        H.source (f.onEdge ((edgeEquivOfBijective f he).symm e)) :=
          (f.map_source _).symm
      _ = H.source e := by
        have hEdgeEval : f.onEdge ((edgeEquivOfBijective f he).symm e) = e :=
          (edgeEquivOfBijective f he).apply_symm_apply e
        rw [hEdgeEval]
      _ = f.onVertex ((vertexEquivOfBijective f hv).symm (H.source e)) :=
        ((vertexEquivOfBijective f hv).apply_symm_apply (H.source e)).symm
  map_inv e := by
    apply (edgeEquivOfBijective f he).injective
    change f.onEdge ((edgeEquivOfBijective f he).symm (H.inv e)) =
      f.onEdge (G.inv ((edgeEquivOfBijective f he).symm e))
    calc
      f.onEdge ((edgeEquivOfBijective f he).symm (H.inv e)) =
        H.inv e := (edgeEquivOfBijective f he).apply_symm_apply (H.inv e)
      _ = H.inv (f.onEdge ((edgeEquivOfBijective f he).symm e)) := by
        have hEdgeEval : f.onEdge ((edgeEquivOfBijective f he).symm e) = e :=
          (edgeEquivOfBijective f he).apply_symm_apply e
        rw [hEdgeEval]
      _ = f.onEdge (G.inv ((edgeEquivOfBijective f he).symm e)) :=
        (f.map_inv _).symm
  map_label e := by
    change G.label ((edgeEquivOfBijective f he).symm e) = H.label e
    calc
      G.label ((edgeEquivOfBijective f he).symm e) =
        H.label (f.onEdge ((edgeEquivOfBijective f he).symm e)) :=
          (f.map_label _).symm
      _ = H.label e := by
        have hEdgeEval : f.onEdge ((edgeEquivOfBijective f he).symm e) = e :=
          (edgeEquivOfBijective f he).apply_symm_apply e
        rw [hEdgeEval]

@[simp] theorem inverseOfBijective_onVertex_apply
    (f : LabelledGraphHom G H)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (x : V₁) :
    (f.inverseOfBijective hv he).onVertex (f.onVertex x) = x :=
  (vertexEquivOfBijective f hv).symm_apply_apply x

@[simp] theorem inverseOfBijective_onEdge_apply
    (f : LabelledGraphHom G H)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (e : E₁) :
    (f.inverseOfBijective hv he).onEdge (f.onEdge e) = e :=
  (edgeEquivOfBijective f he).symm_apply_apply e

end LabelledGraphHom

namespace EGraph

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable {G : EGraph V₁ E₁ ι}
variable {H : EGraph V₂ E₂ ι}

/-- Every genuine signed path downstairs reflects upstairs along
a bijective labelled morphism of incomplete E-graphs. -/
theorem follows_reflect_of_bijective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    {u v : V₁} {w : LabelWord ι}
    (hp : H.Follows (f.onVertex u) w (f.onVertex v)) :
    G.Follows u w v := by
  have hinv := hp.map (f.inverseOfBijective hv he)
  simpa only [f.inverseOfBijective_onVertex_apply] using hinv

/-- Exact preservation AND reflection of all actual signed paths
through a vertex- and directed-edge-bijective graph morphism. -/
theorem follows_iff_bijective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (u v : V₁) (w : LabelWord ι) :
    G.Follows u w v ↔
      H.Follows (f.onVertex u) w (f.onVertex v) := by
  constructor
  · intro hp
    exact hp.map f
  · intro hp
    exact follows_reflect_of_bijective f hv he hp

end EGraph
end ABO
end PSTSEPPA
