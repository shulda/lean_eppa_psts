import PSTSEPPA.ABO.TranslatedQuotientSkeletonPullback
import PSTSEPPA.ABO.ComponentSubgraph

/-!
# Connected Cayley-cover morphisms factor through translated quotient pullbacks

Let Q : H ↠ Γ be a generator-preserving group quotient, L a genuine
incomplete H-Cayley A-skeleton, K a genuine incomplete Γ-Cayley
A-skeleton, and f : L → K any true signed-labelled graph morphism.

Fix an intrinsic B-component of L at root. Its vertex and edge tokens
form the literal component subgraph L_B(root). The previously certified
path translation theorem gives one constant

  c := f(root) · Q(root)⁻¹

such that f(x) = c·Q(x) at EVERY actual vertex of the component.

Here we strengthen that from vertices to ACTUAL directed signed
edges, and construct a literal INJECTIVE LABELLED GRAPH MORPHISM

  L_B(root) → translatedPullback(K,Q,c)

whose composite with the canonical translated-pullback morphism to K
agrees on vertices AND signed edges with the original f restricted
to L_B(root).

This is a genuine factorization for incomplete graphs; no missing
edges, hypothetical transitions, or ambient-coset paths are added.

It reduces the study of arbitrary connected covers over a FIXED
labelled quotient to translated canonical pullbacks, but does not
claim all source ABO Y₁-cover actions arise from our chosen quotient
or that the entire Z₁ catalogue is complete.
-/

namespace PSTSEPPA
namespace ABO

variable {ι H Γ : Type*} [Fintype ι] [DecidableEq ι]
variable [Group H] [Group Γ]
variable {genH : ι → H} {genΓ : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (L : CayleySubgraphSpec genH A)
variable (K : CayleySubgraphSpec genΓ A)
variable (Q : LabelledGroupQuotient genH genΓ)

variable
  (f : LabelledGraphHom
    (L.toEGraph).toLabelledGraph
    (K.toEGraph).toLabelledGraph)

/-- The unique left-translation constant picked by a component root.
It may depend on the root, but never on a vertex reached from it. -/
def componentTranslationConstant (root : L.Vertex) : Γ :=
  (f.onVertex root).1 * (Q.hom root.1)⁻¹

/-- The group coordinate of f on a true B-component is literally the
corresponding translated quotient coordinate, for EVERY selected vertex. -/
theorem component_vertex_translated_coordinate
    (B : Finset ι) (root : L.Vertex)
    (x : (L.subalphabetComponentSubgraph B root).Vertex) :
    (f.onVertex
        ((L.subalphabetComponentSubgraphHom B root).onVertex x)).1 =
      L.componentTranslationConstant K Q f root * Q.hom x.1 := by
  obtain ⟨u, hu, hreach⟩ := x.2
  have hOld :
      (L.subalphabetComponentSubgraphHom B root).onVertex x = u :=
    Subtype.ext hu.symm
  have hEq :=
    L.labelledHom_vertex_eq_leftTranslate_on_component
      K Q f B root u hreach
  rw [hOld]
  change (f.onVertex u).1 =
    (f.onVertex root).1 * (Q.hom root.1)⁻¹ * Q.hom x.1
  rw [← hu]
  exact hEq

/-- Even the SIGNED EDGE TOKEN f(e), not just its endpoints, is
completely determined on a connected component by the same
left translation and the literal quotient of the source group point. -/
theorem component_edge_translated_coordinate
    (B : Finset ι) (root : L.Vertex)
    (e : (L.subalphabetComponentSubgraph B root).Edge) :
    (f.onEdge
        ((L.subalphabetComponentSubgraphHom B root).onEdge e)).1 =
      (L.componentTranslationConstant K Q f root * Q.hom e.1.1,
        e.1.2) := by
  obtain ⟨old, hold, _hB, hreach⟩ := e.2
  have hOld :
      (L.subalphabetComponentSubgraphHom B root).onEdge e = old :=
    Subtype.ext hold.symm
  have hSrc :
      (f.onVertex ((L.toEGraph).source old)).1 =
        (f.onVertex root).1 * (Q.hom root.1)⁻¹ *
          Q.hom ((L.toEGraph).source old).1 :=
    L.labelledHom_vertex_eq_leftTranslate_on_component
      K Q f B root ((L.toEGraph).source old) hreach
  apply Prod.ext
  · calc
      (f.onEdge
          ((L.subalphabetComponentSubgraphHom B root).onEdge e)).1.1 =
          (f.onEdge old).1.1 := by rw [hOld]
      _ = (f.onVertex ((L.toEGraph).source old)).1 :=
        congrArg Subtype.val (f.map_source old)
      _ = (f.onVertex root).1 * (Q.hom root.1)⁻¹ *
          Q.hom ((L.toEGraph).source old).1 := hSrc
      _ = L.componentTranslationConstant K Q f root * Q.hom e.1.1 := by
        change (f.onVertex root).1 * (Q.hom root.1)⁻¹ *
          Q.hom old.1.1 =
            ((f.onVertex root).1 * (Q.hom root.1)⁻¹) *
              Q.hom e.1.1
        rw [hold]
  · calc
      (f.onEdge
          ((L.subalphabetComponentSubgraphHom B root).onEdge e)).1.2 =
          (f.onEdge old).1.2 := by rw [hOld]
      _ = old.1.2 := f.map_label old
      _ = e.1.2 := congrArg Prod.snd hold

/-- Each actual vertex of the intrinsic component has a genuine
vertex in the canonically translated pullback; this is not inferred
from an ambient subgroup coset. -/
theorem component_vertex_mem_translatedPullback
    (B : Finset ι) (root : L.Vertex)
    (x : (L.subalphabetComponentSubgraph B root).Vertex) :
    x.1 ∈
      (K.translatedPullbackQuotient Q
        (L.componentTranslationConstant K Q f root)).vertices := by
  change
    L.componentTranslationConstant K Q f root * Q.hom x.1 ∈ K.vertices
  rw [← L.component_vertex_translated_coordinate K Q f B root x]
  exact (f.onVertex
    ((L.subalphabetComponentSubgraphHom B root).onVertex x)).2

/-- Likewise EVERY old signed component edge is literally present
in the translated pullback, with no completion of missing edges. -/
theorem component_edge_mem_translatedPullback
    (B : Finset ι) (root : L.Vertex)
    (e : (L.subalphabetComponentSubgraph B root).Edge) :
    e.1 ∈
      (K.translatedPullbackQuotient Q
        (L.componentTranslationConstant K Q f root)).edges := by
  change
    (L.componentTranslationConstant K Q f root * Q.hom e.1.1,
      e.1.2) ∈ K.edges
  rw [← L.component_edge_translated_coordinate K Q f B root e]
  exact (f.onEdge
    ((L.subalphabetComponentSubgraphHom B root).onEdge e)).2

/-- A genuine labelled graph factor from the entire intrinsic
B-component of L into the fixed translated canonical pullback. -/
noncomputable def componentToTranslatedPullback
    (B : Finset ι) (root : L.Vertex) :
    LabelledGraphHom
      ((L.subalphabetComponentSubgraph B root).toEGraph).toLabelledGraph
      ((K.translatedPullbackQuotient Q
        (L.componentTranslationConstant K Q f root)).toEGraph).toLabelledGraph where
  onVertex x :=
    ⟨x.1, L.component_vertex_mem_translatedPullback K Q f B root x⟩
  onEdge e :=
    ⟨e.1, L.component_edge_mem_translatedPullback K Q f B root e⟩
  map_source := by
    intro e
    apply Subtype.ext
    rfl
  map_inv := by
    intro e
    apply Subtype.ext
    rfl
  map_label := by
    intro e
    rfl

/-- The literal factorization does not identify distinct vertices. -/
theorem componentToTranslatedPullback_vertex_injective
    (B : Finset ι) (root : L.Vertex) :
    Function.Injective
      (L.componentToTranslatedPullback K Q f B root).onVertex := by
  intro x y hxy
  have hv : x.1 = y.1 :=
    congrArg (fun z :
      (K.translatedPullbackQuotient Q
        (L.componentTranslationConstant K Q f root)).Vertex => z.1) hxy
  exact Subtype.ext hv

/-- The factorization is also injective on signed directed edge tokens,
including formal inverse tokens of loops. -/
theorem componentToTranslatedPullback_edge_injective
    (B : Finset ι) (root : L.Vertex) :
    Function.Injective
      (L.componentToTranslatedPullback K Q f B root).onEdge := by
  intro e₁ e₂ heq
  have hv : e₁.1 = e₂.1 :=
    congrArg (fun z :
      (K.translatedPullbackQuotient Q
        (L.componentTranslationConstant K Q f root)).Edge => z.1) heq
  exact Subtype.ext hv

/-- Vertexwise commutation of the genuine graph factorization:
the translated-pullback cover composed with the injected
component is EXACTLY the original f restricted to this component. -/
theorem componentToTranslatedPullback_vertex_commutes
    (B : Finset ι) (root : L.Vertex)
    (x : (L.subalphabetComponentSubgraph B root).Vertex) :
    (K.translatedPullbackQuotientHom Q
      (L.componentTranslationConstant K Q f root)).onVertex
      ((L.componentToTranslatedPullback K Q f B root).onVertex x) =
    f.onVertex ((L.subalphabetComponentSubgraphHom B root).onVertex x) := by
  apply Subtype.ext
  exact (L.component_vertex_translated_coordinate K Q f B root x).symm

/-- The SAME strict commutation holds for every actual signed edge,
which is stronger than merely matching endpoint coordinates. -/
theorem componentToTranslatedPullback_edge_commutes
    (B : Finset ι) (root : L.Vertex)
    (e : (L.subalphabetComponentSubgraph B root).Edge) :
    (K.translatedPullbackQuotientHom Q
      (L.componentTranslationConstant K Q f root)).onEdge
      ((L.componentToTranslatedPullback K Q f B root).onEdge e) =
    f.onEdge ((L.subalphabetComponentSubgraphHom B root).onEdge e) := by
  apply Subtype.ext
  exact (L.component_edge_translated_coordinate K Q f B root e).symm

end CayleySubgraphSpec
end ABO
end PSTSEPPA
