import PSTSEPPA.ABO.RootedSignedBComponentGraphIso
import PSTSEPPA.ABO.BijectiveGraphPathReflection

/-!
# Exact signed B-component graph-shape transport

The project already contains the correct inverse for a labelled graph
homomorphism bijective on ACTUAL vertices and ORIENTED signed edge
tokens (`BijectiveGraphPathReflection`). A second independent copy
would be wrong: this file deliberately reuses that existing inverse.

This theorem transports a genuine signed graph isomorphism of an
entire B-component across another genuine signed graph isomorphism.
It works for incomplete EGraphs, including missing old edges,
formal inverse edge tokens and loops. It is the graph-theoretic
composition step needed for translating the local H[C] canonical
proper-cluster shape into an original rooted Γ-component.

No ambient Cayley injectivity, invented old edges, extra axioms or sorry.
-/

namespace PSTSEPPA
namespace ABO

namespace LabelledGraphHom

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable {G : LabelledGraph V₁ E₁ ι}
variable {H : LabelledGraph V₂ E₂ ι}

/-- The previously constructed TRUE inverse graph homomorphism is
bijective on all vertices AND all original oriented edge tokens. -/
theorem inverseOfBijective_bijective
    (f : LabelledGraphHom G H)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge) :
    Function.Bijective (f.inverseOfBijective hv he).onVertex ∧
    Function.Bijective (f.inverseOfBijective hv he).onEdge :=
  ⟨(vertexEquivOfBijective f hv).symm.bijective,
   (edgeEquivOfBijective f he).symm.bijective⟩

end LabelledGraphHom

namespace EGraph

variable {V E W F X Y ι : Type*}
variable [Fintype ι] [DecidableEq ι]

/-- Compose a TRUE signed B-component isomorphism with the
inverse of a bijective rooted signed graph map, transporting
the same labelled canonical shape to the OTHER entire
B-component, not only to its ambient group-coordinate image.

Every oriented edge token, including formal inverses, is
transported bijectively. The target `T` may be any labelled
graph, in particular a concrete translated proper B-cluster. -/
theorem signedBComponent_shape_transport_of_bijective
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (B : Finset ι) (anchor : V)
    (T : LabelledGraph X Y ι)
    (g : LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph T)
    (hgv : Function.Bijective g.onVertex)
    (hge : Function.Bijective g.onEdge) :
    ∃ h : LabelledGraphHom
      (H.BComponentEGraph B (f.onVertex anchor)).toLabelledGraph T,
      Function.Bijective h.onVertex ∧
      Function.Bijective h.onEdge := by
  let fB := G.BComponentHomOfBijective H f hv he B anchor
  have hB :
      Function.Bijective fB.onVertex ∧
      Function.Bijective fB.onEdge :=
    G.BComponentHomOfBijective_bijective H f hv he B anchor
  let inv := fB.inverseOfBijective hB.1 hB.2
  have hInv :
      Function.Bijective inv.onVertex ∧
      Function.Bijective inv.onEdge :=
    fB.inverseOfBijective_bijective hB.1 hB.2
  let h := g.comp inv
  refine ⟨h, ?_, ?_⟩
  · change Function.Bijective (g.onVertex ∘ inv.onVertex)
    exact ⟨hgv.1.comp hInv.1.1, hgv.2.comp hInv.1.2⟩
  · change Function.Bijective (g.onEdge ∘ inv.onEdge)
    exact ⟨hge.1.comp hInv.2.1, hge.2.comp hInv.2.2⟩

end EGraph
end ABO
end PSTSEPPA
