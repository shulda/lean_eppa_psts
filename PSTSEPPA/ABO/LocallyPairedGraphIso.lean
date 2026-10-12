import PSTSEPPA.ABO.WeakCompletePairedEdges
import PSTSEPPA.ABO.BijectiveGraphPathReflection

/-!
# Paired signed-label availability transports across actual graph isomorphisms

Completing an incomplete signed EGraph by inserting only fixed-point
loops is legal exactly when the original graph is locally paired:
at each vertex, either both the positive and negative i-edges exist,
or both are missing.

A mere vertex bijection is insufficient to preserve that condition.
A vertex- AND directed-edge-bijective labelled morphism does preserve
and REFLECT the existence of each genuinely labelled old edge.

We prove the signed edge-availability equivalence and transport the
locally paired property. Both are independent of ambient Cayley
coordinates and of retractability, so they apply directly to the
source/local Γ[A]-normalized coset graph isomorphism.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V W E F ι : Type*}
variable (G : EGraph V E ι) (H : EGraph W F ι)

/-- Exact preservation and reflection of the presence of an actual
old signed edge at a specific vertex, with arbitrary label and sign.
No assumption of completed action graphs or global injectivity of
an ambient Cayley projection is used. -/
theorem signedEdgeExists_iff_of_bijective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (s : SignedLabel ι) (u : V) :
    (∃ e : E, G.source e = u ∧ G.label e = s) ↔
      (∃ d : F, H.source d = f.onVertex u ∧ H.label d = s) := by
  constructor
  · rintro ⟨e, hsrc, hlab⟩
    exact ⟨f.onEdge e,
      (f.map_source e).trans (congrArg f.onVertex hsrc),
      (f.map_label e).trans hlab⟩
  · rintro ⟨d, hsrc, hlab⟩
    obtain ⟨e, rfl⟩ := he.2 d
    refine ⟨e, ?_, ?_⟩
    · apply hv.1
      exact (f.map_source e).symm.trans hsrc
    · exact (f.map_label e).symm.trans hlab

/-- The genuine source/local signed EGraph isomorphism preserves
the exact property required for LEGAL trivial fixed-loop completion.
In particular old inverse labels cannot become unpaired. -/
theorem locallyPairedLabels_of_bijective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (hG : G.LocallyPairedLabels) :
    H.LocallyPairedLabels := by
  intro y i
  obtain ⟨u, rfl⟩ := hv.2 y
  exact
    (G.signedEdgeExists_iff_of_bijective H f hv he (.pos i) u).symm.trans
      ((hG u i).trans
        (G.signedEdgeExists_iff_of_bijective H f hv he (.neg i) u))

end EGraph
end ABO
end PSTSEPPA
