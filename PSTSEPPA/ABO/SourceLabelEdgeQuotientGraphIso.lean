import PSTSEPPA.ABO.SourceLabelEdgeQuotientEGraph
import PSTSEPPA.ABO.BijectiveGraphPathReflection

/-!
# Genuine isomorphism of exact signed source-and-label edge quotients

An ABO multi-coset edge is a raw directed signed token modulo equality of
its GLUED source and its FULL signed label; the ambient group coordinate is
not its quotient identity.

Suppose two literal raw oriented graphs are related by genuine bijections
on their vertices and directed signed edges which preserve source, label
and formal reversal. This file shows that:

* source/label-to-target congruence transfers in BOTH directions;
* the exact edge quotient equivalence is a graph morphism preserving
  source, signed label and formal inverse;
* the morphism is bijective on vertices and oriented edge tokens;
* all genuinely realised signed paths are preserved and REFLECTED.

No ambient group retractability is hidden here. In the source ABO
application the raw-edge and vertex bijections must still be supplied
by the actual tagged-coset gluing geometry.
-/

namespace PSTSEPPA
namespace ABO

variable {V W E F ι : Type*}

/-- Target congruence on the exact raw source-and-label equivalence
is invariant under signed-graph bijections, rather than requiring any
ambient Cayley-coordinate injectivity. -/
theorem sourceLabelTargetCongruent_transport
    (G : LabelledGraph V E ι) (H : LabelledGraph W F ι)
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (hsrc : ∀ e, H.source (eEquiv e) = vEquiv (G.source e))
    (hlabel : ∀ e, H.label (eEquiv e) = G.label e)
    (hinv : ∀ e, H.inv (eEquiv e) = eEquiv (G.inv e))
    (hG : G.SourceLabelTargetCongruent) :
    H.SourceLabelTargetCongruent := by
  have htarget (e : E) :
      H.target (eEquiv e) = vEquiv (G.target e) := by
    change H.source (H.inv (eEquiv e)) =
      vEquiv (G.source (G.inv e))
    rw [hinv e]
    exact hsrc (G.inv e)
  intro y z hyz hl
  obtain ⟨e, rfl⟩ := eEquiv.surjective y
  obtain ⟨f, rfl⟩ := eEquiv.surjective z
  have hsG : G.source e = G.source f := by
    apply vEquiv.injective
    calc
      vEquiv (G.source e) = H.source (eEquiv e) := (hsrc e).symm
      _ = H.source (eEquiv f) := hyz
      _ = vEquiv (G.source f) := hsrc f
  have hlG : G.label e = G.label f := by
    calc
      G.label e = H.label (eEquiv e) := (hlabel e).symm
      _ = H.label (eEquiv f) := hl
      _ = G.label f := hlabel f
  calc
    H.target (eEquiv e) = vEquiv (G.target e) := htarget e
    _ = vEquiv (G.target f) :=
      congrArg vEquiv (hG e f hsG hlG)
    _ = H.target (eEquiv f) := (htarget f).symm

/-- Quotient the EXACT source-and-signed-label edge relation on both
sides. The induced bijections form a genuine signed-graph morphism.
Source/label/edge-inversion congruence is proved, not postulated. -/
noncomputable def sourceLabelGraphQuotientHom
    (G : LabelledGraph V E ι) (H : LabelledGraph W F ι)
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (hsrc : ∀ e, H.source (eEquiv e) = vEquiv (G.source e))
    (hlabel : ∀ e, H.label (eEquiv e) = G.label e)
    (hinv : ∀ e, H.inv (eEquiv e) = eEquiv (G.inv e))
    (hG : G.SourceLabelTargetCongruent)
    (hH : H.SourceLabelTargetCongruent) :
    LabelledGraphHom
      (sourceLabelGraphQuotientEGraph G hG).toLabelledGraph
      (sourceLabelGraphQuotientEGraph H hH).toLabelledGraph where
  onVertex := vEquiv
  onEdge := sourceLabelEdgeQuotientEquiv
    vEquiv eEquiv G.source H.source G.label H.label hsrc hlabel
  map_source := by
    intro q
    change
      sourceLabelEdgeQuotientSource H.source H.label
        (sourceLabelEdgeQuotientEquiv vEquiv eEquiv
          G.source H.source G.label H.label hsrc hlabel q) =
      vEquiv (sourceLabelEdgeQuotientSource G.source G.label q)
    exact sourceLabelEdgeQuotientSource_natural
      vEquiv eEquiv G.source H.source G.label H.label hsrc hlabel q
  map_inv := by
    intro q
    change
      sourceLabelEdgeQuotientEquiv vEquiv eEquiv
        G.source H.source G.label H.label hsrc hlabel
          (sourceLabelGraphQuotientInv G hG q) =
      sourceLabelGraphQuotientInv H hH
        (sourceLabelEdgeQuotientEquiv vEquiv eEquiv
          G.source H.source G.label H.label hsrc hlabel q)
    exact (sourceLabelGraphQuotientInv_natural
      G H vEquiv eEquiv hsrc hlabel hG hH hinv q).symm
  map_label := by
    intro q
    change
      sourceLabelEdgeQuotientLabel H.source H.label
        (sourceLabelEdgeQuotientEquiv vEquiv eEquiv
          G.source H.source G.label H.label hsrc hlabel q) =
      sourceLabelEdgeQuotientLabel G.source G.label q
    exact sourceLabelEdgeQuotientLabel_natural
      vEquiv eEquiv G.source H.source G.label H.label hsrc hlabel q

/-- The exact quotient graph morphism is a genuine signed graph
isomorphism: BOTH true vertices and quotient oriented edge tokens
are bijective. -/
theorem sourceLabelGraphQuotientHom_bijective
    (G : LabelledGraph V E ι) (H : LabelledGraph W F ι)
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (hsrc : ∀ e, H.source (eEquiv e) = vEquiv (G.source e))
    (hlabel : ∀ e, H.label (eEquiv e) = G.label e)
    (hinv : ∀ e, H.inv (eEquiv e) = eEquiv (G.inv e))
    (hG : G.SourceLabelTargetCongruent)
    (hH : H.SourceLabelTargetCongruent) :
    Function.Bijective
        (sourceLabelGraphQuotientHom G H vEquiv eEquiv
          hsrc hlabel hinv hG hH).onVertex ∧
      Function.Bijective
        (sourceLabelGraphQuotientHom G H vEquiv eEquiv
          hsrc hlabel hinv hG hH).onEdge := by
  constructor
  · exact vEquiv.bijective
  · exact (sourceLabelEdgeQuotientEquiv
      vEquiv eEquiv G.source H.source G.label H.label
      hsrc hlabel).bijective

/-- True path equivalence, not merely agreement of word values in
an ambient group. This includes inverses, geometric loops and the
absence of old edges in possibly incomplete coset extensions. -/
theorem sourceLabelGraphQuotientHom_follows_iff
    (G : LabelledGraph V E ι) (H : LabelledGraph W F ι)
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (hsrc : ∀ e, H.source (eEquiv e) = vEquiv (G.source e))
    (hlabel : ∀ e, H.label (eEquiv e) = G.label e)
    (hinv : ∀ e, H.inv (eEquiv e) = eEquiv (G.inv e))
    (hG : G.SourceLabelTargetCongruent)
    (hH : H.SourceLabelTargetCongruent)
    (u v : V) (w : LabelWord ι) :
    (sourceLabelGraphQuotientEGraph G hG).Follows u w v ↔
      (sourceLabelGraphQuotientEGraph H hH).Follows
        (vEquiv u) w (vEquiv v) := by
  exact EGraph.follows_iff_bijective
    (sourceLabelGraphQuotientHom G H vEquiv eEquiv
      hsrc hlabel hinv hG hH)
    (sourceLabelGraphQuotientHom_bijective G H vEquiv eEquiv
      hsrc hlabel hinv hG hH).1
    (sourceLabelGraphQuotientHom_bijective G H vEquiv eEquiv
      hsrc hlabel hinv hG hH).2
    u v w

end ABO
end PSTSEPPA
