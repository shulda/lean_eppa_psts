import PSTSEPPA.ABO.SourceLabelEdgeQuotientNaturality

/-!
# Incidence of the exact signed source-and-label edge quotient

For the genuine ABO multi-coset raw directed edges, the quotient relation
identifies precisely those tokens having equal ALREADY-GLUED sources and
identical signed labels. It is not equality in the ambient Cayley graph.

This file gives the resulting quotient its exact source and signed-label maps,
and proves that both commute with the induced quotient equivalence whenever
the tagged raw edges are transported by a genuine incidence- and label-
preserving bijection.

Targets require an additional, nonautomatic congruence hypothesis.
We explicitly parameterise that hypothesis rather than pretending that the
source-and-label quotient, by itself, is an E-graph. Under it, target maps
descend and are natural as well. The formal-inverse operation and the
source-specific multi-coset geometry are separate obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {V W E F Label : Type*}

/-- The literal glued source descends to the incidence-and-label
edge quotient by the defining relation itself. -/
noncomputable def sourceLabelEdgeQuotientSource
    (src : E → V) (label : E → Label) :
    Quotient (sourceLabelEdgeSetoid src label) → V :=
  fun q => Quotient.liftOn q src (by
    intro e f hef
    exact hef.1)

/-- The exact signed label also descends, retaining the SIGN of
each original directed edge token. -/
noncomputable def sourceLabelEdgeQuotientLabel
    (src : E → V) (label : E → Label) :
    Quotient (sourceLabelEdgeSetoid src label) → Label :=
  fun q => Quotient.liftOn q label (by
    intro e f hef
    exact hef.2)

/-- Target incidence is well-defined only after proving the
ABO source/label-to-target congruence. This separate hypothesis
cannot be discarded for a general family of raw edges. -/
noncomputable def sourceLabelEdgeQuotientTarget
    (src : E → V) (label : E → Label) (target : E → V)
    (hTarget : ∀ e f : E,
      src e = src f → label e = label f → target e = target f) :
    Quotient (sourceLabelEdgeSetoid src label) → V :=
  fun q => Quotient.liftOn q target (by
    intro e f hef
    exact hTarget e f hef.1 hef.2)

/-- Glued source incidence is preserved by the exact edge quotient
equivalence induced by bijections of TRUE tagged raw edges and vertices. -/
theorem sourceLabelEdgeQuotientSource_natural
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (src : E → V) (tgtSrc : F → W)
    (label : E → Label) (tgtLabel : F → Label)
    (hsrc : ∀ e, tgtSrc (eEquiv e) = vEquiv (src e))
    (hlabel : ∀ e, tgtLabel (eEquiv e) = label e)
    (q : Quotient (sourceLabelEdgeSetoid src label)) :
    sourceLabelEdgeQuotientSource tgtSrc tgtLabel
      (sourceLabelEdgeQuotientEquiv
        vEquiv eEquiv src tgtSrc label tgtLabel hsrc hlabel q) =
    vEquiv (sourceLabelEdgeQuotientSource src label q) := by
  induction q using Quotient.inductionOn with
  | h e =>
      change tgtSrc (eEquiv e) = vEquiv (src e)
      exact hsrc e

/-- The signed edge label, not just its unsigned generator,
is preserved by transport of the exact edge quotient. -/
theorem sourceLabelEdgeQuotientLabel_natural
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (src : E → V) (tgtSrc : F → W)
    (label : E → Label) (tgtLabel : F → Label)
    (hsrc : ∀ e, tgtSrc (eEquiv e) = vEquiv (src e))
    (hlabel : ∀ e, tgtLabel (eEquiv e) = label e)
    (q : Quotient (sourceLabelEdgeSetoid src label)) :
    sourceLabelEdgeQuotientLabel tgtSrc tgtLabel
      (sourceLabelEdgeQuotientEquiv
        vEquiv eEquiv src tgtSrc label tgtLabel hsrc hlabel q) =
    sourceLabelEdgeQuotientLabel src label q := by
  induction q using Quotient.inductionOn with
  | h e =>
      change tgtLabel (eEquiv e) = label e
      exact hlabel e

/-- Once both genuine raw edge systems satisfy the target congruence,
their descended TARGET maps commute with the quotient equivalence too.
This is the remaining incidence part of the desired graph isomorphism. -/
theorem sourceLabelEdgeQuotientTarget_natural
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (src : E → V) (tgtSrc : F → W)
    (label : E → Label) (tgtLabel : F → Label)
    (target : E → V) (tgtTarget : F → W)
    (hsrc : ∀ e, tgtSrc (eEquiv e) = vEquiv (src e))
    (hlabel : ∀ e, tgtLabel (eEquiv e) = label e)
    (hTarget : ∀ e f : E,
      src e = src f → label e = label f → target e = target f)
    (hTgtTarget : ∀ e f : F,
      tgtSrc e = tgtSrc f → tgtLabel e = tgtLabel f →
        tgtTarget e = tgtTarget f)
    (hmap : ∀ e, tgtTarget (eEquiv e) = vEquiv (target e))
    (q : Quotient (sourceLabelEdgeSetoid src label)) :
    sourceLabelEdgeQuotientTarget tgtSrc tgtLabel tgtTarget hTgtTarget
      (sourceLabelEdgeQuotientEquiv
        vEquiv eEquiv src tgtSrc label tgtLabel hsrc hlabel q) =
    vEquiv (sourceLabelEdgeQuotientTarget src label target hTarget q) := by
  induction q using Quotient.inductionOn with
  | h e =>
      change tgtTarget (eEquiv e) = vEquiv (target e)
      exact hmap e

end ABO
end PSTSEPPA
