import PSTSEPPA.ABO.ExactQuotientEquivTransport
import PSTSEPPA.ABO.MultiCosetEdgeQuotient

/-!
# Exact incidence-and-signed-label edge quotient transport

The correct edge quotient of the ABO multi-coset extension
identifies two raw directed signed edge tokens iff their SOURCES
agree in the already glued VERTEX quotient AND their SIGNED LABELS
agree. Equality of ambient Cayley edge coordinates is not the
definition and must not replace component-tag-aware source equality.

Here we isolate that exact source-and-label equivalence relation.
Given a true bijection of glued vertex types and a true bijection
of raw oriented edge tokens, preserving each edge's source through
the vertex map and preserving every literal signed label, the
induced raw edge equivalence relation is preserved AND REFLECTED.
Consequently the quotient sets of all actual signed edge tokens
are genuinely equivalent. The induced quotient map preserves raw
inclusion classes and has a two-sided inverse.

This will be instantiated after the independent source-rooted
full VERTEX quotient equivalence (#371) and single-B EGraph
isomorphism (#376–#377) are certified. It neither invents old
edges nor asserts global retractability of the original H1,
and does not yet construct target/congruence or EGraph reversal.
-/

namespace PSTSEPPA
namespace ABO

variable {V W E F Label : Type*}

/-- The actual incidence + signed-label equivalence relation
on a collection of raw oriented edge tokens. -/
def sourceLabelEdgeSetoid (source : E → V) (label : E → Label) :
    Setoid E where
  r e f := source e = source f ∧ label e = label f
  iseqv := {
    refl := fun _ => ⟨rfl, rfl⟩
    symm := fun h => ⟨h.1.symm, h.2.symm⟩
    trans := fun h k => ⟨h.1.trans k.1, h.2.trans k.2⟩
  }

/-- Exact preservation and reflection of source-and-signed-label
coincidence. A source equality is reflected through the vertex
bijection; an edge group coordinate is NEVER used. -/
theorem sourceLabelRelated_iff_of_equivs
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (src : E → V) (tgtSrc : F → W)
    (label : E → Label) (tgtLabel : F → Label)
    (hsrc : ∀ e, tgtSrc (eEquiv e) = vEquiv (src e))
    (hlabel : ∀ e, tgtLabel (eEquiv e) = label e)
    (e f : E) :
    (src e = src f ∧ label e = label f) ↔
    (tgtSrc (eEquiv e) = tgtSrc (eEquiv f) ∧
      tgtLabel (eEquiv e) = tgtLabel (eEquiv f)) := by
  constructor
  · rintro ⟨hs, hl⟩
    constructor
    · calc
        tgtSrc (eEquiv e) = vEquiv (src e) := hsrc e
        _ = vEquiv (src f) := by rw [hs]
        _ = tgtSrc (eEquiv f) := (hsrc f).symm
    · calc
        tgtLabel (eEquiv e) = label e := hlabel e
        _ = label f := hl
        _ = tgtLabel (eEquiv f) := (hlabel f).symm
  · rintro ⟨hs, hl⟩
    constructor
    · apply vEquiv.injective
      calc
        vEquiv (src e) = tgtSrc (eEquiv e) := (hsrc e).symm
        _ = tgtSrc (eEquiv f) := hs
        _ = vEquiv (src f) := hsrc f
    · calc
        label e = tgtLabel (eEquiv e) := (hlabel e).symm
        _ = tgtLabel (eEquiv f) := hl
        _ = label f := hlabel f

/-- A genuine equivalence of the EXACT quotient of all raw
directed signed edges by equal glued source and signed label.
No full ambient retractability and no ambient group-coordinate
injectivity are required. -/
noncomputable def sourceLabelEdgeQuotientEquiv
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (src : E → V) (tgtSrc : F → W)
    (label : E → Label) (tgtLabel : F → Label)
    (hsrc : ∀ e, tgtSrc (eEquiv e) = vEquiv (src e))
    (hlabel : ∀ e, tgtLabel (eEquiv e) = label e) :
    Quotient (sourceLabelEdgeSetoid src label) ≃
    Quotient (sourceLabelEdgeSetoid tgtSrc tgtLabel) where
  toFun q :=
    Quotient.liftOn q
      (fun e => Quotient.mk _ (eEquiv e))
      (by
        intro e f hef
        apply Quotient.sound
        exact (sourceLabelRelated_iff_of_equivs
          vEquiv eEquiv src tgtSrc label tgtLabel
          hsrc hlabel e f).mp hef)
  invFun q :=
    Quotient.liftOn q
      (fun y => Quotient.mk _ (eEquiv.symm y))
      (by
        intro y z hyz
        apply Quotient.sound
        apply (sourceLabelRelated_iff_of_equivs
          vEquiv eEquiv src tgtSrc label tgtLabel hsrc hlabel
          (eEquiv.symm y) (eEquiv.symm z)).mpr
        change tgtSrc y = tgtSrc z ∧ tgtLabel y = tgtLabel z at hyz
        simpa only [eEquiv.apply_symm_apply] using hyz)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h e =>
      change Quotient.mk (sourceLabelEdgeSetoid src label)
        (eEquiv.symm (eEquiv e)) =
        Quotient.mk (sourceLabelEdgeSetoid src label) e
      rw [eEquiv.symm_apply_apply]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h f =>
      change Quotient.mk (sourceLabelEdgeSetoid tgtSrc tgtLabel)
        (eEquiv (eEquiv.symm f)) =
        Quotient.mk (sourceLabelEdgeSetoid tgtSrc tgtLabel) f
      rw [eEquiv.apply_symm_apply]

/-- The quotient equivalence maps each raw oriented signed edge
to the EXACT quotient class of its image, keeping the already
glued vertex source and signed label unchanged. -/
@[simp] theorem sourceLabelEdgeQuotientEquiv_mk
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (src : E → V) (tgtSrc : F → W)
    (label : E → Label) (tgtLabel : F → Label)
    (hsrc : ∀ e, tgtSrc (eEquiv e) = vEquiv (src e))
    (hlabel : ∀ e, tgtLabel (eEquiv e) = label e)
    (e : E) :
    sourceLabelEdgeQuotientEquiv vEquiv eEquiv
      src tgtSrc label tgtLabel hsrc hlabel
      (Quotient.mk (sourceLabelEdgeSetoid src label) e) =
    Quotient.mk (sourceLabelEdgeSetoid tgtSrc tgtLabel) (eEquiv e) :=
  rfl

end ABO
end PSTSEPPA
