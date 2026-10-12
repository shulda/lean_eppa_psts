import PSTSEPPA.ABO.SourceLabelEdgeQuotientIncidence
import PSTSEPPA.ABO.Graph

/-!
# Exact signed source-and-label edge quotients as conditional E-graphs

The raw oriented edge equivalence in ABO identifies edges with the same
GLUED source and identical SIGNED label. This alone does not imply that
their targets are the same tagged quotient vertex. We therefore make
target congruence an EXPLICIT hypothesis before descending edge reversal.

Once it holds, the exact quotient is a deterministic ABO E-graph, with
two distinct oriented edge tokens even for geometric loops. The resulting
graph is functorial for genuine bijective source/label/inversion-preserving
maps of the original tagged raw edges. This abstract lemma applies without
assuming the ambient source group is globally retractable.

The source-specific target congruence and actual multi-coset raw edge
transport are separate mathematical obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {V E ι : Type*}

/-- The genuine source/label-to-target congruence needed to form
an E-graph from the exact quotient of directed signed edge tokens. -/
def LabelledGraph.SourceLabelTargetCongruent
    (G : LabelledGraph V E ι) : Prop :=
  ∀ e f : E,
    G.source e = G.source f →
    G.label e = G.label f →
    G.target e = G.target f

/-- Under target congruence, formal reversal preserves the raw
source-and-signed-label setoid, so it descends to the quotient. -/
noncomputable def sourceLabelGraphQuotientInv
    (G : LabelledGraph V E ι)
    (hcongr : G.SourceLabelTargetCongruent) :
    Quotient (sourceLabelEdgeSetoid G.source G.label) →
      Quotient (sourceLabelEdgeSetoid G.source G.label) :=
  fun q => Quotient.liftOn q
    (fun e => Quotient.mk _ (G.inv e))
    (by
      intro e f hef
      apply Quotient.sound
      constructor
      · change G.target e = G.target f
        exact hcongr e f hef.1 hef.2
      · calc
          G.label (G.inv e) =
              PSTS.SignedLetter.inv (G.label e) := G.label_inv e
          _ = PSTS.SignedLetter.inv (G.label f) :=
            congrArg PSTS.SignedLetter.inv hef.2
          _ = G.label (G.inv f) := (G.label_inv f).symm)

/-- Reversal of a raw directed token is represented by the
original formal inverse token (no component-tag collapsing). -/
@[simp] theorem sourceLabelGraphQuotientInv_mk
    (G : LabelledGraph V E ι)
    (hcongr : G.SourceLabelTargetCongruent) (e : E) :
    sourceLabelGraphQuotientInv G hcongr
      (Quotient.mk (sourceLabelEdgeSetoid G.source G.label) e) =
      Quotient.mk (sourceLabelEdgeSetoid G.source G.label) (G.inv e) :=
  rfl

/-- Exact signed edge quotient, promoted to a deterministic E-graph
precisely when source/label-to-target congruence holds. -/
noncomputable def sourceLabelGraphQuotientEGraph
    (G : LabelledGraph V E ι)
    (hcongr : G.SourceLabelTargetCongruent) :
    EGraph V (Quotient (sourceLabelEdgeSetoid G.source G.label)) ι where
  toLabelledGraph := {
    source := sourceLabelEdgeQuotientSource G.source G.label
    inv := sourceLabelGraphQuotientInv G hcongr
    inv_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | h e =>
        change Quotient.mk (sourceLabelEdgeSetoid G.source G.label)
          (G.inv (G.inv e)) =
          Quotient.mk (sourceLabelEdgeSetoid G.source G.label) e
        rw [G.inv_inv]
    inv_ne := by
      intro q
      induction q using Quotient.inductionOn with
      | h e =>
        intro h
        have hl := congrArg
          (sourceLabelEdgeQuotientLabel G.source G.label) h
        change G.label (G.inv e) = G.label e at hl
        rw [G.label_inv e] at hl
        cases hs : G.label e with
        | pos i =>
          rw [hs] at hl
          cases hl
        | neg i =>
          rw [hs] at hl
          cases hl
    label := sourceLabelEdgeQuotientLabel G.source G.label
    label_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | h e =>
        change G.label (G.inv e) =
          PSTS.SignedLetter.inv (G.label e)
        exact G.label_inv e
  }
  deterministic := by
    intro q r hsrc hlabel
    induction q using Quotient.inductionOn with
    | h e =>
      induction r using Quotient.inductionOn with
      | h f =>
        apply Quotient.sound
        exact ⟨hsrc, hlabel⟩

/-- The exact edge quotient preserves the entire target incidence
of each true raw edge. This result does not assume completeness. -/
theorem sourceLabelGraphQuotientEGraph_target_mk
    (G : LabelledGraph V E ι)
    (hcongr : G.SourceLabelTargetCongruent) (e : E) :
    (sourceLabelGraphQuotientEGraph G hcongr).target
      (Quotient.mk (sourceLabelEdgeSetoid G.source G.label) e) =
    G.target e := by
  change G.source (G.inv e) = G.target e
  rfl

variable {W F : Type*}

/-- The inverse-edge transport commutes with the induced quotient
equivalence. We never assume the raw edge map comes from an ambient
group coordinate: it must preserve actual formal reversal. -/
theorem sourceLabelGraphQuotientInv_natural
    (G : LabelledGraph V E ι) (H : LabelledGraph W F ι)
    (vEquiv : V ≃ W) (eEquiv : E ≃ F)
    (hsrc : ∀ e, H.source (eEquiv e) = vEquiv (G.source e))
    (hlabel : ∀ e, H.label (eEquiv e) = G.label e)
    (hG : G.SourceLabelTargetCongruent)
    (hH : H.SourceLabelTargetCongruent)
    (hinv : ∀ e, H.inv (eEquiv e) = eEquiv (G.inv e))
    (q : Quotient (sourceLabelEdgeSetoid G.source G.label)) :
    sourceLabelGraphQuotientInv H hH
      (sourceLabelEdgeQuotientEquiv vEquiv eEquiv
        G.source H.source G.label H.label hsrc hlabel q) =
    sourceLabelEdgeQuotientEquiv vEquiv eEquiv
      G.source H.source G.label H.label hsrc hlabel
      (sourceLabelGraphQuotientInv G hG q) := by
  induction q using Quotient.inductionOn with
  | h e =>
    change
      Quotient.mk (sourceLabelEdgeSetoid H.source H.label)
        (H.inv (eEquiv e)) =
      Quotient.mk (sourceLabelEdgeSetoid H.source H.label)
        (eEquiv (G.inv e))
    rw [hinv]

end ABO
end PSTSEPPA
