import PSTSEPPA.ABO.SourceLiteralY1SelectedType2NamedSourceStageAgreement

/-!
# Dependent equality for completed isolated cosets under both anchor and root changes

The vertex carrier of a genuine completed B-left-coset augmentation
depends on its ambient group anchor, whereas the graph itself
remembers its OLD tagged glued root. To compare two descriptions
of the exact same completed signed structure, it is mathematically
necessary to preserve BOTH data, not merely ambient coset values.

If the two group anchors coincide and the two old vertex roots
coincide, then the genuinely completed signed actions agree as
dependent objects (HEq), independently of the proof terms
establishing absence of old B-labelled edges and local
signed-label pairing. This is PROOF IRRELEVANCE, not a quotient
or an identification of old vertices sharing ambient coordinates.

Unlike eliminating a concrete equality between complex group
expressions inside a dependent source-stage goal, the proof
eliminates equalities of abstract anchor/root variables and
therefore has a stable source-facing API.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {ι V Γ OldEdge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Correct heterogeneous equality of LEGALLY completed original
old+fresh signed B-augmentations when BOTH the true ambient
group coordinate and selected OLD quotient vertex agree. -/
theorem completedStage_heq_of_anchor_and_root_eq
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι)
    {g h : Γ} (hgh : g = h)
    {u v : V} (huv : u = v)
    (hMissingG : ∀ e : OldEdge,
      G.source e = u → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : OldEdge,
      G.source e = v → signedBase (G.label e) ∉ B)
    (hPairedG hPairedH : G.LocallyPairedLabels) :
    HEq
      (completedStage G gen B g u hMissingG hPairedG)
      (completedStage G gen B h v hMissingH hPairedH) := by
  cases hgh
  cases huv
  rfl

end IsolatedCosetGluing
end ABO
end PSTSEPPA
