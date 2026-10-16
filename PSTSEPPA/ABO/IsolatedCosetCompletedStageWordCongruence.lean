import PSTSEPPA.ABO.IsolatedCosetCompletedStageHEqNaturality

/-!
# Exact signed word-congruence transport for dependent isolated B-coset stages

The corrected ABO type-(2) completed signed action depends on TWO
separate pieces of data:
* the genuine OLD, component-tagged glued quotient root vertex;
* the group-coordinate anchor of the NEW full B-left coset.

One cannot deduce equality of old roots from ambient coordinates;
they have to be established independently. Once both the old-root
and the anchor equations are provided, we transport the ENTIRE
chronological signed-word action congruence between the ACTUAL
legally completed augmentations.

We intentionally abstract in both root and anchor coordinates
*before* eliminating their equalities, so Lean need never attempt
to decompose an HEq between two already-expanded dependent
CompleteEGraph carrier types. This is stronger and more stable
than transporting one path at a time, and the proof does not
postulate any new action, identify old tags, or assume global
retractability of the ambient group.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {ι V Γ OldEdge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- All chronological signed words have exactly the same
whole-stage action congruence before/after changing BOTH the
old selected vertex and the new B-coset group anchor by
actual equalities.

In particular this includes B=∅, formally oriented inverse
letters, and the fixed ±loops legally inserted by completion.
The two old-root values must be *equal tagged vertices*,
not merely points with equal ambient group coordinates. -/
theorem completedStage_wordActionCongr_iff_of_anchor_root_eq
    (G : EGraph V OldEdge ι) (gen : ι → Γ) (B : Finset ι)
    {g h : Γ} (hgh : g = h)
    {u v : V} (huv : u = v)
    (hMissingG : ∀ e : OldEdge,
      G.source e = u → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : OldEdge,
      G.source e = v → signedBase (G.label e) ∉ B)
    (hPairedG hPairedH : G.LocallyPairedLabels)
    (p q : LabelWord ι) :
    (∀ x : Vertex V gen B g,
      (completedStage G gen B g u hMissingG hPairedG).followWord x p =
      (completedStage G gen B g u hMissingG hPairedG).followWord x q) ↔
    (∀ y : Vertex V gen B h,
      (completedStage G gen B h v hMissingH hPairedH).followWord y p =
      (completedStage G gen B h v hMissingH hPairedH).followWord y q) := by
  cases hgh
  cases huv
  rfl

/-- Transfer the complete signed action of the actual LEGALLY
completed isolated B-coset under simultaneous old-root and
group-anchor identity. -/
theorem completedStage_wordActionCongr_of_anchor_root_eq
    (G : EGraph V OldEdge ι) (gen : ι → Γ) (B : Finset ι)
    {g h : Γ} (hgh : g = h)
    {u v : V} (huv : u = v)
    (hMissingG : ∀ e : OldEdge,
      G.source e = u → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : OldEdge,
      G.source e = v → signedBase (G.label e) ∉ B)
    (hPairedG hPairedH : G.LocallyPairedLabels)
    (p q : LabelWord ι)
    (hWord : ∀ x : Vertex V gen B g,
      (completedStage G gen B g u hMissingG hPairedG).followWord x p =
      (completedStage G gen B g u hMissingG hPairedG).followWord x q) :
    ∀ y : Vertex V gen B h,
      (completedStage G gen B h v hMissingH hPairedH).followWord y p =
      (completedStage G gen B h v hMissingH hPairedH).followWord y q :=
  (completedStage_wordActionCongr_iff_of_anchor_root_eq
    G gen B hgh huv hMissingG hMissingH hPairedG hPairedH p q).mp hWord

end IsolatedCosetGluing
end ABO
end PSTSEPPA
