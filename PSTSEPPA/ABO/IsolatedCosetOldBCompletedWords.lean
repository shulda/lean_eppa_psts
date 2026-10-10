import PSTSEPPA.ABO.IsolatedCosetOldBPaths
import PSTSEPPA.ABO.TrivialLoopCompletion

/-!
# Exact B-word action of a glued coset stage away from the attachment root

For the corrected ABO Proposition 5.4 type-(2) rank-one base, we must
compare TRUE COMPLETE signed-word actions, not only reachability.

Assume a full B-coset is attached at an old EGraph vertex root with NO
old signed B-edge. For any other old vertex x and any B-signed letter,
the loop-completed glued graph takes precisely the same step as the
loop-completed old graph, embedded into the old summand. Moreover its
old endpoint cannot become root. This is a real one-step calculation
using the old/new oriented edge tokens and the precise missing-edge
case, not a claim of global morphism between complete action graphs
(which would be FALSE at the attachment root).

Induction on the signed word gives exact componentwise B-word action
at every old vertex other than root; this is the missing counterpart
to the kernel theorem for vertices of the new attached full B-coset.

The input pairing hypotheses are explicit so that this lemma does
not assume local pairing for arbitrary EGraphs. The actual rank-two
multi-CE satisfies them by the already certified weak-completeness
and glued-pairing theorems.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- For any locally paired EGraph, the single signed step of
its genuine loop-only completion is exactly the step of its
underlying partial graph, extended by identity at missing labels. -/
theorem loopCompletion_target_edgeAt
    {W F : Type*}
    (H : EGraph W F ι) (hpaired : H.LocallyPairedLabels)
    (x : W) (s : SignedLabel ι) :
    (H.trivialLoopCompletion hpaired).target
      ((H.trivialLoopCompletion hpaired).edgeAt x s) =
        H.loopCompletedStep s x := by
  have hedge :
      (H.trivialLoopCompletion hpaired).edgeAt x s = (x,s) := by
    change (actionGraph (H.loopCompletedPermutation hpaired)).edgeAt
      x s = (x,s)
    exact actionGraph.edgeAt _ x s
  rw [hedge]
  cases s <;> rfl

/-- Each signed B-letter acts on an old NON-ROOT vertex in
the glued loop-completed partial action exactly as in the
original loop-completed partial action. Its old endpoint
stays outside the root, even when original B-edges are loops
or some generator transitions are missing. -/
theorem glued_B_loopCompletedStep_old_ne_root
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (x : V) (hne : x ≠ root)
    (s : SignedLabel ι) (hs : signedBase s ∈ B) :
    (gluedEGraph G gen B g root hMissing).loopCompletedStep
        s (Sum.inl x) =
      Sum.inl (G.loopCompletedStep s x) ∧
    G.loopCompletedStep s x ≠ root := by
  classical
  let H := gluedEGraph G gen B g root hMissing
  by_cases hOld : ∃ e : OldEdge,
      G.source e = x ∧ G.label e = s
  · obtain ⟨e, hes, hel⟩ := hOld
    have hNew :
        H.loopCompletedStep s (Sum.inl x) =
          H.target (Sum.inl e) :=
      H.loopCompletedStep_of_edge s (Sum.inl x) (Sum.inl e)
        (congrArg Sum.inl hes) hel
    have hOriginal :
        G.loopCompletedStep s x = G.target e :=
      G.loopCompletedStep_of_edge s x e hes hel
    constructor
    · rw [hNew, hOriginal]
      rfl
    · rw [hOriginal]
      have hB : signedBase (G.label e) ∈ B := by
        rw [hel]
        exact hs
      exact old_B_edge_target_ne_root G B root hMissing e hB
  · have hNewMissing :
        ¬ ∃ e : Edge OldEdge gen B g,
          H.source e = Sum.inl x ∧ H.label e = s := by
      rintro ⟨e, heSource, heLabel⟩
      cases e with
      | inl e =>
          apply hOld
          exact ⟨e, Sum.inl.inj heSource, heLabel⟩
      | inr e =>
          have hxroot : x = root :=
            gluePoint_inl_eq_root gen B g root x
              ⟨(cayleyGraph gen).source e.1, e.2.1⟩ heSource
          exact hne hxroot
    have hNew :
        H.loopCompletedStep s (Sum.inl x) = Sum.inl x :=
      H.loopCompletedStep_of_missing s (Sum.inl x) hNewMissing
    have hOriginal :
        G.loopCompletedStep s x = x :=
      G.loopCompletedStep_of_missing s x hOld
    constructor
    · rw [hNew, hOriginal]
    · rw [hOriginal]
      exact hne

/-- Precise signed B-word transport outside the attachment
root, for the ACTUAL loop-only completions on both sides.
No word step may move into root: the B-invariant off-root
old component is therefore unchanged as an action, not
just unchanged as a connectivity relation. -/
theorem glued_B_completed_followWord_old_ne_root
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpairedOld : G.LocallyPairedLabels)
    (hpairedNew :
      (gluedEGraph G gen B g root hMissing).LocallyPairedLabels)
    (x : V) (hne : x ≠ root)
    (w : LabelWord ι)
    (hw : LabelWord.Uses B w) :
    ((gluedEGraph G gen B g root hMissing).trivialLoopCompletion
      hpairedNew).followWord (Sum.inl x) w =
      Sum.inl ((G.trivialLoopCompletion hpairedOld).followWord x w) ∧
    (G.trivialLoopCompletion hpairedOld).followWord x w ≠ root := by
  let H := gluedEGraph G gen B g root hMissing
  let T := H.trivialLoopCompletion hpairedNew
  let S := G.trivialLoopCompletion hpairedOld
  induction w generalizing x with
  | nil =>
      exact ⟨rfl, hne⟩
  | cons s w ih =>
      obtain ⟨hStep, hStepNonroot⟩ :=
        glued_B_loopCompletedStep_old_ne_root G gen B g root
          hMissing x hne s hw.1
      obtain ⟨hTail, hTailNonroot⟩ :=
        ih (x := G.loopCompletedStep s x) hStepNonroot hw.2
      have hTStep :
          T.target (T.edgeAt (Sum.inl x) s) =
            Sum.inl (G.loopCompletedStep s x) := by
        rw [loopCompletion_target_edgeAt H hpairedNew]
        exact hStep
      have hSStep :
          S.target (S.edgeAt x s) =
            G.loopCompletedStep s x :=
        loopCompletion_target_edgeAt G hpairedOld x s
      constructor
      · change T.followWord (Sum.inl x) (s :: w) =
          Sum.inl (S.followWord x (s :: w))
        rw [T.followWord_cons, S.followWord_cons,
          hTStep, hSStep]
        exact hTail
      · change S.followWord x (s :: w) ≠ root
        rw [S.followWord_cons, hSStep]
        exact hTailNonroot

end IsolatedCosetGluing
end ABO
end PSTSEPPA
