import PSTSEPPA.ABO.IsolatedCosetOldBCompletedWords
import PSTSEPPA.ABO.IsolatedCosetDisjointPaths
import PSTSEPPA.ABO.IsolatedCosetCompletion

/-!
# Completed actions outside the attached coset's alphabet

A subtle, indispensable point in corrected ABO Proposition 5.4
at k=1: an augmented B-coset must preserve the identity-word
kernel for EVERY singleton alphabet C, not only C=B.

For a signed alphabet C disjoint from the attached B, a new
full B-coset introduces NO genuine C-labelled edge, so:
1. at every OLD point (INCLUDING THE ATTACHMENT ROOT), its
   completed C-step agrees exactly with the old completed C-step;
2. at every NEW point, all completed C-steps are literal LOOPS.

We prove this for actual signed labels and words, allowing
negative generators, old geometric loops and missing edges.
We deduce that any C-word acting trivially on the old complete
stage still fixes all vertices of the new completed augmented
stage. No group-value hypothesis is needed beyond the old
action's kernel, and no assumption of global morphism between
completed stages is used at the attached B labels.

This is the complementary rank-one kernel case to the
B-supported global singleton augmentation theorem.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- An added B-coset cannot change an outgoing C-transition
at ANY old vertex when C and B are disjoint. Missing old
C-edges remain missing; existing old C-edges are preserved. -/
theorem glued_disjoint_C_loopCompletedStep_old
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (C : Finset ι) (hdis : Disjoint C B)
    (x : V) (s : SignedLabel ι)
    (hs : signedBase s ∈ C) :
    (gluedEGraph G gen B g root hMissing).loopCompletedStep
        s (Sum.inl x) = Sum.inl (G.loopCompletedStep s x) := by
  classical
  let H := gluedEGraph G gen B g root hMissing
  by_cases hOld : ∃ e : OldEdge, G.source e = x ∧ G.label e = s
  · obtain ⟨e, heSrc, heLab⟩ := hOld
    have hNew :
        H.loopCompletedStep s (Sum.inl x) =
          H.target (Sum.inl e) :=
      H.loopCompletedStep_of_edge s (Sum.inl x) (Sum.inl e)
        (congrArg Sum.inl heSrc) heLab
    have hOriginal :
        G.loopCompletedStep s x = G.target e :=
      G.loopCompletedStep_of_edge s x e heSrc heLab
    rw [hNew, hOriginal]
    rfl
  · have hMissingNew :
        ¬ ∃ e : Edge OldEdge gen B g,
          H.source e = Sum.inl x ∧ H.label e = s := by
      rintro ⟨e, heSrc, heLab⟩
      have heC : signedBase (H.label e) ∈ C := by
        rw [heLab]
        exact hs
      obtain ⟨f, hf⟩ :=
        glued_C_edge_is_old G gen B g root hMissing C hdis e heC
      subst e
      exact hOld ⟨f, Sum.inl.inj heSrc, heLab⟩
    have hNew :
        H.loopCompletedStep s (Sum.inl x) = Sum.inl x :=
      H.loopCompletedStep_of_missing s (Sum.inl x) hMissingNew
    have hOriginal :
        G.loopCompletedStep s x = x :=
      G.loopCompletedStep_of_missing s x hOld
    rw [hNew, hOriginal]

/-- At each FRESH attached B-coset vertex, a C-step for
disjoint C is absent from the real incomplete graph,
hence the legal trivial completion makes it a loop. -/
theorem glued_disjoint_C_loopCompletedStep_fresh
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (C : Finset ι) (hdis : Disjoint C B)
    (q : FreshPoint gen B g) (s : SignedLabel ι)
    (hs : signedBase s ∈ C) :
    (gluedEGraph G gen B g root hMissing).loopCompletedStep
      s (Sum.inr q) = Sum.inr q := by
  let H := gluedEGraph G gen B g root hMissing
  apply H.loopCompletedStep_of_missing
  rintro ⟨e, heSrc, heLab⟩
  have heC : signedBase (H.label e) ∈ C := by
    rw [heLab]
    exact hs
  obtain ⟨f, hf⟩ :=
    glued_C_edge_is_old G gen B g root hMissing C hdis e heC
  subst e
  cases heSrc

/-- A C-supported signed word acts on every old point
exactly as in the old completed action, INCLUDING root,
as long as C is disjoint from the attached B. -/
theorem glued_disjoint_C_completed_followWord_old
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels)
    (C : Finset ι) (hdis : Disjoint C B)
    (x : V) (w : LabelWord ι)
    (hw : LabelWord.Uses C w) :
    (completedStage G gen B g root hMissing hpaired).followWord
        (Sum.inl x) w =
      Sum.inl ((G.trivialLoopCompletion hpaired).followWord x w) := by
  let H := gluedEGraph G gen B g root hMissing
  let hpNew : H.LocallyPairedLabels :=
    glued_locallyPairedLabels G gen B g root hMissing hpaired
  let T := completedStage G gen B g root hMissing hpaired
  let S := G.trivialLoopCompletion hpaired
  induction w generalizing x with
  | nil => rfl
  | cons s w ih =>
      have hStep :=
        glued_disjoint_C_loopCompletedStep_old
          G gen B g root hMissing C hdis x s hw.1
      have hTStep :
          T.target (T.edgeAt (Sum.inl x) s) =
            Sum.inl (G.loopCompletedStep s x) :=
        (loopCompletion_target_edgeAt H hpNew (Sum.inl x) s).trans hStep
      have hSStep :
          S.target (S.edgeAt x s) =
            G.loopCompletedStep s x :=
        loopCompletion_target_edgeAt G hpaired x s
      rw [T.followWord_cons, S.followWord_cons,
        hTStep, hSStep]
      exact ih (x := G.loopCompletedStep s x) hw.2

/-- Every C-word for C disjoint from B fixes EACH FRESH
B-coset point in the full trivial-loop completion. -/
theorem glued_disjoint_C_completed_followWord_fresh
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels)
    (C : Finset ι) (hdis : Disjoint C B)
    (q : FreshPoint gen B g) (w : LabelWord ι)
    (hw : LabelWord.Uses C w) :
    (completedStage G gen B g root hMissing hpaired).followWord
      (Sum.inr q) w = Sum.inr q := by
  let H := gluedEGraph G gen B g root hMissing
  let hpNew : H.LocallyPairedLabels :=
    glued_locallyPairedLabels G gen B g root hMissing hpaired
  let T := completedStage G gen B g root hMissing hpaired
  induction w with
  | nil => rfl
  | cons s w ih =>
      have hTStep :
          T.target (T.edgeAt (Sum.inr q) s) = Sum.inr q :=
        (loopCompletion_target_edgeAt H hpNew (Sum.inr q) s).trans
          (glued_disjoint_C_loopCompletedStep_fresh
            G gen B g root hMissing C hdis q s hw.1)
      rw [T.followWord_cons, hTStep]
      exact ih hw.2

/-- The identity-word kernel for disjoint alphabet C
is preserved by the completed singleton attachment,
AT EVERY OLD AND NEW VERTEX. Even old root is included. -/
theorem completedStage_disjoint_C_word_kernel
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels)
    (C : Finset ι) (hdis : Disjoint C B)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hOldKernel : ∀ x : V,
      (G.trivialLoopCompletion hpaired).followWord x w = x)
    (v : Vertex V gen B g) :
    (completedStage G gen B g root hMissing hpaired).followWord v w = v := by
  cases v with
  | inl x =>
      rw [glued_disjoint_C_completed_followWord_old
        G gen B g root hMissing hpaired C hdis x w hw]
      exact congrArg Sum.inl (hOldKernel x)
  | inr q =>
      exact glued_disjoint_C_completed_followWord_fresh
        G gen B g root hMissing hpaired C hdis q w hw

end IsolatedCosetGluing
end ABO
end PSTSEPPA
