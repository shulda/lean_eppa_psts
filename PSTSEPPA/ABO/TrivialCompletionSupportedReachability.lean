import PSTSEPPA.ABO.TrivialCompletionOutsideSupport
import PSTSEPPA.ABO.LocalRankRetractableSubalphabet
import PSTSEPPA.ABO.Reachability

/-!
# Full signed-word reachability is preserved by restricting to real edge support

Let G be a genuine incomplete signed deterministic EGraph whose
old directed signed edges use only positive generators in A.
Its LEGAL missing-loop completion does not move a vertex under
any generator outside A, including formal inverse letters.

We prove a precise arbitrary-word strengthening: the completed
endpoint of every chronological signed word w agrees EXACTLY
with the endpoint of its actual A-restriction. Hence two vertices
are connected by SOME signed word in the whole completed action
if and only if they are joined by a genuine A-supported signed
word in that completed action.

Combined with the existing B-component classification of full
coset extensions, this gives the correct FULL connected-component
decomposition of source H₁ plain completed P_A stages by their
original A-component tags, not just B-reachability for prescribed B.
No equality of group coordinates identifies tagged quotient points.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V Edge ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable (G : EGraph V Edge ι)

/-- When genuine old edges are supported inside A,
following ANY signed word in the legally completed stage
is exactly the same as following its supported restriction
to A, including inverse labels and missing fixed loops. -/
theorem trivialLoopCompletion_followWord_restrictTo
    (A : Finset ι)
    (hSupport : ∀ e : Edge, signedBase (G.label e) ∈ A)
    (hpaired : G.LocallyPairedLabels)
    (x : V) (w : LabelWord ι) :
    (G.trivialLoopCompletion hpaired).followWord x w =
      (G.trivialLoopCompletion hpaired).followWord x
        (LabelWord.restrictTo A w) := by
  let T := G.trivialLoopCompletion hpaired
  induction w generalizing x with
  | nil => rfl
  | cons s w ih =>
      by_cases hs : signedBase s ∈ A
      · have hsOutside : signedBase s ∉ Finset.univ \ A := by
          simp [hs]
        have hRestrict :
            LabelWord.restrictTo A (s :: w) =
              s :: LabelWord.restrictTo A w := by
          simp [LabelWord.restrictTo, LabelWord.deleteGenerators, hsOutside]
        rw [hRestrict, T.followWord_cons, T.followWord_cons]
        exact ih (T.target (T.edgeAt x s))
      · have hsOutside : signedBase s ∈ Finset.univ \ A := by
          simp [hs]
        have hRestrict :
            LabelWord.restrictTo A (s :: w) =
              LabelWord.restrictTo A w := by
          simp [LabelWord.restrictTo, LabelWord.deleteGenerators, hsOutside]
        have hStep : T.target (T.edgeAt x s) = x :=
          G.trivialLoopCompletion_outside_label_fixes
            A hSupport hpaired s hs x
        rw [hRestrict, T.followWord_cons, hStep]
        exact ih x

/-- Entire COMPLETE signed-action reachability is precisely
reachability by some A-supported signed path. Distinct
components cannot be joined via labels outside A, since
those labels contribute only actual fixed-point loops. -/
theorem trivialLoopCompletion_reachable_iff_supported_path
    (A : Finset ι)
    (hSupport : ∀ e : Edge, signedBase (G.label e) ∈ A)
    (hpaired : G.LocallyPairedLabels)
    (x y : V) :
    (G.trivialLoopCompletion hpaired).Reachable x y ↔
      ∃ w : LabelWord ι,
        LabelWord.Uses A w ∧
          (G.trivialLoopCompletion hpaired).toEGraph.Follows x w y := by
  let T := G.trivialLoopCompletion hpaired
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨LabelWord.restrictTo A w,
      LabelWord.uses_restrictTo A w, ?_⟩
    have hEndpoint : T.followWord x (LabelWord.restrictTo A w) = y :=
      (G.trivialLoopCompletion_followWord_restrictTo
        A hSupport hpaired x w).symm.trans hw
    rw [← hEndpoint]
    exact T.follows_followWord x (LabelWord.restrictTo A w)
  · rintro ⟨w, _hw, hpath⟩
    refine ⟨w, ?_⟩
    exact T.toEGraph.follows_right_unique
      (T.follows_followWord x w) hpath

end EGraph
end ABO
end PSTSEPPA
