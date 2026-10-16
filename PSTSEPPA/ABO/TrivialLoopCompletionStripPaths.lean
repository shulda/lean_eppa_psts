import PSTSEPPA.ABO.TrivialLoopCompletion
import PSTSEPPA.ABO.Retractability

/-!
# Strip only added stationary loops from actual signed trivial completions

The corrected ABO Theorem 4.7 bridge-freeness proof projects a
B-labelled path into the legal trivial completion of an
INCOMPLETE EGraph, then must remove all ADDED stationary loops.

Here this is proved constructively for any locally paired
signed EGraph, including formal inverse signed tokens and
original genuine geometric loops:

* an existing signed edge is followed and retained;
* an absent signed edge is a fixed loop in the completion and
  its letter is deleted;
* the reduced chronological word uses no new label and
  is a TRUE path in the original incomplete graph, with
  precisely the same initial and final vertices.

Consequently the intrinsic B-connectivity relation is
unchanged by this particular completion, for ALL B, including
the empty alphabet. This is Step 1 of the corrected bridge
argument. It does NOT prove the subsequent cluster, embedding,
or bridge-free transport required for Theorem 4.7.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V Edge ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable (G : EGraph V Edge ι)

/-- Actual signed one-letter step in legal trivial completion
is exactly the original signed partial step if available,
otherwise it fixes its source. -/
theorem trivialLoopCompletion_target_pair
    (hpaired : G.LocallyPairedLabels)
    (u : V) (s : SignedLabel ι) :
    (G.trivialLoopCompletion hpaired).target (u, s) =
      G.loopCompletedStep s u := by
  cases s <;> rfl

/-- Exact chronological first step of the LEGALLY completed
signed EGraph; this is the only completion normalization
needed by the path-stripping recursion. -/
theorem trivialLoopCompletion_followWord_cons
    (hpaired : G.LocallyPairedLabels)
    (u : V) (s : SignedLabel ι) (w : LabelWord ι) :
    (G.trivialLoopCompletion hpaired).followWord u (s :: w) =
      (G.trivialLoopCompletion hpaired).followWord
        (G.loopCompletedStep s u) w := by
  let T := G.trivialLoopCompletion hpaired
  have hedge : T.edgeAt u s = (u, s) :=
    T.edgeAt_eq rfl rfl
  rw [T.followWord_cons, hedge]
  rw [G.trivialLoopCompletion_target_pair hpaired u s]

/-- For ANY completed signed chronological path, remove
precisely some newly added stationary-loop letters to obtain
a genuine OLD path with the SAME endpoints. The retained
word uses a subset of the original signed alphabet, so
this handles all bounded-support bridge paths. -/
theorem trivialLoopCompletion_stripWord
    (hpaired : G.LocallyPairedLabels)
    (u : V) (w : LabelWord ι) :
    ∃ q : LabelWord ι,
      (∀ B : Finset ι,
        LabelWord.Uses B w → LabelWord.Uses B q) ∧
      G.Follows u q
        ((G.trivialLoopCompletion hpaired).followWord u w) := by
  induction w generalizing u with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · intro B _
        exact LabelWord.uses_nil B
      · exact EGraph.Follows.nil u
  | cons s w ih =>
      have hstep :
          (G.trivialLoopCompletion hpaired).followWord u (s :: w) =
            (G.trivialLoopCompletion hpaired).followWord
              (G.loopCompletedStep s u) w :=
        G.trivialLoopCompletion_followWord_cons hpaired u s w
      by_cases hOld :
          ∃ e : Edge, G.source e = u ∧ G.label e = s
      · obtain ⟨e, hsrc, hlabel⟩ := hOld
        obtain ⟨q, hUses, hPath⟩ := ih (G.target e)
        refine ⟨s :: q, ?_, ?_⟩
        · intro B hWord
          exact ⟨hWord.1, hUses B hWord.2⟩
        · rw [hstep, G.loopCompletedStep_of_edge s u e hsrc hlabel]
          exact EGraph.Follows.cons e hsrc hlabel hPath
      · obtain ⟨q, hUses, hPath⟩ := ih u
        refine ⟨q, ?_, ?_⟩
        · intro B hWord
          exact hUses B hWord.2
        · rw [hstep, G.loopCompletedStep_of_missing s u hOld]
          exact hPath

/-- Every ACTUAL B-path in the LEGAL completion can be
replaced by a genuine B-path in the old incomplete EGraph.
Added fixed loops are not mistaken for original edge tokens. -/
theorem trivialLoopCompletion_stripFollows
    (hpaired : G.LocallyPairedLabels)
    (B : Finset ι) (u v : V)
    (w : LabelWord ι) (hUses : LabelWord.Uses B w)
    (hPath :
      (G.trivialLoopCompletion hpaired).toEGraph.Follows u w v) :
    ∃ q : LabelWord ι,
      LabelWord.Uses B q ∧ G.Follows u q v := by
  have hEndpoint :
      (G.trivialLoopCompletion hpaired).followWord u w = v :=
    (G.trivialLoopCompletion hpaired).toEGraph.follows_right_unique
      ((G.trivialLoopCompletion hpaired).follows_followWord u w)
      hPath
  obtain ⟨q, hqUses, hqPath⟩ :=
    G.trivialLoopCompletion_stripWord hpaired u w
  refine ⟨q, hqUses B hUses, ?_⟩
  rw [hEndpoint] at hqPath
  exact hqPath

/-- The proper-subalphabet connected components are IDENTICAL
before and after adding ONLY legally missing stationary signed
loops. In particular there are no artificial bridges from
those new edges, even for B=∅ or existing original loops. -/
theorem trivialLoopCompletion_subalphabetFollows_iff
    (hpaired : G.LocallyPairedLabels)
    (B : Finset ι) (u v : V) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (G.trivialLoopCompletion hpaired).toEGraph.Follows u w v) ↔
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      G.Follows u w v) := by
  constructor
  · rintro ⟨w, hUses, hPath⟩
    exact G.trivialLoopCompletion_stripFollows
      hpaired B u v w hUses hPath
  · rintro ⟨w, hUses, hPath⟩
    refine ⟨w, hUses, ?_⟩
    exact hPath.map (G.trivialLoopCompletionHom hpaired)

end EGraph
end ABO
end PSTSEPPA
