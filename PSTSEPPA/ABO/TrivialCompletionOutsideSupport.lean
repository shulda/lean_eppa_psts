import PSTSEPPA.ABO.TrivialLoopCompletion
import PSTSEPPA.ABO.CosetConnectivity

/-!
# Trivial completion is stationary outside the original edge alphabet

The corrected ABO Section 5 adjoins only missing signed-label
loops when passing from a weakly complete EGraph to its complete
action. If every G-edge has underlying label in A, then each
label outside A is missing at EVERY vertex, and the completion
acts by the identity permutation on those labels.

We prove the stronger direct signed-word version: for EVERY
subalphabet C disjoint from A, every signed C-word fixes
EVERY completed vertex, irrespective of its ambient group
evaluation. This covers inverse letters, empty C, geometric
loops and repeated/trivial generators.

The lemma is deliberately stated for a generic EGraph with
an EXPLICIT edge-label support premise. Applying it to the
actual ABO full coset extensions and augmented stages requires
separate proof that their genuine edges are all A-labelled.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V Edge ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : EGraph V Edge ι)

/-- An outgoing signed label outside A is literally missing
at every vertex when all real edges have labels in A. -/
theorem no_outside_label_edge
    (A : Finset ι)
    (hSupport : ∀ e : Edge, signedBase (G.label e) ∈ A)
    (s : SignedLabel ι)
    (hsOutside : signedBase s ∉ A)
    (x : V) :
    ¬ ∃ e : Edge, G.source e = x ∧ G.label e = s := by
  rintro ⟨e, _, hlabel⟩
  apply hsOutside
  rw [← hlabel]
  exact hSupport e

/-- In the actual loop-only completed action, a signed label
outside all old edge support fixes every point. -/
theorem trivialLoopCompletion_outside_label_fixes
    (A : Finset ι)
    (hSupport : ∀ e : Edge, signedBase (G.label e) ∈ A)
    (hpaired : G.LocallyPairedLabels)
    (s : SignedLabel ι)
    (hsOutside : signedBase s ∉ A)
    (x : V) :
    (G.trivialLoopCompletion hpaired).target
      ((G.trivialLoopCompletion hpaired).edgeAt x s) = x := by
  let T := G.trivialLoopCompletion hpaired
  have hedge : T.edgeAt x s = (x, s) := by
    exact actionGraph.edgeAt (G.loopCompletedPermutation hpaired) x s
  rw [hedge]
  exact G.trivialLoopCompletion_loop_of_missing hpaired x s
    (G.no_outside_label_edge A hSupport s hsOutside x)

/-- Every word supported in C disjoint from the entire
old edge alphabet A acts trivially on every vertex of
the LEGAL loop-only completion. No ambient evaluation
hypothesis is needed. -/
theorem trivialLoopCompletion_disjoint_word_fixes
    (A C : Finset ι)
    (hSupport : ∀ e : Edge, signedBase (G.label e) ∈ A)
    (hpaired : G.LocallyPairedLabels)
    (hdis : Disjoint C A)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (x : V) :
    (G.trivialLoopCompletion hpaired).followWord x w = x := by
  let T := G.trivialLoopCompletion hpaired
  induction w generalizing x with
  | nil => rfl
  | cons s w ih =>
      have hsOutside : signedBase s ∉ A := by
        intro hsA
        exact (Finset.disjoint_left.mp hdis) hw.1 hsA
      have hstep : T.target (T.edgeAt x s) = x :=
        G.trivialLoopCompletion_outside_label_fixes
          A hSupport hpaired s hsOutside x
      rw [T.followWord_cons, hstep]
      exact ih (x := x) hw.2

end EGraph
end ABO
end PSTSEPPA
