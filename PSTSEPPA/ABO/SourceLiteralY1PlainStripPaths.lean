import PSTSEPPA.ABO.TrivialLoopCompletionStripPaths
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainStageIso

/-!
# No fictitious B-bridges from missing loops in literal printed P_A stages

Corrected ABO Theorem 4.7 (especially its bridge-freeness
clause) uses the B=∅ augmentation to cover the legally
completed PLAIN proper-coset extension, then projects a
B-labelled path into that complete stage. It is essential
to remove only the missing-label stationary loops before
reasoning in the genuine incomplete tagged-coset EGraph.

The preceding generic certified-or-pending stripping lemma
specialises HERE to the ACTUAL original-input, rooted,
rank-two, intersection-support-glued printed T(Y₁) P_A stage.
The resulting equivalence uses the EXACT SAME old quotient
vertex carrier, preserves both signs and every original edge,
and includes B=∅. No equality of ambient group coordinates
is used to identify distinct original component-tagged points.

This establishes the complete bridge proof's loop-stripping
PREPARATION only; genuine B-bridge freeness still requires the
cluster and augmentation arguments of repaired Theorem 4.7.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- A B-word path in the TRUE legally loop-completed printed
original P_A stage connects two selected tagged OLD quotient
vertices iff some (possibly shorter) B-word already connects
the exact same vertices in the TRUE incompletely labelled
old P_A coset-extension EGraph, not in X₁. -/
theorem sourceLiteralY1SelectedRootPlain_subalphabetFollows_iff
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (u v : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A))) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).toEGraph.Follows u w v) ↔
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (sourceLiteralY1SelectedRootCompletedEGraph
        src dst base A hcard root
        (allProperCosetFamily A)).Follows u w v) := by
  exact
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root
      (allProperCosetFamily A)).trivialLoopCompletion_subalphabetFollows_iff
        (sourceLiteralY1SelectedRootAllProper_locallyPaired
          src dst base A hcard root) B u v

end ABO
end PSTSEPPA
