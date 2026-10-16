import PSTSEPPA.ABO.SourceLiteralY1X2AllPrintedPlainTransitionQuotient
import PSTSEPPA.ABO.TrivialLoopCompletionCayleyCosetBridge

/-!
# ACTUAL paper T(X₂-all) B-coset bridge lifting to OLD P_A extension

This is the first completely literal source-specific application
of the generic corrected ABO bridge-lifting mechanism.

Fix a TRUE original input basepoint, a two-letter alphabet A,
and an actual paper T(Y₁) root. The incomplete old stage is
the precise intersection-support glued P_A-coset extension of
the ORIGINAL signed edge preimage, retaining all original
B-component tags even when ambient group coordinates agree.

The actual labelled transition quotient
  T(X₂^all) -> T(complete(old rooted P_A stage))
has already been constructed; its genuine based Cayley graph
map reaches the desired old stage component on vertices AND
formal signed oriented edges.

If two group points g,h in the TRUE generated T(X₂^all) lie
in the same B-left coset, then their images under that actual
based Cayley projection are connected by a TRUE signed B-word
path in the INCOMPLETE old P_A extension. The proof projects
a group B-path and strips precisely the stationary loops
added by LEGAL completion; it never uses an imaginary X₁
old-edge completion or an ambient-value-injective quotient.

This says only that group-related points IN THE PROJECTED
CAYLEY IMAGE possess an OLD B-bridge. It is NOT yet the full
Definition-4.1/4.7 ambient Cayley embedding or bridge-free
induction of all actual Z₁/Yₖ components, nor PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The genuine original printed rooted P_A extension admits
a REAL B-labelled OLD path between the actual images of
two B-left-coset-related group points in T(X₂^all).
This holds for ALL B, including B=∅, both inverse
orientations and disconnected old source structures. -/
theorem sourceLiteralY1X2AllPrintedPlain_oldBCosetBridge
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A)))
    (B : Finset ι)
    (g h : (sourceLiteralY1X2AllStage src dst).transitionGroup)
    (hcoset :
      h ∈ generatedLeftCoset
        (sourceLiteralY1X2AllGenerator src dst) B g) :
    ∃ q : LabelWord ι,
      LabelWord.Uses B q ∧
      (sourceLiteralY1SelectedRootCompletedEGraph
        src dst base A hcard root
        (allProperCosetFamily A)).Follows
        ((sourceLiteralY1X2AllPrintedPlainCayleyHom
          src dst base A hcard root u).onVertex g)
        q
        ((sourceLiteralY1X2AllPrintedPlainCayleyHom
          src dst base A hcard root u).onVertex h) := by
  exact
    EGraph.trivialLoopCompletion_groupProjectionCoset_oldPath
      (sourceLiteralY1SelectedRootCompletedEGraph
        src dst base A hcard root (allProperCosetFamily A))
      (sourceLiteralY1SelectedRootAllProper_locallyPaired
        src dst base A hcard root)
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).hom
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).map_gen
      u B g h hcoset

end ABO
end PSTSEPPA
