import PSTSEPPA.ABO.MultiCosetSignedParentSupport
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainStageIso
import PSTSEPPA.ABO.StageStabilityWordKernel

/-!
# The actual PRINTED rooted P_A stage fixes all signed labels outside A

This proof works with the exact component-tagged original-input
paper T(Y₁) root and its genuine old/fresh coset extension.
Its RAW oriented edge tokens have precisely the old source
A-labelled edges and fresh signed B-coset edges for B⊊A.
There is no additional old X₁ completion.

We prove every original RAW edge has signed base label in A.
This survives the exact SOURCE+SIGNED-LABEL edge quotient,
which does not manufacture any new edge label. Therefore
every actual label outside A is missing from the original
weakly-complete stage, and its LEGAL trivial loop completion
acts identically on each genuine tagged old/fresh vertex.

Conclude that each distinguished transition-group generator
outside A is precisely 1 in the ACTUAL complete signed
transition group. This is the missing source premise
for the independent full local G[A]-Cayley stage projection
lemma, combined with all-stage A-connectedness.

No ambient-coordinate tag identification, incorrect global
H-ambient embeddedness, equivariant exact Z₁ selection,
Theorem 4.7(iii), or PSTS EPPA is claimed here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Every ACTUAL RAW signed old/fresh edge in a selected
printed original-input rooted P_A multi-coset family
has its signed base label in A. In particular every
fresh B-edge uses B⊊A; the tagged gluing makes NO new labels. -/
theorem sourceLiteralY1SelectedRootRawGraph_label_mem_parent
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (e : (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawEdge P) :
    signedBase ((sourceLiteralY1SelectedRootRawGraph
      src dst base A hcard root P).label e) ∈ A := by
  rcases e with ⟨⟨B, hBP⟩, edge⟩
  change signedBase
    (((sourceLiteralY1DirectRootComponent src dst base A root).singleCosetEGraph B).label edge) ∈ A
  exact (sourceLiteralY1DirectRootComponent src dst base A root).
    singleCosetEdge_label_mem_parent B (P.proper B hBP).subset edge

/-- The actual full source+signed-label edge quotient of
the original printed P_A extension has NO real
edge whose signed base label lies outside A. -/
theorem sourceLiteralY1SelectedRootCompletedEGraph_label_mem_parent
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    ∀ e, signedBase ((sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root P).label e) ∈ A := by
  intro e
  induction e using Quotient.inductionOn with
  | h raw =>
      change signedBase ((sourceLiteralY1SelectedRootRawGraph
        src dst base A hcard root P).label raw) ∈ A
      exact sourceLiteralY1SelectedRootRawGraph_label_mem_parent
        src dst base A hcard root P raw

/-- Every actual signed label outside A is a FIXED
loop in the COMPLETE printed rooted P_A stage.
The statement includes every old and fresh quotient vertex. -/
theorem sourceLiteralY1SelectedRootPlain_outside_A_fixes
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (s : SignedLabel ι) (hs : signedBase s ∉ A)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A))) :
    (sourceLiteralY1SelectedRootPlainCompleteStage
      src dst base A hcard root).target
      ((sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).edgeAt u s) = u := by
  exact (sourceLiteralY1SelectedRootCompletedEGraph
    src dst base A hcard root (allProperCosetFamily A)).
      trivialLoopCompletion_outside_label_fixes
      A (sourceLiteralY1SelectedRootCompletedEGraph_label_mem_parent
        src dst base A hcard root (allProperCosetFamily A))
      (sourceLiteralY1SelectedRootAllProper_locallyPaired
        src dst base A hcard root) s hs u

/-- The full ACTUAL original printed P_A transition
subgroup generator for each i outside A equals ONE.
This is equality of the permutation action on all genuine
component-tagged old/fresh vertices, not just at a basepoint. -/
theorem sourceLiteralY1SelectedRootPlain_transitionOutsideA_one
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (i : ι) (hi : i ∉ A) :
    (sourceLiteralY1SelectedRootPlainCompleteStage
      src dst base A hcard root).transitionSubgroupGenerator i = 1 := by
  let T := sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root
  apply Subtype.ext
  change T.transitionGenerator i = (1 : RightPerm _)
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro u
  change T.target (T.edgeAt u (.pos i)) = u
  exact sourceLiteralY1SelectedRootPlain_outside_A_fixes
    src dst base A hcard root (.pos i) hi u

end ABO
end PSTSEPPA
