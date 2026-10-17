import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainStageIso
import PSTSEPPA.ABO.RootedSourceAllProperCompletedStageIso
import PSTSEPPA.ABO.KStableLocalGeneratedSubgroupQuotient

/-!
# Identify the literal PRINTED T(Y₁) P_A with the actual locally normalized H[A] stage

There are two independently constructed exact representations
of the true selected old T(Y₁) A-root's completed multi-coset stage.

* The LITERAL paper presentation uses the original incomplete
  T(Y₁) old A-component and the genuine intersection-supported
  quotient transported from SourceH₁ via its labelled isomorphism.
* The ABO local-normalization presentation begins with the SAME
  literal incomplete old T(Y₁) component but proves its exact
  setoid by translation into the generated subgroup H[A].

Both quotient relations are the SAME actual
  MultiCosetRawRelated P
on each pair of genuine component/alphabet-tagged raw vertices.
They MUST NOT be identified just because their ambient H group
coordinates coincide.

This file tests that these two independent proofs yield not just
equivalent cardinalities or group-coordinate projections but the
same component-tagged Setoid and therefore the SAME genuine
source+full-signed-label quotient and legal fixed-loop completion.

If the equality is certified by Lean, the already proved signed
local↔ambient rooted stage isomorphism can be composed with the
actual literal G[A] cover from PR #632 to discharge the next
source-facing first-rank Theorem 4.7(ii) coverage gate.
No full embedding, bridge-freeness, higher rank or PSTS EPPA
is asserted by this identification alone.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The TWO source-exact glued vertex quotients have LITERALLY
the same (B∩C)-supported relation, including distinct old
component tags with equal ambient group coordinates.
No global retractability of T(Y₁) is required. -/
theorem sourceLiteralY1SelectedRoot_setoid_eq_rootedAmbient
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root P =
    ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).rootedAmbientMultiCosetSetoid A hcard
        (sourceLiteralY1_transitionTwoRetractable src dst)
        (⟨root, by trivial⟩ :
          ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).Vertex)
        P := by
  rfl

/-- The same genuine old/fresh component-tagged signed
P_A completion is obtained from BOTH independent
corrected source constructions, including exact formal
oriented edge quotients and legally stationary loops.
Proof irrelevant Setoid witnesses cannot change the
resulting true source-labelled graph structure. -/
theorem sourceLiteralY1SelectedRootPlainStage_eq_rootedAmbient
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    sourceLiteralY1SelectedRootPlainCompleteStage
      src dst base A hcard root =
    ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).rootedAmbientAllProperCompletedStage A hcard
        (sourceLiteralY1_transitionTwoRetractable src dst)
        (⟨root, by trivial⟩ :
          ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).Vertex) := by
  rfl

end ABO
end PSTSEPPA
