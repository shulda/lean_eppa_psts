import PSTSEPPA.ABO.UpwardInductionOriginalBComponentLoopActionInvariant

/-!
# Signed B-action on the OUTSIDE of one true original H B-component

The previous source-facing theorem proves that any original
incomplete H B-component and its complement are exactly
invariant under every legal completed positive/inverse
B-generator step. We now package the restriction of each
completed B-generator to the complement as a TRUE
permutation with its formal signed inverse.

This is not a merely set-theoretic preservation statement:
the resulting actual `Equiv.Perm` has explicit forward
and inverse functions matching exactly the original
stationary-loop-completed H signed actions.

It is the complementary half of the nonisolated ABO
Theorem 4.7(iii) whole-B-component action-amalgam plan:
a future complete stage will take the genuine unchanged
B-action on old vertices OUTSIDE the selected component
and the full H[B]-coset B-action INSIDE its replacement,
without identifying other old component tags.

No source H group-coordinate quotient, new old edges,
isolated-root assumption or custom axiom.
-/

namespace PSTSEPPA
namespace ABO
namespace EGraph

variable {V Edge ι : Type*}
variable [Fintype ι] [DecidableEq ι]

/-- A genuine permutation of the complement of ONE ORIGINAL
B-component induced by an old positive B-generator. Its
inverse is exactly the old negative signed generator,
including original old loops and legal missing-label
stationary loops. -/
noncomputable def loopCompletedOutsideBPermutation
    (G : EGraph V Edge ι)
    (hpaired : G.LocallyPairedLabels)
    (B : Finset ι) (anchor : V)
    (i : ι) (hi : i ∈ B) :
    Equiv.Perm {v : V // v ∉ G.BComponentVertexSet B anchor} where
  toFun v :=
    ⟨G.loopCompletedStep (.pos i) v.1,
      G.loopCompletedStep_outside_BComponent
        hpaired B anchor (.pos i) hi v.1 v.2⟩
  invFun v :=
    ⟨G.loopCompletedStep (.neg i) v.1,
      G.loopCompletedStep_outside_BComponent
        hpaired B anchor (.neg i) hi v.1 v.2⟩
  left_inv v := by
    apply Subtype.ext
    exact G.loopCompletedStep_inverse hpaired (.pos i) v.1
  right_inv v := by
    apply Subtype.ext
    exact G.loopCompletedStep_inverse hpaired (.neg i) v.1

/-- The restricted action uses EXACTLY the original old
completed positive B-step on the old group vertex. -/
theorem loopCompletedOutsideBPermutation_value
    (G : EGraph V Edge ι)
    (hpaired : G.LocallyPairedLabels)
    (B : Finset ι) (anchor : V)
    (i : ι) (hi : i ∈ B)
    (v : {v : V // v ∉ G.BComponentVertexSet B anchor}) :
    (G.loopCompletedOutsideBPermutation
      hpaired B anchor i hi v).1 =
      G.loopCompletedStep (.pos i) v.1 := rfl

/-- Likewise the inverse permutation is the actual original
negative signed B-step, not a postulated inverse edge. -/
theorem loopCompletedOutsideBPermutation_inv_value
    (G : EGraph V Edge ι)
    (hpaired : G.LocallyPairedLabels)
    (B : Finset ι) (anchor : V)
    (i : ι) (hi : i ∈ B)
    (v : {v : V // v ∉ G.BComponentVertexSet B anchor}) :
    ((G.loopCompletedOutsideBPermutation
      hpaired B anchor i hi).symm v).1 =
      G.loopCompletedStep (.neg i) v.1 := rfl

end EGraph
end ABO
end PSTSEPPA
