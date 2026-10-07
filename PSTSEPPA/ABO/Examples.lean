import PSTSEPPA.ABO.Transition

/-!
# Regression examples for the ABO graph conventions
-/

namespace PSTSEPPA
namespace ABO
namespace Examples

/-- Two distinct labels on a one-point complete action graph.  All edges are
geometric loops and both positive generators induce the identity permutation.
This simultaneously checks that loops are allowed, inverse edge tokens remain
distinct, and the generator assignment need not be injective. -/
inductive LoopEdge where
  | apos | aneg | bpos | bneg
  deriving DecidableEq

def loopInv : LoopEdge → LoopEdge
  | .apos => .aneg
  | .aneg => .apos
  | .bpos => .bneg
  | .bneg => .bpos

def loopLabel : LoopEdge → SignedLabel Bool
  | .apos => .pos false
  | .aneg => .neg false
  | .bpos => .pos true
  | .bneg => .neg true

def twoTrivialGenerators : CompleteEGraph Unit LoopEdge Bool where
  source _ := ()
  inv := loopInv
  inv_inv := by
    intro e
    cases e <;> rfl
  inv_ne := by
    intro e
    cases e <;> decide
  label := loopLabel
  label_inv := by
    intro e
    cases e <;> rfl
  deterministic := by
    intro e f _ hlabel
    cases e <;> cases f <;> simp_all [loopLabel]
  complete := by
    intro u s
    rcases u with ⟨⟩
    cases s with
    | pos i =>
        cases i
        · exact ⟨.apos, rfl, rfl⟩
        · exact ⟨.bpos, rfl, rfl⟩
    | neg i =>
        cases i
        · exact ⟨.aneg, rfl, rfl⟩
        · exact ⟨.bneg, rfl, rfl⟩

example :
    twoTrivialGenerators.transitionGenerator false =
      twoTrivialGenerators.transitionGenerator true := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro u
  cases u
  rfl

example :
    twoTrivialGenerators.transitionGenerator false = 1 := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro u
  cases u
  rfl

example (w : LabelWord Bool) :
    CompleteEGraph.rightApply (twoTrivialGenerators.wordValue w) () = () := by
  cases CompleteEGraph.rightApply_wordValue twoTrivialGenerators w ()
  rfl

end Examples
end ABO
end PSTSEPPA
