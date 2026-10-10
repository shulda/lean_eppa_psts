import PSTSEPPA.ABO.CanonicalCover
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Perm

/-!
# Finiteness certificates for finite oriented ABO stages

The corrected ABO Section 5 builds finite transition groups from
finite complete directed E-graphs. It is important to certify the
types explicitly, rather than silently postulate a finite action
group for later k-stability/construction arguments.

Each positive generator i has TWO formal signed labels, +i and -i,
even when the corresponding action is a loop or trivial. The
signed-label type is equivalent to the disjoint sum ι⊕ι; hence
it is finite whenever the unsigned alphabet is finite.

The transition group of ANY complete EGraph on finite V is a
subgroup of the opposite permutation group Perm(V)^op, and thus
has a Fintype. This holds independently of the cardinality
of the edge token type and without injective generator labels.

This supplies finiteness for the actual complete stage
graphs and their literal disjoint sums. The remaining Section
5 construction/stability/cluster arguments are separate.
-/

namespace PSTSEPPA
namespace ABO

/-- The two oriented signed versions of every positive label
are exactly two disjoint copies of the positive label type. -/
def signedLabelEquivSum (ι : Type*) :
    SignedLabel ι ≃ (ι ⊕ ι) where
  toFun
    | .pos i => .inl i
    | .neg i => .inr i
  invFun
    | .inl i => .pos i
    | .inr i => .neg i
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro s
    cases s <;> rfl

/-- Finite positive alphabet implies FINITE positive/negative
signed label tokens, with no identification of a sign
even when the permutation generator is trivial. -/
noncomputable instance {ι : Type*} [Fintype ι] :
    Fintype (SignedLabel ι) :=
  Fintype.ofEquiv (ι ⊕ ι) (signedLabelEquivSum ι).symm

/-- The complete canonical action graph uses a finite
directed edge-token type on finite vertices and labels. -/
theorem finite_actionEdge
    {V ι : Type*} [Fintype V] [Fintype ι] :
    Finite (ActionEdge V ι) := by
  classical
  infer_instance

namespace CompleteEGraph

variable {V Edge ι : Type*}

/-- A complete EGraph on a finite carrier has a finite
transition group, regardless of whether some labels
induce identical permutations or act trivially. -/
noncomputable instance (T : CompleteEGraph V Edge ι)
    [Fintype V] :
    Fintype T.transitionGroup := by
  classical
  letI : Fintype (Equiv.Perm V) := inferInstance
  let e : Equiv.Perm V ≃ RightPerm V :=
    { toFun := MulOpposite.op
      invFun := MulOpposite.unop
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  letI : Fintype (RightPerm V) :=
    Fintype.ofEquiv (Equiv.Perm V) e
  exact Fintype.ofFinite _

/-- Finite-vertex complete graphs therefore give finite
transition groups as a proposition, ready for Section 5
without requiring an explicit enumeration. -/
theorem finite_transitionGroup
    (T : CompleteEGraph V Edge ι) [Fintype V] :
    Finite T.transitionGroup := by
  classical
  infer_instance

end CompleteEGraph
end ABO
end PSTSEPPA
