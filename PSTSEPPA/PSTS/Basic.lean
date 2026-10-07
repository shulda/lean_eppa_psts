import Mathlib.Data.Option.Basic

/-!
# Partial Steiner triple systems

A partial Steiner triple system is represented by its partial binary operation.
Using `Option` keeps the representation close to the concrete partial-bijection
calculus used later in the MAX transfer.
-/

namespace PSTSEPPA

/-- A partial Steiner triple system on `V`, in functional form.

`op x y = some z` means that `{x,y,z}` is a (possibly diagonal) Steiner
triple. We store only one companion identity: the other follows from symmetry.
-/
structure PSTS (V : Type*) where
  op : V → V → Option V
  diag : ∀ x, op x x = some x
  symm : ∀ x y, op x y = op y x
  steiner_left : ∀ {x y z}, op x y = some z → op x z = some y

namespace PSTS

variable {V : Type*}

@[simp]
theorem op_self (A : PSTS V) (x : V) : A.op x x = some x :=
  A.diag x

theorem op_comm (A : PSTS V) (x y : V) : A.op x y = A.op y x :=
  A.symm x y

theorem steiner_right (A : PSTS V) {x y z : V} (h : A.op x y = some z) :
    A.op y z = some x := by
  apply A.steiner_left
  exact (A.symm y x).trans h

/-- The operation is defined on the ordered pair `(x,y)`. -/
def Defined (A : PSTS V) (x y : V) : Prop :=
  ∃ z, A.op x y = some z

@[simp]
theorem defined_self (A : PSTS V) (x : V) : A.Defined x x :=
  ⟨x, A.diag x⟩

theorem defined_comm (A : PSTS V) {x y : V} : A.Defined x y ↔ A.Defined y x := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, (A.symm y x).trans hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, (A.symm x y).trans hz⟩

/-- If an operation value coincides with its first argument, then the two
arguments already coincide. -/
theorem eq_of_op_eq_some_left (A : PSTS V) {x y : V} (h : A.op x y = some x) :
    y = x := by
  have hxy : (some x : Option V) = some y :=
    (A.diag x).symm.trans (A.steiner_left h)
  exact (Option.some.inj hxy).symm

/-- Symmetric version of `eq_of_op_eq_some_left`. -/
theorem eq_of_op_eq_some_right (A : PSTS V) {x y : V} (h : A.op x y = some y) :
    x = y := by
  apply A.eq_of_op_eq_some_left
  exact (A.symm y x).trans h

end PSTS

end PSTSEPPA
