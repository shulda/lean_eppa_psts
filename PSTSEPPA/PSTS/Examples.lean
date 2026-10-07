import PSTSEPPA.PSTS.PartialAut
import Mathlib.Data.Fin.Basic

/-!
# Gate T0 regression examples

Tiny examples validating the PSTS, closed-substructure and partial-automorphism
API before beginning the word and MAX layers.
-/

namespace PSTSEPPA
namespace PSTS
namespace Examples

/-- The PSTS with no non-diagonal triples. -/
def discrete (V : Type*) [DecidableEq V] : PSTS V where
  op x y := if x = y then some x else none
  diag x := by simp
  symm x y := by
    by_cases h : x = y
    · subst y
      rfl
    · have h' : y ≠ x := Ne.symm h
      simp [h, h']
  steiner_left := by
    intro x y z hxyz
    by_cases hxy : x = y
    · subst y
      simp at hxyz
      subst z
      simp
    · simp [hxy] at hxyz

/-- Explicit zero-point regression system. -/
def zeroPoint : PSTS (Fin 0) := discrete (Fin 0)

/-- Explicit one-point regression system. -/
def onePoint : PSTS (Fin 1) := discrete (Fin 1)

/-- Explicit two-point regression system. -/
def twoPoint : PSTS (Fin 2) := discrete (Fin 2)

/-- Three named points supporting one Steiner triple. -/
inductive TriplePoint
  | a | b | c
  deriving DecidableEq

open TriplePoint

/-- The total Steiner quasigroup operation on one 3-point block. -/
def tripleOp : TriplePoint → TriplePoint → Option TriplePoint
  | a, a => some a
  | a, b => some c
  | a, c => some b
  | b, a => some c
  | b, b => some b
  | b, c => some a
  | c, a => some b
  | c, b => some a
  | c, c => some c

/-- The PSTS consisting of one Steiner triple. -/
def oneTriple : PSTS TriplePoint where
  op := tripleOp
  diag x := by cases x <;> rfl
  symm x y := by cases x <;> cases y <;> rfl
  steiner_left := by
    intro x y z hxyz
    cases x <;> cases y <;>
      simp only [tripleOp, Option.some.injEq] at hxyz ⊢ <;>
      subst z <;> rfl

/-- Every singleton in the one-triple PSTS is closed. -/
example (p : TriplePoint) : oneTriple.Closed ({p} : Set TriplePoint) :=
  oneTriple.closed_singleton p

/-- Two vertices of the unique block do not form a closed subset. -/
theorem oneTriple_ab_not_closed :
    ¬ oneTriple.Closed ({a, b} : Set TriplePoint) := by
  intro h
  have hc : c ∈ ({a, b} : Set TriplePoint) :=
    h (x := a) (y := b) (z := c) (by simp) (by simp) (by rfl)
  simp at hc

/-- A genuinely partial automorphism: it is defined only at `a` and sends it
to `b`. -/
def singletonAB : PartialAut oneTriple :=
  PartialAut.single oneTriple a b

@[simp]
theorem singletonAB_at_a : singletonAB.toPEquiv a = some b :=
  PEquiv.single_apply a b

@[simp]
theorem singletonAB_at_c : singletonAB.toPEquiv c = none :=
  PEquiv.single_apply_of_ne (by decide) b

end Examples
end PSTS
end PSTSEPPA
