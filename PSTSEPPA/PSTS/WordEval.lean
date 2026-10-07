import PSTSEPPA.PSTS.PartialAut

/-!
# Signed words and partial evaluation

A signed word records a sequence of chosen partial automorphisms and formal
inverses.  Evaluation follows the convention fixed in Gate T0:
`p.trans q` means first apply `p`, then `q`.
-/

namespace PSTSEPPA
namespace PSTS

/-- A generator or its formal inverse. -/
inductive SignedLetter (ι : Type*) where
  | pos : ι → SignedLetter ι
  | neg : ι → SignedLetter ι
  deriving DecidableEq

namespace SignedLetter

variable {ι : Type*}

/-- Formal inverse of a signed letter. -/
def inv : SignedLetter ι → SignedLetter ι
  | pos i => neg i
  | neg i => pos i

@[simp]
theorem inv_pos (i : ι) : inv (pos i) = neg i :=
  rfl

@[simp]
theorem inv_neg (i : ι) : inv (neg i) = pos i :=
  rfl

@[simp]
theorem inv_inv (s : SignedLetter ι) : inv (inv s) = s := by
  cases s <;> rfl

end SignedLetter

/-- A finite signed word. -/
abbrev SignedWord (ι : Type*) :=
  List (SignedLetter ι)

namespace SignedWord

variable {V ι : Type*} {A : PSTS V}

/-- Evaluate one signed letter as a partial automorphism. -/
def evalLetter (gen : ι → PartialAut A) : SignedLetter ι → PartialAut A
  | .pos i => gen i
  | .neg i => (gen i).symm

@[simp]
theorem evalLetter_pos (gen : ι → PartialAut A) (i : ι) :
    evalLetter gen (.pos i) = gen i :=
  rfl

@[simp]
theorem evalLetter_neg (gen : ι → PartialAut A) (i : ι) :
    evalLetter gen (.neg i) = (gen i).symm :=
  rfl

@[simp]
theorem evalLetter_inv (gen : ι → PartialAut A) (s : SignedLetter ι) :
    evalLetter gen s.inv = (evalLetter gen s).symm := by
  cases s <;> simp [evalLetter, SignedLetter.inv]

/-- Evaluate a word from left to right.  Thus `[s, t]` means first `s`,
then `t`. -/
def eval (gen : ι → PartialAut A) : SignedWord ι → PartialAut A
  | [] => PartialAut.refl A
  | s :: w => (evalLetter gen s).trans (eval gen w)

@[simp]
theorem eval_nil (gen : ι → PartialAut A) :
    eval gen [] = PartialAut.refl A :=
  rfl

@[simp]
theorem eval_cons (gen : ι → PartialAut A) (s : SignedLetter ι) (w : SignedWord ι) :
    eval gen (s :: w) = (evalLetter gen s).trans (eval gen w) :=
  rfl

@[simp]
theorem eval_singleton (gen : ι → PartialAut A) (s : SignedLetter ι) :
    eval gen [s] = evalLetter gen s := by
  simp [eval]

/-- Word concatenation matches composition in the same left-to-right order. -/
theorem eval_append (gen : ι → PartialAut A) (u v : SignedWord ι) :
    eval gen (u ++ v) = (eval gen u).trans (eval gen v) := by
  induction u with
  | nil =>
      simp
  | cons s u ih =>
      simp only [List.cons_append, eval_cons, ih]
      rw [← PartialAut.trans_assoc]

/-- Formal inverse word: reverse the order and invert every letter. -/
def inv : SignedWord ι → SignedWord ι
  | [] => []
  | s :: w => inv w ++ [s.inv]

@[simp]
theorem inv_nil : inv ([] : SignedWord ι) = [] :=
  rfl

@[simp]
theorem inv_cons (s : SignedLetter ι) (w : SignedWord ι) :
    inv (s :: w) = inv w ++ [s.inv] :=
  rfl

@[simp]
theorem inv_inv (w : SignedWord ι) : inv (inv w) = w := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      simp [inv, ih]

/-- Evaluation of the formal inverse word is the inverse partial automorphism. -/
theorem eval_inv (gen : ι → PartialAut A) (w : SignedWord ι) :
    eval gen (inv w) = (eval gen w).symm := by
  induction w with
  | nil =>
      simp [eval, inv]
  | cons s w ih =>
      rw [inv_cons, eval_append, ih]
      simp [eval, PartialAut.symm_trans_rev]

/-- The underlying partial equivalence of a word is obtained by composing the
underlying partial equivalences of its letters in exactly the same order. -/
theorem eval_toPEquiv_cons (gen : ι → PartialAut A) (s : SignedLetter ι)
    (w : SignedWord ι) :
    (eval gen (s :: w)).toPEquiv =
      (evalLetter gen s).toPEquiv.trans (eval gen w).toPEquiv :=
  rfl

end SignedWord

end PSTS
end PSTSEPPA
