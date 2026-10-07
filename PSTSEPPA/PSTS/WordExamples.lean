import PSTSEPPA.PSTS.Examples
import PSTSEPPA.PSTS.WordEval

/-!
# Gate T1 orientation regressions

These examples make the word convention executable on the one-block PSTS.
They also guard against the false simplification that a partial map followed by
its inverse is the total identity.
-/

namespace PSTSEPPA
namespace PSTS
namespace Examples

open TriplePoint

/-- Two composable singleton partial automorphisms. -/
def wordGen : Bool → PartialAut oneTriple
  | false => PartialAut.single oneTriple a b
  | true => PartialAut.single oneTriple b c

/-- Positive letters are evaluated left-to-right: first `a ↦ b`, then
`b ↦ c`. -/
theorem eval_two_positive :
    (SignedWord.eval wordGen [.pos false, .pos true]).toPEquiv =
      PEquiv.single a c := by
  simp [SignedWord.eval, SignedWord.evalLetter, wordGen, PartialAut.trans]

/-- A generator followed by its formal inverse is only the identity on the
generator's source, not the total identity. -/
theorem eval_pos_neg :
    (SignedWord.eval wordGen [.pos false, .neg false]).toPEquiv =
      PEquiv.single a a := by
  simp [SignedWord.eval, SignedWord.evalLetter, wordGen, PartialAut.trans]

@[simp]
theorem eval_pos_neg_at_a :
    (SignedWord.eval wordGen [.pos false, .neg false]).toPEquiv a = some a := by
  rw [eval_pos_neg]
  exact PEquiv.single_apply a a

@[simp]
theorem eval_pos_neg_at_c :
    (SignedWord.eval wordGen [.pos false, .neg false]).toPEquiv c = none := by
  rw [eval_pos_neg]
  exact PEquiv.single_apply_of_ne (by decide) a

/-- The inverse-word theorem has the expected order reversal on an explicit
two-letter word. -/
example :
    SignedWord.eval wordGen (SignedWord.inv [.pos false, .pos true]) =
      (SignedWord.eval wordGen [.pos false, .pos true]).symm :=
  SignedWord.eval_inv wordGen _

end Examples
end PSTS
end PSTSEPPA
