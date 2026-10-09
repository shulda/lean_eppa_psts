import PSTSEPPA.ABO.CayleyGraph
import PSTSEPPA.PSTS.WordEval

/-!
# Concrete total-permutation lifts for the PSTS Cayley/MAX application

This is the specialised C1 bridge from a selected alphabet of partial
automorphisms to the finite permutation group that will label the
Cayley graph. We do NOT formalise a general inverse monoid.

An independent total-permutation lift of each partial generator
extends its action at every point of the partial domain. Signed
inverse letters must also extend the inverse partial automorphism,
with the SAME orientation.

We prove the fundamental word-evaluation compatibility:
if an actual partial word sends x to y, the total permutation word
sends x to the SAME y. Consequently any two partial words with equal
values in the total permutation group agree everywhere they are both
defined. In particular an identity-valued word acts as a partial
identity, an elementary fact needed in the Cayley path-inclusion
argument and later fibre-MAX construction.

Group values use the OPPOSITE permutation group to match the
right-action/chronological-word convention of the audited transfer.
No new group-existence theorem, content lemma, bridge-freeness,
or full ABO assertion is assumed.
-/

namespace PSTSEPPA
namespace PSTS

variable {V ι : Type*} {A : PSTS V}

/-- Chosen total permutations extending the selected actual partial
PSTS automorphisms. Extending finite partial bijections to total
permutations is a separate finite combinatorial existence obligation.
There is no need to assume the lifts preserve the PSTS operation
globally; they are merely permutations of its finite vertex set. -/
structure TotalPermutationLifts (A : PSTS V)
    (gen : ι → PartialAut A) where
  perm : ι → Equiv.Perm V
  extends : ∀ (i : ι) {x y : V},
    (gen i).toPEquiv x = some y → perm i x = y

namespace TotalPermutationLifts

variable {gen : ι → PartialAut A}
variable (L : TotalPermutationLifts A gen)

/-- The lift generators considered as right-action values.
Multiplication in the opposite permutation group corresponds
exactly to chronological word concatenation. -/
def groupGenerator (i : ι) : ABO.RightPerm V :=
  MulOpposite.op (L.perm i)

/-- Total group value of a signed word in the chosen permutations. -/
def groupValue (w : SignedWord ι) : ABO.RightPerm V :=
  SignedWord.evalGroup L.groupGenerator w

/-- The total map obtained by applying the group value of the
signed word, in chronological order, at a vertex. -/
def totalApply (w : SignedWord ι) (x : V) : V :=
  MulOpposite.unop (L.groupValue w) x

@[simp]
theorem totalApply_nil (x : V) :
    L.totalApply [] x = x := by
  rfl

/-- The group-valued total action processes the first signed letter,
then the remaining word. This tests the opposite-group orientation. -/
theorem totalApply_cons (s : SignedLetter ι)
    (w : SignedWord ι) (x : V) :
    L.totalApply (s :: w) x =
      L.totalApply w (ABO.signedPerm L.perm s x) := by
  cases s <;> rfl

/-- A negative signed letter is extended by the inverse total
permutation, not by a separately chosen permutation. -/
theorem signedLetter_extends (s : SignedLetter ι)
    {x y : V}
    (h : (SignedWord.evalLetter gen s).toPEquiv x = some y) :
    ABO.signedPerm L.perm s x = y := by
  cases s with
  | pos i =>
      exact L.extends i h
  | neg i =>
      have hforward : (gen i).toPEquiv y = some x :=
        ((gen i).toPEquiv.eq_some_iff).mp h
      have hf : L.perm i y = x := L.extends i hforward
      change (L.perm i).symm x = y
      rw [← hf]
      exact (L.perm i).left_inv y

/-- Every partial word is literally a restriction of its value
in the chosen total permutation group. -/
theorem partial_word_agrees_with_total
    (w : SignedWord ι) {x y : V}
    (h : (SignedWord.eval gen w).toPEquiv x = some y) :
    L.totalApply w x = y := by
  induction w generalizing x y with
  | nil =>
      simp only [SignedWord.eval_nil, PartialAut.toPEquiv_refl,
        PEquiv.refl_apply, Option.some.injEq] at h
      subst y
      exact L.totalApply_nil x
  | cons s w ih =>
      change
        ((SignedWord.evalLetter gen s).toPEquiv.trans
          (SignedWord.eval gen w).toPEquiv) x = some y at h
      rw [PEquiv.trans_eq_some] at h
      obtain ⟨mid, hfirst, htail⟩ := h
      rw [L.totalApply_cons, L.signedLetter_extends s hfirst]
      exact ih htail

/-- Equality of *total permutation group values* forces any two
partial words to agree on their common domain. This is the
prefix consistency required by the Cayley path-inclusion lemma,
including the case of distinct words representing the identity. -/
theorem partial_words_agree_of_groupValue_eq
    (u v : SignedWord ι)
    (hUV : L.groupValue u = L.groupValue v)
    {x y z : V}
    (hu : (SignedWord.eval gen u).toPEquiv x = some y)
    (hv : (SignedWord.eval gen v).toPEquiv x = some z) :
    y = z := by
  have h1 := L.partial_word_agrees_with_total u hu
  have h2 := L.partial_word_agrees_with_total v hv
  change (MulOpposite.unop (L.groupValue u)) x = y at h1
  change (MulOpposite.unop (L.groupValue v)) x = z at h2
  rw [hUV] at h1
  exact h1.symm.trans h2

/-- An identity-valued word, whenever defined, fixes its input.
This is a necessary elementary consequence of concrete lifts,
not a spurious claim that the identity partial map is the
maximum of all partial bijections. -/
theorem identity_group_word_is_partial_identity
    (w : SignedWord ι)
    (hw : L.groupValue w = 1)
    {x y : V}
    (hxy : (SignedWord.eval gen w).toPEquiv x = some y) :
    y = x := by
  have h := L.partial_word_agrees_with_total w hxy
  change (MulOpposite.unop (L.groupValue w)) x = y at h
  rw [hw] at h
  simpa using h.symm

end TotalPermutationLifts
end PSTS
end PSTSEPPA
