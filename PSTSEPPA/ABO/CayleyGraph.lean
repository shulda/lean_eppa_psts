import PSTSEPPA.ABO.ActionGraph

/-!
# Cayley graphs

The ABO Cayley graph of a group with a labelled generating family is the
complete action graph of right multiplication by those generators.

The key orientation check is that following a word `w` from `x` ends at
`x * evalGroup(w)`, with no reversal of the word.
-/

namespace PSTSEPPA
namespace ABO

/-- Right multiplication by a fixed group element, as a permutation. -/
def rightMulPerm {Γ : Type*} [Group Γ] (g : Γ) : Equiv.Perm Γ where
  toFun x := x * g
  invFun x := x * g⁻¹
  left_inv x := by
    simp [mul_assoc]
  right_inv x := by
    simp [mul_assoc]

namespace rightMulPerm

variable {Γ : Type*} [Group Γ]

@[simp]
theorem apply (g x : Γ) :
    rightMulPerm g x = x * g :=
  rfl

@[simp]
theorem symm (g : Γ) :
    (rightMulPerm g).symm = rightMulPerm g⁻¹ := by
  apply Equiv.ext
  intro x
  rfl

end rightMulPerm

/-- The complete labelled Cayley graph for a labelled family of group
generators.  No assumption that the family generates all of `Γ` is built
into the definition. -/
noncomputable def cayleyGraph {Γ ι : Type*} [Group Γ]
    (gen : ι → Γ) :
    CompleteEGraph Γ (ActionEdge Γ ι) ι :=
  actionGraph (fun i => rightMulPerm (gen i))

namespace cayleyGraph

variable {Γ ι : Type*} [Group Γ] (gen : ι → Γ)

@[simp]
theorem target_pos (x : Γ) (i : ι) :
    (cayleyGraph gen).target (x, SignedLabel.pos i) =
      x * gen i := by
  rw [actionGraph.target]
  rfl

@[simp]
theorem target_neg (x : Γ) (i : ι) :
    (cayleyGraph gen).target (x, SignedLabel.neg i) =
      x * (gen i)⁻¹ := by
  rw [actionGraph.target]
  rfl

/-- One signed Cayley step is right multiplication by the group value of the
same signed letter. -/
theorem target_eq_mul_evalGroupLetter
    (x : Γ) (s : SignedLabel ι) :
    (cayleyGraph gen).target (x, s) =
      x * PSTS.SignedWord.evalGroupLetter gen s := by
  cases s <;> rfl

/-- Following a word in the Cayley graph agrees exactly with group-valued word
evaluation in the chronological, left-to-right convention. -/
theorem followWord_eq_mul_evalGroup
    (x : Γ) (w : LabelWord ι) :
    (cayleyGraph gen).followWord x w =
      x * PSTS.SignedWord.evalGroup gen w := by
  induction w generalizing x with
  | nil =>
      simp
  | cons s w ih =>
      rw [CompleteEGraph.followWord_cons]
      rw [actionGraph.edgeAt, target_eq_mul_evalGroupLetter]
      rw [ih]
      simp [PSTS.SignedWord.evalGroup, mul_assoc]

/-- The transition generator of the Cayley graph is right multiplication by
the corresponding labelled group element, viewed in the opposite permutation
group. -/
@[simp]
theorem transitionGenerator (i : ι) :
    (cayleyGraph gen).transitionGenerator i =
      MulOpposite.op (rightMulPerm (gen i)) := by
  exact actionGraph.transitionGenerator
    (fun j => rightMulPerm (gen j)) i

end cayleyGraph

end ABO
end PSTSEPPA
