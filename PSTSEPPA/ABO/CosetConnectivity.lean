import PSTSEPPA.ABO.CosetIntersections

/-!
# Subalphabet connectivity of retractable cosets

A word uses a subalphabet A when every positive or negative letter has its
underlying generator in A.  Membership in a coset g G[A] is equivalent to
reachability from g by such a word.  Combined with the coset-intersection
formula, this gives the connectedness statement used throughout the ABO
cluster arguments.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace LabelWord

/-- Every letter of the word belongs to the indicated subalphabet. -/
def Uses (A : Finset ι) : LabelWord ι → Prop
  | [] => True
  | s :: w => signedBase s ∈ A ∧ Uses A w

@[simp]
theorem uses_nil (A : Finset ι) :
    Uses A ([] : LabelWord ι) :=
  trivial

@[simp]
theorem uses_cons (A : Finset ι) (s : SignedLabel ι) (w : LabelWord ι) :
    Uses A (s :: w) ↔ signedBase s ∈ A ∧ Uses A w :=
  Iff.rfl

@[simp]
theorem uses_append (A : Finset ι) (p q : LabelWord ι) :
    Uses A (p ++ q) ↔ Uses A p ∧ Uses A q := by
  induction p with
  | nil =>
      simp [Uses]
  | cons s p ih =>
      simp [Uses, ih, and_assoc]

theorem Uses.inv {A : Finset ι} {w : LabelWord ι}
    (hw : Uses A w) :
    Uses A (PSTS.SignedWord.inv w) := by
  induction w with
  | nil =>
      simp [Uses]
  | cons s w ih =>
      rw [PSTS.SignedWord.inv_cons, uses_append]
      constructor
      · exact ih hw.2
      · cases s <;> simpa [Uses] using hw.1

end LabelWord

/-- Evaluation of a subalphabet-supported word lies in the generated subgroup. -/
theorem evalGroup_mem_generatedSubgroup_of_uses
    (gen : ι → Γ) (A : Finset ι) {w : LabelWord ι}
    (hw : LabelWord.Uses A w) :
    PSTS.SignedWord.evalGroup gen w ∈ generatedSubgroup gen A := by
  induction w with
  | nil =>
      exact (generatedSubgroup gen A).one_mem
  | cons s w ih =>
      have htail := ih hw.2
      cases s with
      | pos i =>
          have hhead :
              gen i ∈ generatedSubgroup gen A :=
            generator_mem_generatedSubgroup gen A hw.1
          exact (generatedSubgroup gen A).mul_mem hhead htail
      | neg i =>
          have hgen :
              gen i ∈ generatedSubgroup gen A :=
            generator_mem_generatedSubgroup gen A hw.1
          have hhead :
              (gen i)⁻¹ ∈ generatedSubgroup gen A :=
            (generatedSubgroup gen A).inv_mem hgen
          exact (generatedSubgroup gen A).mul_mem hhead htail

/-- Every element of a subalphabet-generated subgroup has a representing word
using only that subalphabet. -/
theorem exists_word_uses_eq_of_mem_generatedSubgroup
    (gen : ι → Γ) (A : Finset ι) {x : Γ}
    (hx : x ∈ generatedSubgroup gen A) :
    ∃ w : LabelWord ι,
      LabelWord.Uses A w ∧
      PSTS.SignedWord.evalGroup gen w = x := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with ⟨i, rfl⟩
      exact
        ⟨[PSTS.SignedLetter.pos i.1],
          by simp [LabelWord.Uses, i.2],
          by simp⟩
  | one =>
      exact ⟨[], by simp, by simp⟩
  | mul x y hx hy ihx ihy =>
      rcases ihx with ⟨p, hpA, hp⟩
      rcases ihy with ⟨q, hqA, hq⟩
      refine ⟨p ++ q, ?_, ?_⟩
      · exact (LabelWord.uses_append A p q).2 ⟨hpA, hqA⟩
      · rw [PSTS.SignedWord.evalGroup_append, hp, hq]
  | inv x hx ih =>
      rcases ih with ⟨p, hpA, hp⟩
      refine ⟨PSTS.SignedWord.inv p, hpA.inv, ?_⟩
      rw [PSTS.SignedWord.evalGroup_inv, hp]

/-- Reachability by a word whose labels all lie in A. -/
def SubalphabetReachable
    (gen : ι → Γ) (A : Finset ι) (u v : Γ) : Prop :=
  ∃ w : LabelWord ι,
    LabelWord.Uses A w ∧
    (cayleyGraph gen).followWord u w = v

/-- Coset membership is exactly subalphabet reachability. -/
theorem mem_generatedLeftCoset_iff_subalphabetReachable
    (gen : ι → Γ) (A : Finset ι) (g x : Γ) :
    x ∈ generatedLeftCoset gen A g ↔
      SubalphabetReachable gen A g x := by
  constructor
  · intro hx
    change g⁻¹ * x ∈ generatedSubgroup gen A at hx
    rcases exists_word_uses_eq_of_mem_generatedSubgroup gen A hx with
      ⟨w, hwA, hw⟩
    refine ⟨w, hwA, ?_⟩
    rw [cayleyGraph.followWord_eq_mul_evalGroup, hw]
    simp [mul_assoc]
  · rintro ⟨w, hwA, hw⟩
    have hmem :=
      evalGroup_mem_generatedSubgroup_of_uses gen A hwA
    change g⁻¹ * x ∈ generatedSubgroup gen A
    have heq :
        g * PSTS.SignedWord.evalGroup gen w = x := by
      rw [← cayleyGraph.followWord_eq_mul_evalGroup gen g w]
      exact hw
    rw [← heq]
    simpa [mul_assoc] using hmem

/-- A nonempty intersection of two subalphabet cosets is connected by the
intersection alphabet. -/
theorem generatedLeftCoset_inter_subalphabet_connected
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (A B : Finset ι) (g h : Γ)
    (hne :
      (generatedLeftCoset gen A g ∩
        generatedLeftCoset gen B h).Nonempty) :
    ∃ z : Γ,
      z ∈ generatedLeftCoset gen A g ∩ generatedLeftCoset gen B h ∧
      ∀ x : Γ,
        x ∈ generatedLeftCoset gen A g ∩ generatedLeftCoset gen B h →
          SubalphabetReachable gen (A ∩ B) z x := by
  rcases generatedLeftCoset_inter_of_nonempty
      gen hgen hret A B g h hne with
    ⟨z, hz, hinter⟩
  refine ⟨z, hz, ?_⟩
  intro x hx
  have hx' :
      x ∈ generatedLeftCoset gen (A ∩ B) z := by
    rw [← hinter]
    exact hx
  exact
    (mem_generatedLeftCoset_iff_subalphabetReachable
      gen (A ∩ B) z x).1 hx'

end ABO
end PSTSEPPA
