import PSTSEPPA.ABO.StabilityRetractability
import PSTSEPPA.ABO.RetractableGroupContent

/-!
# The automatic rank-one base of the corrected ABO Section 5 induction

The independent ABO proof audit isolates a genuine k=1 base gap in
Proposition 5.4. Its local repair begins with the elementary but
necessary fact that EVERY labelled group is 1-retractable.

This file formalizes that exact low-rank fact using the rank-bounded
KRetractable definition. If the original word alphabet A has
cardinality <=1, either the generator a being erased lies outside A,
in which case deletion does nothing, or A={a}, so erasing all
a-labelled letters turns BOTH words into the empty word, regardless
of their original values. This includes the empty original alphabet,
trivial generators, inverse letters, and k=0.

This is a genuine *base-input* for R2, not the missing stability of
the later quotient G₂ -> H₁. The repaired Prop. 5.4 still requires
the rank-two cluster geometry and real Section 5 transition-group
stage construction, which are explicitly not claimed here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace LabelWord

/-- Erasing generator a from a word using only a (with either
sign, possibly repeated) yields precisely the EMPTY word. -/
theorem eraseGenerator_eq_nil_of_uses_singleton (a : ι) :
    ∀ w : LabelWord ι,
      Uses ({a} : Finset ι) w →
      eraseGenerator a w = [] := by
  intro w
  induction w with
  | nil =>
      intro _
      rfl
  | cons s w ih =>
      intro hw
      have hs : signedBase s = a := Finset.mem_singleton.mp hw.1
      have ht : eraseGenerator a w = [] := ih hw.2
      change
        (if signedBase s ∈ ({a} : Finset ι)
          then eraseGenerator a w
          else s :: eraseGenerator a w) = []
      simpa [hs] using ht

end LabelWord

/-- Rank-bounded retractability is monotone in the rank:
deletion equations for all support alphabets of size ≤k
also hold on every alphabet of size ≤j≤k. -/
theorem kRetractable_mono
    (gen : ι → Γ) {j k : ℕ}
    (hk : KRetractable gen k) (hjk : j ≤ k) :
    KRetractable gen j := by
  intro A hA a p q hp hq hpq
  exact hk A (hA.trans hjk) a p q hp hq hpq

/-- Every labelled group is automatically 1-retractable:
the first genuine rank of the corrected ABO Section 5 induction
has NO nontrivial group-theoretic deletion obstruction. -/
theorem kRetractable_one (gen : ι → Γ) :
    KRetractable gen 1 := by
  intro A hA a p q hp hq hpq
  by_cases ha : a ∈ A
  · have hSubset : A ⊆ ({a} : Finset ι) := by
      intro b hb
      have hba : b = a :=
        (Finset.card_le_one.mp hA) b hb a ha
      simpa [hba]
    have hpSingle : LabelWord.Uses ({a} : Finset ι) p :=
      LabelWord.uses_of_all ({a} : Finset ι) p (by
        intro s hs
        exact hSubset (LabelWord.mem_base_of_uses A p hp s hs))
    have hqSingle : LabelWord.Uses ({a} : Finset ι) q :=
      LabelWord.uses_of_all ({a} : Finset ι) q (by
        intro s hs
        exact hSubset (LabelWord.mem_base_of_uses A q hq s hs))
    have hpErase : LabelWord.eraseGenerator a p = [] :=
      LabelWord.eraseGenerator_eq_nil_of_uses_singleton a p hpSingle
    have hqErase : LabelWord.eraseGenerator a q = [] :=
      LabelWord.eraseGenerator_eq_nil_of_uses_singleton a q hqSingle
    simp [hpErase, hqErase]
  · have hpUnchanged : LabelWord.eraseGenerator a p = p := by
      apply LabelWord.eraseGenerator_eq_self_of_all_base_ne a p
      intro s hs hsa
      have hMem := LabelWord.mem_base_of_uses A p hp s hs
      exact ha (by simpa [hsa] using hMem)
    have hqUnchanged : LabelWord.eraseGenerator a q = q := by
      apply LabelWord.eraseGenerator_eq_self_of_all_base_ne a q
      intro s hs hsa
      have hMem := LabelWord.mem_base_of_uses A q hq s hs
      exact ha (by simpa [hsa] using hMem)
    simpa [hpUnchanged, hqUnchanged] using hpq

/-- In particular the empty-alphabet k=0 endpoint of the
construction is automatically retractable as well. -/
theorem kRetractable_zero (gen : ι → Γ) :
    KRetractable gen 0 :=
  kRetractable_mono gen (kRetractable_one gen) (Nat.zero_le _)

end ABO
end PSTSEPPA
