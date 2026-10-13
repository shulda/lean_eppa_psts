import PSTSEPPA.ABO.DependentDisjointStages

/-!
# Exact arbitrary signed-word congruence in dependent disjoint actions

A dependent union of complete signed action graphs retains its literal
fibre tag, and following a word preserves that tag. Consequently two
arbitrary signed chronological words agree on the full tagged action
if and only if they agree, vertexwise, on EVERY individual fibre.

Unlike the identity-word-only kernel lemmas, these equivalences
compare any two group words and retain original per-stage vertices.
They are independent of retractability, stability, nonempty stage
families or any property of the original ABO H₁ source.
-/

namespace PSTSEPPA
namespace ABO

variable {J ι : Type*}
variable {V Edge : J → Type*}
variable [Fintype ι] [DecidableEq ι]

/-- Word-action equality at a literally tagged vertex is EQUIVALENT
to action equality at the original vertex of that same fibre. -/
theorem dependentDisjointStage_wordEquality_at_tag_iff
    (T : ∀ j : J, CompleteEGraph (V j) (Edge j) ι)
    (j : J) (x : V j) (p q : LabelWord ι) :
    (dependentDisjointStage T).followWord
        (⟨j, x⟩ : Sigma V) p =
      (dependentDisjointStage T).followWord
        (⟨j, x⟩ : Sigma V) q ↔
      (T j).followWord x p = (T j).followWord x q := by
  rw [dependentDisjointStage_followWord,
    dependentDisjointStage_followWord]
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · intro h
    exact congrArg (fun y : V j => (⟨j, y⟩ : Sigma V)) h

/-- Two arbitrary signed words have equal complete actions on
the sigma union precisely when they have equal complete actions
on all genuine individually indexed completed stages. -/
theorem dependentDisjointStage_wordEquality_all_iff
    (T : ∀ j : J, CompleteEGraph (V j) (Edge j) ι)
    (p q : LabelWord ι) :
    (∀ u : Sigma V,
      (dependentDisjointStage T).followWord u p =
        (dependentDisjointStage T).followWord u q) ↔
      ∀ (j : J) (x : V j),
        (T j).followWord x p = (T j).followWord x q := by
  constructor
  · intro h j x
    exact (dependentDisjointStage_wordEquality_at_tag_iff
      T j x p q).mp (h ⟨j, x⟩)
  · intro h
    rintro ⟨j, x⟩
    exact (dependentDisjointStage_wordEquality_at_tag_iff
      T j x p q).mpr (h j x)

end ABO
end PSTSEPPA
