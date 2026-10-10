import PSTSEPPA.ABO.DisjointUnionEGraphs
import PSTSEPPA.ABO.StageStabilityWordKernel

/-!
# Exact signed-word kernels of disjoint complete ABO stages

The Section 5 construction assembles finite complete E-graphs by
literal disjoint unions. A signed word acts identically on the
disjoint union precisely when it acts identically on each component.

This is a theorem about the actual transition-group word values,
not an assumed quotient or an informal componentwise argument.
It also handles empty carriers, identity generators, inverse
letters, and genuine loops.

Together with the synchronized-product identification, this is
the word-kernel assembly step in the repaired Proposition 5.4.
The existence and stability of the augmented component stages
are separate mathematical obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable [Fintype ι] [DecidableEq ι]

namespace CompleteEGraph

/-- The genuine transition word value on a literal disjoint
union is the identity iff the word value is the identity on
BOTH constituent complete graphs, including empty carriers. -/
theorem disjointUnion_wordValue_eq_one_iff
    (G : CompleteEGraph V₁ E₁ ι)
    (H : CompleteEGraph V₂ E₂ ι)
    (w : LabelWord ι) :
    (G.disjointUnion H).wordValue w = 1 ↔
      G.wordValue w = 1 ∧ H.wordValue w = 1 := by
  constructor
  · intro hsum
    have hall :=
      ((G.disjointUnion H).wordValue_eq_one_iff_all_vertices_fixed w).mp hsum
    constructor
    · apply (G.wordValue_eq_one_iff_all_vertices_fixed w).mpr
      intro x
      have h := hall (.inl x)
      rw [G.disjointUnion_followWord_inl] at h
      exact Sum.inl.inj h
    · apply (H.wordValue_eq_one_iff_all_vertices_fixed w).mpr
      intro y
      have h := hall (.inr y)
      rw [G.disjointUnion_followWord_inr] at h
      exact Sum.inr.inj h
  · rintro ⟨hG, hH⟩
    apply ((G.disjointUnion H).wordValue_eq_one_iff_all_vertices_fixed w).mpr
    intro z
    cases z with
    | inl x =>
        rw [G.disjointUnion_followWord_inl]
        exact congrArg Sum.inl
          ((G.wordValue_eq_one_iff_all_vertices_fixed w).mp hG x)
    | inr y =>
        rw [G.disjointUnion_followWord_inr]
        exact congrArg Sum.inr
          ((H.wordValue_eq_one_iff_all_vertices_fixed w).mp hH y)

end CompleteEGraph
end ABO
end PSTSEPPA
