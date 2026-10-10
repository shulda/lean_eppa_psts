import PSTSEPPA.ABO.StabilityRetractability
import PSTSEPPA.ABO.CanonicalCover
import Mathlib.Data.Finset.Card

/-!
# Rank stability as a word-kernel / moved-vertex test

The repaired ABO Proposition 5.4 proves k-stability of a labelled
quotient by considering a word w using at most k generator labels:
if it acts NONTRIVIALLY upstairs, it must act nontrivially
downstairs. In the source this is tested at actual vertices
of the finite complete action graph.

This module gives the kernel-checked algebraic equivalence between:

* k-stability, defined as injectivity on every k-generated subgroup;
* triviality upstairs of every <=k-labelled word whose value is 1
  downstairs.

For a complete EGraph T, a word is trivial in its actual
transition group if and only if following that word fixes EVERY
vertex of T. Consequently, if an H-trivial <=k-word has a
nontrivial value in T, it has a concrete moved-vertex witness.
This is exactly the logical interface for the k=1 repair R2:
classify singleton-labelled components of each completed finite
stage and show no unwanted moved-vertex witness exists.

No geometric component classification or stability of the
actual ABO stage tower is asserted by this module. These are
the remaining substantial source-induction proof obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]

namespace LabelledGroupQuotient

variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable (Q : LabelledGroupQuotient genΓ genΔ)

/-- Kernel test for rank-k stability: every word supported in
an alphabet of size at most k whose H-value is the identity
must already have identity value in G. This tests only a
single word at a time rather than two arbitrary subgroup points. -/
theorem kStable_of_word_kernel
    (k : ℕ)
    (hker :
      ∀ (A : Finset ι), A.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses A w →
          PSTS.SignedWord.evalGroup genΔ w = 1 →
          PSTS.SignedWord.evalGroup genΓ w = 1) :
    Q.KStable k := by
  intro A hA x y hxy
  obtain ⟨p, hpA, hpx⟩ :=
    exists_word_uses_eq_of_mem_generatedSubgroup genΓ A x.2
  obtain ⟨q, hqA, hqy⟩ :=
    exists_word_uses_eq_of_mem_generatedSubgroup genΓ A y.2
  let w : LabelWord ι := PSTS.SignedWord.inv p ++ q
  have hwA : LabelWord.Uses A w :=
    (LabelWord.uses_append A _ _).mpr ⟨hpA.inv, hqA⟩
  have himages : Q.hom x.1 = Q.hom y.1 :=
    congrArg Subtype.val hxy
  have hdown :
      PSTS.SignedWord.evalGroup genΔ w = 1 := by
    dsimp [w]
    rw [PSTS.SignedWord.evalGroup_append,
      PSTS.SignedWord.evalGroup_inv]
    have hpMap :
        PSTS.SignedWord.evalGroup genΔ p =
          Q.hom x.1 := by
      rw [← Q.map_evalGroup p, hpx]
    have hqMap :
        PSTS.SignedWord.evalGroup genΔ q =
          Q.hom y.1 := by
      rw [← Q.map_evalGroup q, hqy]
    rw [hpMap, hqMap, himages]
    simp
  have hup : PSTS.SignedWord.evalGroup genΓ w = 1 :=
    hker A hA w hwA hdown
  have hgroup : x.1⁻¹ * y.1 = 1 := by
    dsimp [w] at hup
    simpa [PSTS.SignedWord.evalGroup_append,
      PSTS.SignedWord.evalGroup_inv, hpx, hqy] using hup
  apply Subtype.ext
  exact inv_mul_eq_one.mp hgroup

/-- Source-facing reformulation of k-stability as a word
kernel condition. This converts the hard part of Proposition
5.4 into a concrete signed-word test on finite action stages. -/
theorem kStable_iff_word_kernel (k : ℕ) :
    Q.KStable k ↔
      ∀ (A : Finset ι), A.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses A w →
          PSTS.SignedWord.evalGroup genΔ w = 1 →
          PSTS.SignedWord.evalGroup genΓ w = 1 := by
  constructor
  · intro hstable A hA w hw heq
    have hWord : PSTS.SignedWord.evalGroup genΔ w =
        PSTS.SignedWord.evalGroup genΔ ([] : LabelWord ι) := by
      simpa using heq
    have hLift :=
      Q.evalGroup_eq_of_stableAt (hstable A hA) hw
        (LabelWord.uses_nil A) hWord
    simpa using hLift
  · exact Q.kStable_of_word_kernel k

end LabelledGroupQuotient

namespace CompleteEGraph

variable {V Edge : Type*}
variable (T : CompleteEGraph V Edge ι)

/-- Exact moved-vertex criterion for the genuine transition-group
value of a signed word. The completed stage action may have
repeated or trivial generator permutations; the statement needs
neither faithfulness of generator labels nor connectivity. -/
theorem wordValue_eq_one_iff_all_vertices_fixed
    (w : LabelWord ι) :
    T.wordValue w = 1 ↔
      ∀ u : V, T.followWord u w = u := by
  constructor
  · intro h u
    have hWord := T.rightApply_wordValue w u
    rw [h] at hWord
    simpa [rightApply] using hWord.symm
  · intro h
    apply MulOpposite.unop_injective
    apply Equiv.ext
    intro u
    have hWord := T.rightApply_wordValue w u
    change rightApply (T.wordValue w) u = u
    exact hWord.trans (h u)

/-- Contrapositive witness form used in corrected Proposition 5.4:
a nonidentity transition word value moves a concrete vertex. -/
theorem exists_moved_vertex_of_wordValue_ne_one
    (w : LabelWord ι)
    (hne : T.wordValue w ≠ 1) :
    ∃ u : V, T.followWord u w ≠ u := by
  by_contra hnone
  apply hne
  apply (T.wordValue_eq_one_iff_all_vertices_fixed w).mpr
  intro u
  by_contra hmove
  exact hnone ⟨u, hmove⟩

end CompleteEGraph
end ABO
end PSTSEPPA
