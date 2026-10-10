import PSTSEPPA.ABO.LocalRankRetractableSubalphabet
import PSTSEPPA.ABO.SynchronizedLabelledGroups
import Mathlib.Data.Fintype.Pi

/-!
# Finite detector products for ALL subalphabets of bounded rank

The unary cyclic-detector construction (#320-321) can be generalized
without inventing an auxiliary free group or changing signed-word
conventions. Fix any k and any labelled group gen : ι → Γ.

Index by EVERY finite subalphabet A ⊆ ι of cardinality ≤ k,
and use the GENUINE generated subgroup Γ[A], with all labels
outside A sent to identity. The product of these actual groups
has a canonical labelled generator family and acts as a universal
finite-rank word-restriction detector.

This module establishes exact coordinate evaluation, arbitrary
signed erasure/restriction identities, and finite-product size
certificates. The later rank-lift theorem will prove that a
synchronous product with the original Γ is (k+1)-retractable
and is k-stable over Γ whenever Γ is k-retractable.

This is an ALGEBRAIC generalization only, not the still-open
geometric Y_k/Z_k catalogue or reflecting-group construction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Exact rank-k index: every subalphabet of size at most k. -/
abbrev RankDetectorIndex (ι : Type*) (k : ℕ) [Fintype ι] :=
  {A : Finset ι // A.card ≤ k}

/-- The actual dependent product of the generated subalphabet groups. -/
abbrev RankDetectorGroup (gen : ι → Γ) (k : ℕ) :=
  ∀ j : RankDetectorIndex ι k, generatedSubgroup gen j.1

/-- On detector coordinate A, labelled letter i acts as gen(i)
if i∈A and as identity otherwise. -/
def rankDetectorGenerator (gen : ι → Γ) (k : ℕ) :
    ι → RankDetectorGroup gen k :=
  fun i j => trivialCompletionGenerator gen j.1 i

/-- Evaluation on one dependent product coordinate is literally
evaluation in the genuine trivial completion for that subalphabet. -/
theorem evalGroup_rankDetector_apply
    (gen : ι → Γ) (k : ℕ)
    (w : LabelWord ι) (j : RankDetectorIndex ι k) :
    (PSTS.SignedWord.evalGroup (rankDetectorGenerator gen k) w) j =
      PSTS.SignedWord.evalGroup
        (trivialCompletionGenerator gen j.1) w := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      cases s <;>
        simp [PSTS.SignedWord.evalGroup_cons,
          rankDetectorGenerator, ih]

/-- After coercion into Γ, detector coordinate A is precisely
the ambient group value of the word restricted to A.
This uses no k-retractability of Γ. -/
theorem coe_evalGroup_rankDetector
    (gen : ι → Γ) (k : ℕ)
    (w : LabelWord ι) (j : RankDetectorIndex ι k) :
    (((PSTS.SignedWord.evalGroup
        (rankDetectorGenerator gen k) w) j :
          generatedSubgroup gen j.1) : Γ) =
      PSTS.SignedWord.evalGroup gen (LabelWord.restrictTo j.1 w) := by
  rw [evalGroup_rankDetector_apply,
    coe_evalGroup_trivialCompletionGenerator]

/-- Erasing a generator from the selected subalphabet never
increases its rank: the output remains an ACTUAL detector index. -/
def RankDetectorIndex.erase (j : RankDetectorIndex ι k) (a : ι) :
    RankDetectorIndex ι k :=
  ⟨j.1.erase a,
    (Finset.card_le_card (Finset.erase_subset a j.1)).trans j.2⟩

namespace LabelWord

/-- Restricting a signed word to A\{a} is exactly the same as
first restricting to A and then erasing all signed a-letters.
Includes formal inverses, empty words and absent labels. -/
theorem restrictTo_erase
    (A : Finset ι) (a : ι) (w : LabelWord ι) :
    restrictTo (A.erase a) w =
      eraseGenerator a (restrictTo A w) := by
  have hcomp :
      Finset.univ \ (A.erase a) =
        insert a (Finset.univ \ A) := by
    ext i
    by_cases hi : i = a
    · subst i
      simp
    · simp [Finset.mem_erase, hi]
  calc
    restrictTo (A.erase a) w =
        restrictTo A (eraseGenerator a w) := by
      simp only [restrictTo, eraseGenerator, hcomp,
        deleteGenerators_insert]
    _ = eraseGenerator a (restrictTo A w) :=
      restrictTo_eraseGenerator A a w

/-- If w is supported by A, erasing a is literally the same
word as restricting w to A\{a}. -/
theorem eraseGenerator_eq_restrictTo_erase_of_uses
    (A : Finset ι) (a : ι) (w : LabelWord ι)
    (hw : Uses A w) :
    eraseGenerator a w = restrictTo (A.erase a) w := by
  calc
    eraseGenerator a w =
        eraseGenerator a (restrictTo A w) := by
      rw [restrictTo_eq_self_of_uses A w hw]
    _ = restrictTo (A.erase a) w :=
      (restrictTo_erase A a w).symm

end LabelWord

/-- Restricted evaluation commutes exactly with erasure,
even though the two detector coordinates have DIFFERENT
generated-subgroup types; coercion into Γ makes the equality
well typed and mathematically meaningful. -/
theorem coe_evalGroup_rankDetector_erase
    (gen : ι → Γ) (k : ℕ)
    (j : RankDetectorIndex ι k) (a : ι) (w : LabelWord ι) :
    (((PSTS.SignedWord.evalGroup
        (rankDetectorGenerator gen k)
        (LabelWord.eraseGenerator a w)) j :
          generatedSubgroup gen j.1) : Γ) =
      (((PSTS.SignedWord.evalGroup
        (rankDetectorGenerator gen k) w) (j.erase a) :
          generatedSubgroup gen (j.erase a).1) : Γ) := by
  rw [coe_evalGroup_rankDetector, coe_evalGroup_rankDetector,
    LabelWord.restrictTo_eraseGenerator,
    LabelWord.restrictTo_erase]

variable [Finite Γ]

/-- If Γ and the alphabet are finite, the complete dependent
detector product on EVERY ≤k alphabet is finite. -/
theorem finite_rankDetectorGroup
    (gen : ι → Γ) (k : ℕ) :
    Finite (RankDetectorGroup gen k) := by
  classical
  letI : Fintype Γ := Fintype.ofFinite _
  infer_instance

end ABO
end PSTSEPPA
