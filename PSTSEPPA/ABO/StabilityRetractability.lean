import PSTSEPPA.ABO.Stability
import PSTSEPPA.ABO.CayleyEdgeRetraction
import PSTSEPPA.ABO.RetractableGroupContent
import Mathlib.Data.Finset.Card

/-!
# Repaired ABO Theorem 4.7: descend ranked retractability across a stable quotient

The source's Theorem 4.7 (repair R1 in the independently audited
PSTS/ABO project) uses (k+1)-retractability of the upstairs G
without including it as a hypothesis. It DOES follow from
(k+1)-retractability of the quotient H and k-stability of G -> H.

The proof is elementary but logically indispensable. Take words
p,q supported in an alphabet A of size <= k+1 with equal G-value.
After deleting one generator a, both restricted words are
supported in A\{a}, with size <= k. Downstairs, retractability
preserves equality after deletion. k-stability reflects that
equality back into G. If a is not in A, deletion changes nothing.

This module formalizes precisely that repaired rank argument.
It additionally proves stability of labelled quotients under
composition: needed for the composite final G -> H_k map in
corrected ABO Lemma 5.6.

No global (k+1)-retractability is silently assumed; the low
rank including k=0 is covered directly.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ Θ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

namespace LabelWord

/-- Erasing a signed generator a from an A-word leaves a genuine
word supported on A with a removed, for both positive and
inverse occurrences. -/
theorem uses_eraseGenerator (A : Finset ι) (a : ι) :
    ∀ (w : LabelWord ι),
      Uses A w → Uses (A.erase a) (eraseGenerator a w) := by
  intro w
  induction w with
  | nil =>
      intro _
      trivial
  | cons s w ih =>
      intro hw
      have hs : signedBase s ∈ A := hw.1
      have ht : Uses (A.erase a) (eraseGenerator a w) :=
        ih hw.2
      by_cases h : signedBase s = a
      · have hm : signedBase s ∈ ({a} : Finset ι) := by
          simp [h]
        simpa [eraseGenerator, deleteGenerators, hm] using ht
      · have hnot : signedBase s ∉ ({a} : Finset ι) := by
          simpa using h
        have hA : signedBase s ∈ A.erase a :=
          Finset.mem_erase.mpr ⟨h, hs⟩
        simpa [eraseGenerator, deleteGenerators, hnot] using
          (show signedBase s ∈ A.erase a ∧
            Uses (A.erase a) (eraseGenerator a w) from ⟨hA, ht⟩)

/-- Every signed generator word uses the full finite alphabet. -/
theorem uses_univ (w : LabelWord ι) :
    Uses Finset.univ w := by
  induction w with
  | nil =>
      trivial
  | cons s w ih =>
      exact ⟨Finset.mem_univ _, ih⟩

end LabelWord

/-- Retractability up to rank k: deletion of one generator respects
all group word equalities whose original words use a common
subalphabet of size at most k. No claim about larger supports. -/
def KRetractable (gen : ι → Γ) (k : ℕ) : Prop :=
  ∀ (A : Finset ι), A.card ≤ k →
    ∀ (a : ι) (p q : LabelWord ι),
      LabelWord.Uses A p → LabelWord.Uses A q →
      PSTS.SignedWord.evalGroup gen p =
        PSTS.SignedWord.evalGroup gen q →
      PSTS.SignedWord.evalGroup gen (LabelWord.eraseGenerator a p) =
        PSTS.SignedWord.evalGroup gen (LabelWord.eraseGenerator a q)

/-- Global retractability implies every finite-rank version. -/
theorem kRetractable_of_retractable
    (gen : ι → Γ) (hret : Retractable gen) (k : ℕ) :
    KRetractable gen k := by
  intro A hsize a p q hp hq heq
  exact hret a p q heq

namespace LabelledGroupQuotient

variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable (Q : LabelledGroupQuotient genΓ genΔ)

/-- The missing implication in the printed hypotheses of
corrected ABO Theorem 4.7 (repair R1).

A k-stable labelled group quotient into a (k+1)-retractable
group has a (k+1)-retractable domain. For a generator a in A,
deletion lowers the support rank by one; H-retractability
gives equality downstairs, and stability reflects it upstairs.
If a lies outside A, erasure is the identity already upstairs. -/
theorem kRetractable_of_kStable
    (k : ℕ)
    (hstable : Q.KStable k)
    (hretDown : KRetractable genΔ (k + 1)) :
    KRetractable genΓ (k + 1) := by
  intro A hA a p q hp hq heq
  by_cases ha : a ∈ A
  · have hsmall : (A.erase a).card ≤ k :=
      Nat.lt_succ_iff.mp
        (lt_of_lt_of_le (Finset.card_erase_lt_of_mem ha) hA)
    have hpErase :
        LabelWord.Uses (A.erase a) (LabelWord.eraseGenerator a p) :=
      LabelWord.uses_eraseGenerator A a p hp
    have hqErase :
        LabelWord.Uses (A.erase a) (LabelWord.eraseGenerator a q) :=
      LabelWord.uses_eraseGenerator A a q hq
    have hDown :
        PSTS.SignedWord.evalGroup genΔ p =
          PSTS.SignedWord.evalGroup genΔ q := by
      calc
        PSTS.SignedWord.evalGroup genΔ p =
            Q.hom (PSTS.SignedWord.evalGroup genΓ p) :=
          (Q.map_evalGroup p).symm
        _ = Q.hom (PSTS.SignedWord.evalGroup genΓ q) :=
          congrArg Q.hom heq
        _ = PSTS.SignedWord.evalGroup genΔ q :=
          Q.map_evalGroup q
    have hDownErase :
        PSTS.SignedWord.evalGroup genΔ
            (LabelWord.eraseGenerator a p) =
          PSTS.SignedWord.evalGroup genΔ
            (LabelWord.eraseGenerator a q) :=
      hretDown A hA a p q hp hq hDown
    exact Q.evalGroup_eq_of_stableAt
      (hstable (A.erase a) hsmall) hpErase hqErase hDownErase
  · have hpNo : LabelWord.eraseGenerator a p = p := by
      apply LabelWord.eraseGenerator_eq_self_of_all_base_ne a p
      intro s hs hsa
      have hm : signedBase s ∈ A :=
        LabelWord.mem_base_of_uses A p hp s hs
      exact ha (by simpa [hsa] using hm)
    have hqNo : LabelWord.eraseGenerator a q = q := by
      apply LabelWord.eraseGenerator_eq_self_of_all_base_ne a q
      intro s hs hsa
      have hm : signedBase s ∈ A :=
        LabelWord.mem_base_of_uses A q hq s hs
      exact ha (by simpa [hsa] using hm)
    simpa [hpNo, hqNo] using heq

/-- A source-friendly version of repair R1 when the target
group is globally retractable. -/
theorem kRetractable_of_retractable_target
    (k : ℕ) (hstable : Q.KStable k)
    (hretDown : Retractable genΔ) :
    KRetractable genΓ (k + 1) :=
  Q.kRetractable_of_kStable k hstable
    (kRetractable_of_retractable genΔ hretDown (k + 1))

/-- In particular, if the whole generator alphabet has at most
k+1 elements, a k-stable quotient onto a retractable group
forces full retractability upstairs. This is the exact missing
G-retractability justification needed by Theorem 4.7 in the
source when its ambient alphabet has rank k+1. -/
theorem retractable_of_kStable
    (k : ℕ) (hstable : Q.KStable k)
    (hretDown : Retractable genΔ)
    (hcard : Fintype.card ι ≤ k + 1) :
    Retractable genΓ := by
  have hlocal : KRetractable genΓ (k + 1) :=
    Q.kRetractable_of_retractable_target k hstable hretDown
  intro a p q heq
  exact hlocal Finset.univ (by simpa using hcard)
    a p q (LabelWord.uses_univ p)
    (LabelWord.uses_univ q) heq

/-- Stability persists under composition of labelled quotients.
This is the small algebraic bridge needed when Section 5
uses k-stability of the WHOLE finite quotient chain from
the final G down to the intermediate H_k. -/
theorem kStable_comp
    [Group Θ] {genΘ : ι → Θ}
    (R : LabelledGroupQuotient genΔ genΘ)
    (k : ℕ) (hQ : Q.KStable k) (hR : R.KStable k) :
    (Q.comp R).KStable k := by
  intro A hA x y hxy
  have hRxy :
      R.subgroupHom A (Q.subgroupHom A x) =
        R.subgroupHom A (Q.subgroupHom A y) := by
    apply Subtype.ext
    exact congrArg Subtype.val hxy
  have hQxy : Q.subgroupHom A x = Q.subgroupHom A y :=
    (hR A hA) hRxy
  exact (hQ A hA) hQxy

end LabelledGroupQuotient
end ABO
end PSTSEPPA
