import PSTSEPPA.ABO.LocalRankRetractableSubalphabet
import PSTSEPPA.ABO.CosetConnectivity

/-!
# Subalphabet coset intersections from bounded retractability

The original ABO coset-intersection theorem assumes globally retractable
labelled groups.  At intermediate stages of the corrected Section 5
induction one only has `KRetractable gen k`.

The exact local replacement is enough for a pair of alphabets A and B
provided |A ∪ B| ≤ k.  Its proof works directly with actual signed
words, and does not assume that the generators are independent,
faithful, nontrivial or even that they generate the whole group.

The essential bounded word-calculus step is that deleting an arbitrary
set of generators preserves an equality of two words if both words
started in ONE common support alphabet of size ≤k.  The intermediate
words are still supported on that alphabet, so the argument does not
silently apply k-retractability outside its scope.

This proves exact subgroup/coset intersections and genuine
intersection-alphabet connectivity at this rank.  For k=2 it applies
to subalphabets of one fixed rank-two parent; it does NOT claim
arbitrary two rank-two cosets have connected intersections.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace LabelWord

/-- Inclusion of support alphabets preserves word support, with both signs. -/
theorem Uses.mono (A B : Finset ι) (hAB : A ⊆ B) :
    ∀ (w : LabelWord ι), Uses A w → Uses B w := by
  intro w
  induction w with
  | nil => intro _; trivial
  | cons s w ih =>
      intro hw
      exact ⟨hAB hw.1, ih hw.2⟩

/-- Erasing arbitrary signed letters never introduces new support. -/
theorem Uses.deleteGenerators (A E : Finset ι) :
    ∀ (w : LabelWord ι), Uses A w →
      Uses A (deleteGenerators E w) := by
  intro w
  induction w with
  | nil => intro _; trivial
  | cons s w ih =>
      intro hw
      by_cases hs : signedBase s ∈ E
      · simpa [deleteGenerators, hs] using ih hw.2
      · simpa [deleteGenerators, hs, Uses] using
          (show signedBase s ∈ A ∧ Uses A (deleteGenerators E w)
            from ⟨hw.1, ih hw.2⟩)

/-- A word which already uses only B is unchanged by B-restriction. -/
theorem restrictTo_eq_self_of_uses (B : Finset ι) :
    ∀ (w : LabelWord ι), Uses B w → restrictTo B w = w := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons s w ih =>
      intro hw
      have hs : signedBase s ∉ Finset.univ \ B := by
        simpa using hw.1
      simp [restrictTo, deleteGenerators, hs, ih hw.2]

/-- Two support conditions combine to support in the intersection. -/
theorem Uses.inter (A B : Finset ι) :
    ∀ (w : LabelWord ι),
      Uses A w → Uses B w → Uses (A ∩ B) w := by
  intro w
  induction w with
  | nil => intro _ _; trivial
  | cons s w ih =>
      intro hA hB
      exact ⟨Finset.mem_inter.mpr ⟨hA.1, hB.1⟩,
        ih hA.2 hB.2⟩

end LabelWord

/-- Bounded retractability is closed under deletion of an ARBITRARY
finite family E of letters as long as the original common support D
has cardinality at most k. No assumption E ⊆ D is required. -/
theorem KRetractable.deleteGenerators_eq_of_uses
    (gen : ι → Γ) {k : ℕ} (hret : KRetractable gen k)
    (D : Finset ι) (hD : D.card ≤ k) (E : Finset ι) :
    ∀ (p q : LabelWord ι),
      LabelWord.Uses D p → LabelWord.Uses D q →
      PSTS.SignedWord.evalGroup gen p =
        PSTS.SignedWord.evalGroup gen q →
      PSTS.SignedWord.evalGroup gen (LabelWord.deleteGenerators E p) =
        PSTS.SignedWord.evalGroup gen (LabelWord.deleteGenerators E q) := by
  induction E using Finset.induction_on with
  | empty =>
      intro p q _ _ heq
      simpa using heq
  | @insert a E ha ih =>
      intro p q hp hq heq
      have hp' : LabelWord.Uses D (LabelWord.eraseGenerator a p) :=
        LabelWord.Uses.deleteGenerators D {a} p hp
      have hq' : LabelWord.Uses D (LabelWord.eraseGenerator a q) :=
        LabelWord.Uses.deleteGenerators D {a} q hq
      rw [LabelWord.deleteGenerators_insert,
        LabelWord.deleteGenerators_insert]
      exact ih _ _ hp' hq' (hret D hD a p q hp hq heq)

/-- Local word restriction respects equal group values when their common
support D has at most k labels; this is the bounded version of the
unrestricted `Retractable.restrictTo_eq`. -/
theorem KRetractable.restrictTo_eq_of_uses
    (gen : ι → Γ) {k : ℕ} (hret : KRetractable gen k)
    (D : Finset ι) (hD : D.card ≤ k) (B : Finset ι)
    (p q : LabelWord ι)
    (hp : LabelWord.Uses D p) (hq : LabelWord.Uses D q)
    (heq : PSTS.SignedWord.evalGroup gen p =
      PSTS.SignedWord.evalGroup gen q) :
    PSTS.SignedWord.evalGroup gen (LabelWord.restrictTo B p) =
      PSTS.SignedWord.evalGroup gen (LabelWord.restrictTo B q) := by
  exact KRetractable.deleteGenerators_eq_of_uses gen hret D hD
    (Finset.univ \ B) p q hp hq heq

/-- LOCAL version of the subgroup-intersection identity:
k-retractability alone suffices whenever the UNION of the two
alphabets has size ≤k. No ambient generatedness is needed. -/
theorem generatedSubgroup_inf_of_kRetractable
    (gen : ι → Γ) {k : ℕ} (hret : KRetractable gen k)
    (A B : Finset ι) (hcard : (A ∪ B).card ≤ k) :
    generatedSubgroup gen A ⊓ generatedSubgroup gen B =
      generatedSubgroup gen (A ∩ B) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p, hp, hpval⟩ :=
      exists_word_uses_eq_of_mem_generatedSubgroup gen A hx.1
    obtain ⟨q, hq, hqval⟩ :=
      exists_word_uses_eq_of_mem_generatedSubgroup gen B hx.2
    have hpD : LabelWord.Uses (A ∪ B) p :=
      LabelWord.Uses.mono A (A ∪ B) Finset.subset_union_left p hp
    have hqD : LabelWord.Uses (A ∪ B) q :=
      LabelWord.Uses.mono B (A ∪ B) Finset.subset_union_right q hq
    have hEq : PSTS.SignedWord.evalGroup gen p =
        PSTS.SignedWord.evalGroup gen q := hpval.trans hqval.symm
    have hRestricted :=
      KRetractable.restrictTo_eq_of_uses gen hret (A ∪ B) hcard B
        p q hpD hqD hEq
    have hVal :
        PSTS.SignedWord.evalGroup gen (LabelWord.restrictTo B p) = x := by
      calc
        PSTS.SignedWord.evalGroup gen (LabelWord.restrictTo B p) =
            PSTS.SignedWord.evalGroup gen (LabelWord.restrictTo B q) :=
          hRestricted
        _ = PSTS.SignedWord.evalGroup gen q := by
          rw [LabelWord.restrictTo_eq_self_of_uses B q hq]
        _ = x := hqval
    have hpA :
        LabelWord.Uses A (LabelWord.restrictTo B p) :=
      LabelWord.Uses.deleteGenerators A (Finset.univ \ B) p hp
    have hpB : LabelWord.Uses B (LabelWord.restrictTo B p) :=
      LabelWord.uses_restrictTo B p
    have hpAB : LabelWord.Uses (A ∩ B) (LabelWord.restrictTo B p) :=
      LabelWord.Uses.inter A B _ hpA hpB
    rw [← hVal]
    exact evalGroup_mem_generatedSubgroup_of_uses gen (A ∩ B) hpAB
  · intro x hx
    have hA :
        generatedSubgroup gen (A ∩ B) ≤ generatedSubgroup gen A :=
      generatedSubgroup_mono gen Finset.inter_subset_left
    have hB :
        generatedSubgroup gen (A ∩ B) ≤ generatedSubgroup gen B :=
      generatedSubgroup_mono gen Finset.inter_subset_right
    exact ⟨hA hx, hB hx⟩

/-- Exact intersection of actual left cosets over a rank-bounded
common support alphabet, based at any point in the intersection. -/
theorem generatedLeftCoset_inter_of_kRetractable
    (gen : ι → Γ) {k : ℕ} (hret : KRetractable gen k)
    (A B : Finset ι) (hcard : (A ∪ B).card ≤ k)
    (g h z : Γ)
    (hzA : z ∈ generatedLeftCoset gen A g)
    (hzB : z ∈ generatedLeftCoset gen B h) :
    generatedLeftCoset gen A g ∩ generatedLeftCoset gen B h =
      generatedLeftCoset gen (A ∩ B) z := by
  rw [generatedLeftCoset_eq_of_mem gen A hzA,
    generatedLeftCoset_eq_of_mem gen B hzB]
  ext x
  constructor
  · rintro ⟨hxA, hxB⟩
    change z⁻¹ * x ∈ generatedSubgroup gen A at hxA
    change z⁻¹ * x ∈ generatedSubgroup gen B at hxB
    change z⁻¹ * x ∈ generatedSubgroup gen (A ∩ B)
    have hInf :
        z⁻¹ * x ∈
          generatedSubgroup gen A ⊓ generatedSubgroup gen B :=
      ⟨hxA, hxB⟩
    rwa [generatedSubgroup_inf_of_kRetractable gen hret A B hcard] at hInf
  · intro hx
    change z⁻¹ * x ∈ generatedSubgroup gen (A ∩ B) at hx
    have hInf :
        z⁻¹ * x ∈
          generatedSubgroup gen A ⊓ generatedSubgroup gen B := by
      rwa [generatedSubgroup_inf_of_kRetractable gen hret A B hcard]
    exact ⟨hInf.1, hInf.2⟩

/-- The local coset intersection is genuinely path-connected using
only the intersection labels (not merely a set-theoretic equality). -/
theorem generatedLeftCoset_inter_connected_of_kRetractable
    (gen : ι → Γ) {k : ℕ} (hret : KRetractable gen k)
    (A B : Finset ι) (hcard : (A ∪ B).card ≤ k)
    (g h : Γ)
    (hne : (generatedLeftCoset gen A g ∩
      generatedLeftCoset gen B h).Nonempty) :
    ∃ z : Γ,
      z ∈ generatedLeftCoset gen A g ∩ generatedLeftCoset gen B h ∧
      ∀ x : Γ,
        x ∈ generatedLeftCoset gen A g ∩ generatedLeftCoset gen B h →
          SubalphabetReachable gen (A ∩ B) z x := by
  obtain ⟨z, hzA, hzB⟩ := hne
  refine ⟨z, ⟨hzA, hzB⟩, ?_⟩
  intro x hx
  apply (mem_generatedLeftCoset_iff_subalphabetReachable gen (A ∩ B) z x).mp
  rw [← generatedLeftCoset_inter_of_kRetractable
    gen hret A B hcard g h z hzA hzB]
  exact hx

end ABO
end PSTSEPPA
