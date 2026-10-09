import PSTSEPPA.ABO.CosetConnectivity
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Card

/-!
# Canonical least group-generator content of retractable labelled groups

This is the purely ALGEBRAIC Proposition 3.5 / Definition 3.4 step
in corrected ABO I: a generated retractable group has a unique least
positive-generator support in every group-value fibre.

The earlier certified subgroup-intersection theorem
  G[A] ∩ G[B] = G[A ∩ B]
implies any two signed words of equal group value admit a third
signed word of that value whose positive-generator support is
contained in the intersection of their supports.

Minimise support cardinality in each group-value fibre and apply
that intersection lemma to prove that the chosen representative's
support lies in the support of EVERY other representative.
The resulting finite support is realised by an actual word, not
merely defined as a formal intersection of potentially infinitely
many supports. No external group-theoretic theorem is assumed.

This is NOT the stronger geometric Cayley path-content theorem:
the new representing word need not be a path between prescribed
vertices of an oriented input graph. The latter requires the
corrected ABO Lemma 5.6.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace LabelWord

/-- The finite set of unsigned positive GROUP GENERATORS occurring
in a signed word, not the vertices/edges of a Cayley walk. -/
def positiveSupport (w : LabelWord ι) : Finset ι :=
  (w.map signedBase).toFinset

/-- A word uses A whenever all of its individual unsigned
generator letters lie in A. -/
theorem uses_of_all (A : Finset ι) :
    ∀ w : LabelWord ι,
      (∀ s ∈ w, signedBase s ∈ A) → Uses A w := by
  intro w
  induction w with
  | nil =>
      intro _
      trivial
  | cons s w ih =>
      intro h
      have hs : signedBase s ∈ A :=
        h s List.mem_cons_self
      have hw : ∀ t ∈ w, signedBase t ∈ A := by
        intro t ht
        exact h t (List.mem_cons_of_mem s ht)
      exact ⟨hs, ih hw⟩

/-- Every word uses precisely the support obtained by
forgetting the signs of its letters. -/
theorem uses_positiveSupport (w : LabelWord ι) :
    Uses (positiveSupport w) w := by
  apply uses_of_all
  intro s hs
  have hMem : signedBase s ∈ w.map signedBase :=
    List.mem_map.mpr ⟨s, hs, rfl⟩
  simpa [positiveSupport] using hMem

/-- Any signed letter appearing in an A-word has its base in A. -/
theorem mem_base_of_uses (A : Finset ι) :
    ∀ (w : LabelWord ι), Uses A w →
      ∀ s ∈ w, signedBase s ∈ A := by
  intro w
  induction w with
  | nil =>
      intro _ s hs
      cases hs
  | cons t w ih =>
      intro hw s hs
      rcases List.mem_cons.mp hs with hEq | hTail
      · rw [hEq]
        exact hw.1
      · exact ih hw.2 s hTail

/-- An A-supported signed word has unsigned support contained in A. -/
theorem positiveSupport_subset_of_uses
    (A : Finset ι) (w : LabelWord ι)
    (hw : Uses A w) :
    positiveSupport w ⊆ A := by
  intro i hi
  have hiList : i ∈ w.map signedBase := by
    simpa [positiveSupport] using hi
  obtain ⟨s, hs, hsBase⟩ := List.mem_map.mp hiList
  rw [← hsBase]
  exact mem_base_of_uses A w hw s hs

end LabelWord

/-- Genuine pairwise INTERSECTION of group-generator contents.
This is a word-level consequence of the already checked retractable
subgroup intersection theorem, with NO endpoint/path claim. -/
theorem retractable_sameValue_wordSupport_inter
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen)
    (u v : LabelWord ι)
    (huv : PSTS.SignedWord.evalGroup gen u =
      PSTS.SignedWord.evalGroup gen v) :
    ∃ w : LabelWord ι,
      PSTS.SignedWord.evalGroup gen w =
        PSTS.SignedWord.evalGroup gen u ∧
      LabelWord.positiveSupport w ⊆ LabelWord.positiveSupport u ∧
      LabelWord.positiveSupport w ⊆ LabelWord.positiveSupport v := by
  let A := LabelWord.positiveSupport u
  let B := LabelWord.positiveSupport v
  have huA :
      PSTS.SignedWord.evalGroup gen u ∈ generatedSubgroup gen A :=
    evalGroup_mem_generatedSubgroup_of_uses gen A
      (LabelWord.uses_positiveSupport u)
  have hvB :
      PSTS.SignedWord.evalGroup gen u ∈ generatedSubgroup gen B := by
    rw [huv]
    exact evalGroup_mem_generatedSubgroup_of_uses gen B
      (LabelWord.uses_positiveSupport v)
  have hInter :
      PSTS.SignedWord.evalGroup gen u ∈
        generatedSubgroup gen (A ∩ B) := by
    rw [← generatedSubgroup_inf gen hgen hret A B]
    exact ⟨huA, hvB⟩
  obtain ⟨w, hwUses, hwVal⟩ :=
    exists_word_uses_eq_of_mem_generatedSubgroup
      gen (A ∩ B) hInter
  have hwAB :
      LabelWord.positiveSupport w ⊆ A ∩ B :=
    LabelWord.positiveSupport_subset_of_uses (A ∩ B) w hwUses
  refine ⟨w, hwVal, ?_, ?_⟩
  · intro e he
    exact (Finset.mem_inter.mp (hwAB he)).1
  · intro e he
    exact (Finset.mem_inter.mp (hwAB he)).2

namespace RetractableGroupContent

variable (gen : ι → Γ) (hgen : IsGenerated gen)

/-- There is at least one word in every group fibre and hence
at least one (natural-valued) support cardinality. -/
theorem exists_support_card (g : Γ) :
    ∃ n : ℕ, ∃ w : LabelWord ι,
      PSTS.SignedWord.evalGroup gen w = g ∧
      (LabelWord.positiveSupport w).card = n := by
  obtain ⟨w, hw⟩ := hgen.exists_evalGroup_eq g
  exact ⟨(LabelWord.positiveSupport w).card, w, hw, rfl⟩

/-- Least cardinality among supports representing the group element g. -/
noncomputable def leastSupportCard (g : Γ) : ℕ := by
  classical
  exact Nat.find (exists_support_card gen hgen g)

/-- A representative of group element g with the least NUMBER
of distinct generator labels. No content minimality is assumed. -/
noncomputable def leastWord (g : Γ) : LabelWord ι := by
  classical
  exact Classical.choose (Nat.find_spec (exists_support_card gen hgen g))

theorem leastWord_spec (g : Γ) :
    PSTS.SignedWord.evalGroup gen (leastWord gen hgen g) = g ∧
    (LabelWord.positiveSupport (leastWord gen hgen g)).card =
      leastSupportCard gen hgen g := by
  classical
  exact Classical.choose_spec
    (Nat.find_spec (exists_support_card gen hgen g))

theorem leastWord_card_le
    (g : Γ) (v : LabelWord ι)
    (hv : PSTS.SignedWord.evalGroup gen v = g) :
    (LabelWord.positiveSupport (leastWord gen hgen g)).card ≤
      (LabelWord.positiveSupport v).card := by
  classical
  calc
    (LabelWord.positiveSupport (leastWord gen hgen g)).card =
        leastSupportCard gen hgen g := (leastWord_spec gen hgen g).2
    _ ≤ (LabelWord.positiveSupport v).card :=
      Nat.find_min' (exists_support_card gen hgen g) ⟨v, hv, rfl⟩

/-- For a retractable labelled group, least cardinality upgrades
to LEAST INCLUSION content in every group-value fibre. -/
theorem leastWord_support_subset
    (hret : Retractable gen)
    (g : Γ) (v : LabelWord ι)
    (hv : PSTS.SignedWord.evalGroup gen v = g) :
    LabelWord.positiveSupport (leastWord gen hgen g) ⊆
      LabelWord.positiveSupport v := by
  have hSame :
      PSTS.SignedWord.evalGroup gen (leastWord gen hgen g) =
        PSTS.SignedWord.evalGroup gen v :=
    (leastWord_spec gen hgen g).1.trans hv.symm
  obtain ⟨w, hwVal, hwSub, hwSubV⟩ :=
    retractable_sameValue_wordSupport_inter
      gen hgen hret (leastWord gen hgen g) v hSame
  have hwg :
      PSTS.SignedWord.evalGroup gen w = g :=
    hwVal.trans (leastWord_spec gen hgen g).1
  have hCard :
      (LabelWord.positiveSupport (leastWord gen hgen g)).card ≤
        (LabelWord.positiveSupport w).card :=
    leastWord_card_le gen hgen g w hwg
  have hEq :
      LabelWord.positiveSupport w =
        LabelWord.positiveSupport (leastWord gen hgen g) :=
    Finset.eq_of_subset_of_card_le hwSub hCard
  rw [← hEq]
  exact hwSubV

/-- The genuine canonical finite content of each group element,
realised by a signed word of that value, and contained in the
content of EVERY other representing word. -/
noncomputable def content (g : Γ) : Finset ι :=
  LabelWord.positiveSupport (leastWord gen hgen g)

theorem content_is_represented (g : Γ) :
    ∃ w : LabelWord ι,
      PSTS.SignedWord.evalGroup gen w = g ∧
      LabelWord.positiveSupport w = content gen hgen g :=
  ⟨leastWord gen hgen g, (leastWord_spec gen hgen g).1, rfl⟩

theorem content_subset_of_representation
    (hret : Retractable gen) (g : Γ) (v : LabelWord ι)
    (hv : PSTS.SignedWord.evalGroup gen v = g) :
    content gen hgen g ⊆ LabelWord.positiveSupport v :=
  leastWord_support_subset gen hgen hret g v hv

end RetractableGroupContent
end ABO
end PSTSEPPA
