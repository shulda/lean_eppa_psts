import PSTSEPPA.ABO.CayleyEdgeWords
import PSTSEPPA.ABO.Retractability

/-!
# Retractability deletes a redundant positive Cayley edge AT GROUP VALUE

This is the algebraic half of the corrected ABO I Lemma 5.6.

The source first erases a particular positive EDGE generator e in an
arbitrary signed E-word, not a selected PSTS label in a signed P-word.
If an alternative same-G-value path avoids e and the E-generated group
is retractable, erasure preserves the EXACT final group value.

This module proves that step for actual signed Cayley paths using
the certified edge-word translation.

IMPORTANT: the erased E-word need NOT be a legal Cayley path.
Recovering a path of the same endpoints and exact G-value that
avoids e is the genuinely hard content of ABO Lemma 5.6 and
the corrected Section 4/5 construction. This file explicitly
does not assume that a word deletion is a path.
-/

namespace PSTSEPPA
namespace ABO

variable {Q G ι : Type*} [Group Q] [Group G]

namespace LabelWord

variable {E : Type*} [DecidableEq E]

/-- A word with no occurrence of a signed generator e is unchanged
by the literal edge-generator deletion operation from retractability. -/
theorem eraseGenerator_eq_self_of_all_base_ne (e : E) :
    ∀ (w : LabelWord E),
      (∀ s ∈ w, signedBase s ≠ e) →
      eraseGenerator e w = w := by
  intro w
  induction w with
  | nil =>
      intro _
      rfl
  | cons s w ih =>
      intro h
      have hs : signedBase s ≠ e :=
        h s (List.mem_cons_self)
      have hw : ∀ t ∈ w, signedBase t ≠ e := by
        intro t ht
        exact h t (List.mem_cons_of_mem s ht)
      have hnot : signedBase s ∉ ({e} : Finset E) := by
        simpa using hs
      simp [eraseGenerator, deleteGenerators, hnot, ih hw]

end LabelWord

/-- The generic ABO `signedBase` and our geometric
`signedPositiveBase` agree on the complete positive edge alphabet. -/
theorem cayleyEdgeWord_bases_signedBase
    (gen : ι → Q) (q : Q) (w : LabelWord ι) :
    (cayleyEdgeWord gen q w).map signedBase =
      cayleyWordPositiveTrace gen q w := by
  have h : (signedBase : SignedLabel (Q × ι) → Q × ι) =
      signedPositiveBase := by
    funext s
    cases s <;> rfl
  rw [h]
  exact cayleyEdgeWord_bases gen q w

/-- If a positive edge e is absent from a true Cayley path,
the signed E-word of the path is fixed by deleting e. -/
theorem cayleyEdgeWord_erase_unvisited
    [DecidableEq Q] [DecidableEq ι]
    (gen : ι → Q) (q : Q) (w : LabelWord ι)
    (e : Q × ι)
    (he : e ∉ cayleyWordPositiveTrace gen q w) :
    LabelWord.eraseGenerator e (cayleyEdgeWord gen q w) =
      cayleyEdgeWord gen q w := by
  apply LabelWord.eraseGenerator_eq_self_of_all_base_ne
  intro s hs heq
  have hMap :
      signedBase s ∈ (cayleyEdgeWord gen q w).map signedBase :=
    List.mem_map.mpr ⟨s, hs, rfl⟩
  rw [cayleyEdgeWord_bases_signedBase] at hMap
  rw [heq] at hMap
  exact he hMap

/-- Actual source step: if two signed Cayley paths have the
same FINAL G-value and the second one avoids positive edge e,
then deleting e from the signed E-word of the first path
does not change its final G-value.

This is strictly weaker than the endpoint-preserving
replacement-path lemma: the deleted word need not be a path. -/
theorem cayleyPathGroupValue_erase_one_of_retractable
    [Fintype Q] [Fintype ι]
    [DecidableEq Q] [DecidableEq ι]
    (gen : ι → Q) (edge : Q × ι → G)
    (hret : Retractable edge)
    (q : Q) (u v : LabelWord ι) (e : Q × ι)
    (hval : cayleyPathGroupValue gen edge q u =
      cayleyPathGroupValue gen edge q v)
    (heAvoid : e ∉ cayleyWordPositiveTrace gen q v) :
    PSTS.SignedWord.evalGroup edge
      (LabelWord.eraseGenerator e (cayleyEdgeWord gen q u)) =
      cayleyPathGroupValue gen edge q u := by
  have hEq :
      PSTS.SignedWord.evalGroup edge (cayleyEdgeWord gen q u) =
      PSTS.SignedWord.evalGroup edge (cayleyEdgeWord gen q v) := by
    rw [cayleyEdgeWord_eval, cayleyEdgeWord_eval]
    exact hval
  have hEraseEq :=
    hret e (cayleyEdgeWord gen q u) (cayleyEdgeWord gen q v) hEq
  rw [cayleyEdgeWord_erase_unvisited gen q v e heAvoid] at hEraseEq
  calc
    PSTS.SignedWord.evalGroup edge
        (LabelWord.eraseGenerator e (cayleyEdgeWord gen q u)) =
      PSTS.SignedWord.evalGroup edge (cayleyEdgeWord gen q v) :=
        hEraseEq
    _ = cayleyPathGroupValue gen edge q v :=
      cayleyEdgeWord_eval gen edge q v
    _ = cayleyPathGroupValue gen edge q u := hval.symm

end ABO
end PSTSEPPA
