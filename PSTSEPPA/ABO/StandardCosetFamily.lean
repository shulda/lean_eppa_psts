import PSTSEPPA.ABO.MultiCosetWeakCompleteness
import PSTSEPPA.ABO.CayleySubgraphAdmissibility
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Omega

/-!
# Canonical family of all proper subalphabets for ABO coset extension

The source's full coset-extension construction uses the canonical
family P_A consisting of all proper subalphabets B ⊂ A, not an
arbitrary manually selected family. We formalize this finite family
and the precise rank assumptions needed for its properties.

* If A is nonempty, P_A contains the empty alphabet and therefore
  the union of its coset constituents contains a copy of the
  original skeleton.
* If |A| ≥ 2, each letter a∈A belongs to its proper singleton
  subalphabet {a}. Hence every old A-edge label is covered by a
  proper constituent and the canonical full coset extension is
  weakly complete.
* For |A| = 1 there is no proper subalphabet containing its unique
  letter. The rank-two bound is essential, rather than a proof gap.

This is the canonical specialization used for the subsequent
rank-induction arguments of ABO Sections 4 and 5.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

/-- The source-facing family of all strictly proper subalphabets
of A, as an actual finite CosetFamilySpec. -/
def allProperCosetFamily (A : Finset ι) : CosetFamilySpec A where
  alphabets :=
    (Finset.univ : Finset (Finset ι)).filter (fun B => B ⊂ A)
  proper := by
    intro B hBA
    exact (Finset.mem_filter.mp hBA).2

@[simp]
theorem mem_allProperCosetFamily
    (A B : Finset ι) :
    B ∈ (allProperCosetFamily A).alphabets ↔ B ⊂ A := by
  simp [allProperCosetFamily]

/-- The empty alphabet is selected whenever the ambient
alphabet A is nonempty. -/
theorem empty_mem_allProperCosetFamily
    (A : Finset ι) (hA : A.Nonempty) :
    (∅ : Finset ι) ∈ (allProperCosetFamily A).alphabets := by
  apply (mem_allProperCosetFamily A ∅).2
  refine ⟨Finset.empty_subset A, ?_⟩
  intro hsub
  rcases hA with ⟨i, hi⟩
  have hiEmpty : i ∈ (∅ : Finset ι) := hsub hi
  exact (Finset.not_mem_empty i) hiEmpty

/-- At rank at least two, a singleton letter is a strictly proper
subalphabet, even when other letters have trivial/repeated generator
images in Γ. -/
theorem singleton_ssubset_of_card_ge_two
    (A : Finset ι) (hcard : 2 ≤ A.card)
    (i : ι) (hi : i ∈ A) :
    ({i} : Finset ι) ⊂ A := by
  refine ⟨Finset.singleton_subset_iff.mpr hi, ?_⟩
  intro hAS
  have hle : A.card ≤ 1 := by
    have h := Finset.card_le_card hAS
    simpa using h
  omega

/-- Every old skeleton edge at rank at least two has its label
in a selected proper alphabet of P_A. -/
theorem allProperCosetFamily_covers_skeleton_labels
    (K : CayleySubgraphSpec gen A)
    (hcard : 2 ≤ A.card)
    (e : K.Edge) :
    ∃ B ∈ (allProperCosetFamily A).alphabets,
      signedBase e.1.2 ∈ B := by
  let i := signedBase e.1.2
  have hi : i ∈ A := K.label_mem e.1 e.2
  refine ⟨{i}, ?_, Finset.mem_singleton_self i⟩
  exact (mem_allProperCosetFamily A {i}).2
    (singleton_ssubset_of_card_ge_two A hcard i hi)

/-- The canonical full proper-subalphabet coset extension is
weakly complete for |A|≥2 and an admissible K: every signed
directed edge is represented by some completed constituent.
This is not completeness at every vertex. -/
theorem allProperCosetFamily_weaklyComplete
    (K : CayleySubgraphSpec gen A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card) :
    K.MultiCosetWeaklyComplete
      (allProperCosetFamily A) hadm hgen hret := by
  apply K.multiCosetWeaklyComplete_of_label_coverage
    (allProperCosetFamily A) hadm hgen hret
  intro e
  exact allProperCosetFamily_covers_skeleton_labels K hcard e

end ABO
end PSTSEPPA
