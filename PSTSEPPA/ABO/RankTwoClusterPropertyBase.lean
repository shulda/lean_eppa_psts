import PSTSEPPA.ABO.RankTwoClusterSupportBase
import PSTSEPPA.ABO.CayleySubgraphAdmissibility

/-!
# Unconditional rank-two cluster-property base, for any Cayley skeleton

ABO Proposition 4.4 states that the rank-two coset-extension
induction has a trivial cluster-property base. Admissibility is
already known to hold for any Cayley skeleton with |A|≤2,
without an extra hypothesis.

We package the two independent, Lean-checked rank-two
lemmas into one source-facing result:
  * each actual B-component of the full proper-alphabet
    multi-CE is a selected completed tagged B-coset, or
  * it is a singleton, and that singleton has a unique
    inclusion-least component-tagged support, universally
    minimal over the entire B-component.

The theorem constructs the extension using the proved low-rank
admissibility lemma instead of taking admissibility as an
unproved input. The ambient group still requires the source's
generation and retractability hypotheses.

This closes the *base-case component support/shape gate*,
not the higher-rank cluster-property induction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- With |A|≤2 no separate admissibility premise is necessary:
each full proper-family B-component is either a completed
tagged full B-coset, or a singleton with a least support
universal over all vertices in its whole B-component. -/
theorem rank_two_B_component_full_or_singleton_with_core_support
    (hcard : A.card ≤ 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard) hgen hret) :
    (∃ p : K.AttachedCosetVertex B,
      z = K.multiCosetInclude (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard) hgen hret
        B hBP p ∧
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard) hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            (K.admissible_of_card_le_two hcard)
            hgen hret).Follows z w y) ↔
        ∃ q : K.AttachedCosetVertex B,
          q.1 = p.1 ∧
          y = K.multiCosetInclude (allProperCosetFamily A)
            (K.admissible_of_card_le_two hcard)
            hgen hret B hBP q) ∨
    ((∀ y : K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard) hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            (K.admissible_of_card_le_two hcard)
            hgen hret).Follows z w y) → y = z) ∧
      ∃ (M : Finset ι)
        (hMP : M ∈ (allProperCosetFamily A).alphabets)
        (p : K.AttachedCosetVertex M),
        K.multiCosetInclude (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard)
          hgen hret M hMP p = z ∧
        ∀ (y : K.MultiCosetVertex (allProperCosetFamily A)
              (K.admissible_of_card_le_two hcard)
              hgen hret),
          (∃ w : LabelWord ι, LabelWord.Uses B w ∧
            (K.multiCosetEGraph (allProperCosetFamily A)
              (K.admissible_of_card_le_two hcard)
              hgen hret).Follows z w y) →
          ∀ (C : Finset ι)
            (hCP : C ∈ (allProperCosetFamily A).alphabets)
            (q : K.AttachedCosetVertex C),
            K.multiCosetInclude (allProperCosetFamily A)
              (K.admissible_of_card_le_two hcard)
              hgen hret C hCP q = y →
            ∃ hMC : M ⊆ C,
              K.attachedSubalphabetMap M C hMC p = q) := by
  let hadm : K.AdmissibleForCosetExtension :=
    K.admissible_of_card_le_two hcard
  by_cases hPresent :
      ∃ p : K.AttachedCosetVertex B,
        K.multiCosetInclude (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard)
          hgen hret B hBP p = z
  · left
    obtain ⟨p, hp⟩ := hPresent
    refine ⟨p, hp.symm, ?_⟩
    intro y
    rw [← hp]
    exact K.multiCoset_selected_B_component_exact
      (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard)
      hgen hret B hBP p y
  · right
    constructor
    · intro y hzy
      exact K.rank_two_off_selected_B_component_singleton
        (K.admissible_of_card_le_two hcard)
        hgen hret hcard B hBP z hPresent y hzy
    · exact K.rank_two_off_B_component_unique_minimal_support
        (K.admissible_of_card_le_two hcard)
        hgen hret hcard B hBP z hPresent

end CayleySubgraphSpec
end ABO
end PSTSEPPA
