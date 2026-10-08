import PSTSEPPA.ABO.AdmissibleAttachedIntersection

/-!
# Coset overlap refinement with equal and nested parameters

The strict-subalphabet common-refinement theorem is insufficient for the
transitivity step in ABO equation (3.10): when intersecting alphabets B₁,
B₂ and B₃, one or both of B₁ ∩ B₂ and B₂ ∩ B₃ can equal B₂.

This lemma extends the earlier refinement theorem to arbitrary *non-strict*
subsets C₁,C₂ ⊆ B, treating the cases C₁ = B and C₂ = B separately.
Thus no strict-inclusion result is invoked in a degenerate case (repair R5).

The ambient parent B remains proper in A, as required by admissibility.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Common-refinement property for *all* C₁,C₂ ⊆ B, including C₁=B,
C₂=B, equal constituents, nesting, and empty alphabets. -/
theorem attachedSubalphabetMap_common_refinement_le
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C₁ C₂ : Finset ι)
    (hBA : B ⊂ A)
    (hC₁ : C₁ ⊆ B)
    (hC₂ : C₂ ⊆ B)
    (p : K.AttachedCosetVertex C₁)
    (q : K.AttachedCosetVertex C₂)
    (heq :
      K.attachedSubalphabetMap C₁ B hC₁ p =
        K.attachedSubalphabetMap C₂ B hC₂ q) :
    ∃ r : K.AttachedCosetVertex (C₁ ∩ C₂),
      K.attachedSubalphabetMap (C₁ ∩ C₂) C₁
          Finset.inter_subset_left r = p ∧
      K.attachedSubalphabetMap (C₁ ∩ C₂) C₂
          Finset.inter_subset_right r = q := by
  by_cases hEq₁ : C₁ = B
  · subst C₁
    have hmeet : B ∩ C₂ = C₂ :=
      Finset.inter_eq_right.mpr hC₂
    rw [hmeet]
    refine ⟨q, ?_, ?_⟩
    · have hfirst : p = K.attachedSubalphabetMap C₂ B hC₂ q := by
        calc
          p = K.attachedSubalphabetMap B B hC₁ p :=
            (K.attachedSubalphabetMap_self B p).symm
          _ = K.attachedSubalphabetMap C₂ B hC₂ q := heq
      exact hfirst.symm
    · exact K.attachedSubalphabetMap_self C₂ q
  · by_cases hEq₂ : C₂ = B
    · subst C₂
      have hmeet : C₁ ∩ B = C₁ :=
        Finset.inter_eq_left.mpr hC₁
      rw [hmeet]
      refine ⟨p, ?_, ?_⟩
      · exact K.attachedSubalphabetMap_self C₁ p
      · calc
          K.attachedSubalphabetMap C₁ B hC₁ p =
              K.attachedSubalphabetMap B B hC₂ q := heq
          _ = q := K.attachedSubalphabetMap_self B q
    · have hstrict₁ : C₁ ⊂ B := by
        refine ⟨hC₁, ?_⟩
        intro hback
        exact hEq₁ (Finset.Subset.antisymm hC₁ hback)
      have hstrict₂ : C₂ ⊂ B := by
        refine ⟨hC₂, ?_⟩
        intro hback
        exact hEq₂ (Finset.Subset.antisymm hC₂ hback)
      exact K.attachedSubalphabetMap_common_refinement
        hadm hgen hret B C₁ C₂ hBA hstrict₁ hstrict₂ p q heq

end CayleySubgraphSpec
end ABO
end PSTSEPPA
