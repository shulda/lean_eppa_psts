import PSTSEPPA.ABO.ComponentIndexPairInjectivity
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.MultiCosetVertexSupport
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Actual intersection of two selected full coset components in a multi-CE

The full proper-alphabet multi-coset extension selects every
proper alphabet, so each original component-tagged B-coset is
an intrinsic B-component even in the presence of all other
(incomparable) constituent alphabets.

If a B-component and a C-component are both of these selected
full-coset types, their nonempty intersection is genuinely
(B∩C)-connected, as required by the easy skeleton/skeleton
case of ABO Proposition 3.23.

For any two intersection vertices z₁,z₂, exact overlap in the
multi-coset vertex quotient lifts each one to component-tagged
(B∩C)-points r₁,r₂. The parent B- and C-component tags of these
points agree, hence the (B∩C) tags are equal by admissibility
(Lemma 3.21). A real word path inside the single-(B∩C)
coset extension then maps to a real path in the whole multi-CE.

The proof does not use the full Definition 3.22 cluster property.
In particular it does not address off-skeleton cluster components.
Ambient Cayley-coordinate equality alone would be insufficient.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Intersections of two *selected complete coset* B/C-components
in the full proper-subalphabet multi-CE are intrinsically
(B∩C)-connected. The chosen anchor points may lie anywhere in
their respective component-tagged full cosets.

This is not the entire cluster-property-dependent Proposition
3.23, only its both-skeleton-meeting / selected full-coset case. -/
theorem allProperCoset_selected_BC_component_inter_connected
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (pB : K.AttachedCosetVertex B)
    (pC : K.AttachedCosetVertex C)
    (z₁ z₂ : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hz₁B : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
        (K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret B hBP pB) w z₁)
    (hz₂B : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
        (K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret B hBP pB) w z₂)
    (hz₁C : ∃ w : LabelWord ι, LabelWord.Uses C w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
        (K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP pC) w z₁)
    (hz₂C : ∃ w : LabelWord ι, LabelWord.Uses C w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
        (K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP pC) w z₂) :
    ∃ w : LabelWord ι, LabelWord.Uses (B ∩ C) w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z₁ w z₂ := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  have hBA : B ⊂ A := (mem_allProperCosetFamily A B).mp hBP
  have hCA : C ⊂ A := (mem_allProperCosetFamily A C).mp hCP
  have hDP : B ∩ C ∈ P.alphabets :=
    allProperCosetFamily_inter_mem A B C hBP hCP
  obtain ⟨b₁, hb₁, hz₁b⟩ :=
    (K.multiCoset_selected_B_component_exact
      P hadm hgen hret B hBP pB z₁).mp hz₁B
  obtain ⟨b₂, hb₂, hz₂b⟩ :=
    (K.multiCoset_selected_B_component_exact
      P hadm hgen hret B hBP pB z₂).mp hz₂B
  obtain ⟨c₁, hc₁, hz₁c⟩ :=
    (K.multiCoset_selected_B_component_exact
      P hadm hgen hret C hCP pC z₁).mp hz₁C
  obtain ⟨c₂, hc₂, hz₂c⟩ :=
    (K.multiCoset_selected_B_component_exact
      P hadm hgen hret C hCP pC z₂).mp hz₂C
  obtain ⟨r₁, hr₁, hr₁b, hr₁c⟩ :=
    K.multiCosetVertex_two_supports_intersection
      P hadm hgen hret z₁
      B C hBP hCP hDP b₁ c₁ hz₁b.symm hz₁c.symm
  obtain ⟨r₂, hr₂, hr₂b, hr₂c⟩ :=
    K.multiCosetVertex_two_supports_intersection
      P hadm hgen hret z₂
      B C hBP hCP hDP b₂ c₂ hz₂b.symm hz₂c.symm
  have hrB₁ :
      K.componentIndexMap (B ∩ C) B Finset.inter_subset_left r₁.1 =
        b₁.1 := by
    exact congrArg
      (fun t : K.AttachedCosetVertex B => t.1) hr₁b
  have hrB₂ :
      K.componentIndexMap (B ∩ C) B Finset.inter_subset_left r₂.1 =
        b₂.1 := by
    exact congrArg
      (fun t : K.AttachedCosetVertex B => t.1) hr₂b
  have hrC₁ :
      K.componentIndexMap (B ∩ C) C Finset.inter_subset_right r₁.1 =
        c₁.1 := by
    exact congrArg
      (fun t : K.AttachedCosetVertex C => t.1) hr₁c
  have hrC₂ :
      K.componentIndexMap (B ∩ C) C Finset.inter_subset_right r₂.1 =
        c₂.1 := by
    exact congrArg
      (fun t : K.AttachedCosetVertex C => t.1) hr₂c
  have hBidx :
      K.componentIndexMap (B ∩ C) B Finset.inter_subset_left r₁.1 =
        K.componentIndexMap (B ∩ C) B Finset.inter_subset_left r₂.1 := by
    calc
      _ = b₁.1 := hrB₁
      _ = pB.1 := hb₁
      _ = b₂.1 := hb₂.symm
      _ = _ := hrB₂.symm
  have hCidx :
      K.componentIndexMap (B ∩ C) C Finset.inter_subset_right r₁.1 =
        K.componentIndexMap (B ∩ C) C Finset.inter_subset_right r₂.1 := by
    calc
      _ = c₁.1 := hrC₁
      _ = pC.1 := hc₁
      _ = c₂.1 := hc₂.symm
      _ = _ := hrC₂.symm
  have hridx :
      r₁.1 = r₂.1 :=
    K.componentIndex_inter_pair_injective
      hadm hgen hret B C hBA hCA r₁.1 r₂.1 hBidx hCidx
  obtain ⟨w, hw, hpath⟩ :=
    K.singleCosetEGraph_connected_on_index
      (B ∩ C) r₁ r₂ hridx
  have hMapped : G.Follows
      (K.multiCosetInclude P hadm hgen hret (B ∩ C) hDP r₁)
      w
      (K.multiCosetInclude P hadm hgen hret (B ∩ C) hDP r₂) :=
    hpath.map
      (K.singleCosetToMultiHom P hadm hgen hret (B ∩ C) hDP)
  rw [hr₁, hr₂] at hMapped
  exact ⟨w, hw, hMapped⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
