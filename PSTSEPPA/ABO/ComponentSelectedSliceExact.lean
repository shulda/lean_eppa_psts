import PSTSEPPA.ABO.SelectedCosetSliceConnectivity

/-!
# Exact intrinsic B-component slices within tagged selected C-cosets

The previous theorem identifies B-reachability between two points of
a fixed tagged completed C-coset with a genuine B∩C-path inside the
same C-copy, even when B is incomparable to C.

Here the root z of the actual B-component may be OUTSIDE that C-copy.
If its B-component meets the C-copy at an included tagged point p,
then its entire vertex slice INSIDE that specific C-component tag is
precisely the complete left (B∩C)-coset relative to p.

Proof: use the witnessed B-path p→z to transport connectivity
between z and a second selected C-point q into connectivity between
p and q. Apply the selected-C slice theorem and invert the original
path for the converse.

This is the source-facing assertion that the intersection of a
B-component with a selected maximal constituent C is an intrinsic
(B∩C)-coset, proved as an *iff of actual signed-word paths* with
the correct C-component index. No ambient Cayley injectivity,
bridge freeness, or higher-rank cluster property is assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The true global B-component of z, assumed to meet the tagged
C-coset at p, has intersection with that C-copy EXACTLY the full
(B∩C)-coset through p. Both directions use realised signed paths
and retain the literal attached component tag. -/
theorem multiCoset_B_component_selected_C_slice_exact
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (hCP : C ∈ P.alphabets)
    (p : K.AttachedCosetVertex C)
    (z : K.MultiCosetVertex P hadm hgen hret)
    (hMeet :
      ∃ u : LabelWord ι, LabelWord.Uses B u ∧
        (K.multiCosetEGraph P hadm hgen hret).Follows
          (K.multiCosetInclude P hadm hgen hret C hCP p)
          u z)
    (q : K.AttachedCosetVertex C)
    (hIndex : p.1 = q.1) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        z w
        (K.multiCosetInclude P hadm hgen hret C hCP q)) ↔
    q.2.1 ∈ generatedLeftCoset gen (B ∩ C) p.2.1 := by
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨u, hu, hpZ⟩ := hMeet
  have hFromP :=
    K.multiCoset_selected_C_slice_B_reachable_iff_inter_coset
      P hadm hgen hret B C hCP p q hIndex
  constructor
  · rintro ⟨w, hw, hZq⟩
    apply hFromP.mp
    exact ⟨u ++ w,
      (LabelWord.uses_append B u w).2 ⟨hu, hw⟩,
      G.follows_append hpZ hZq⟩
  · intro hC
    obtain ⟨w, hw, hpQ⟩ := hFromP.mpr hC
    exact ⟨PSTS.SignedWord.inv u ++ w,
      (LabelWord.uses_append B (PSTS.SignedWord.inv u) w).2
        ⟨hu.inv, hw⟩,
      G.follows_append (G.follows_inverse hpZ) hpQ⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
