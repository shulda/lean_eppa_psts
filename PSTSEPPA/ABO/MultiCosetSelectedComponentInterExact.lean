import PSTSEPPA.ABO.MultiCosetSelectedComponentIntersections

/-!
# Exact B∩C-component equality for selected full-coset components

Once the intersection of two intrinsic B- and C-components
based at selected complete constituent cosets is known to
be (B∩C)-connected, the full set-level component identity
follows by concatenating actual signed-labelled paths.

For a common vertex z, a vertex t lies simultaneously in
the selected B- and C-components iff it is joined to z by
a real (B∩C)-supported path in the full multi-coset EGraph.

This is the literal intrinsic path-component form of the
both-skeleton-meeting/full-coset case of source ABO Proposition
3.23, without assuming the global cluster property. Other
two cases with off-skeleton cluster components remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The intersection of selected complete B- and C-coset
path-components is exactly the intrinsic (B∩C)-component of
any chosen common vertex, even when other selected alphabet
constituents are incomparable to B or C. -/
theorem allProperCoset_selected_BC_component_inter_exact
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (pB : K.AttachedCosetVertex B)
    (pC : K.AttachedCosetVertex C)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hzB : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
        (K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret B hBP pB) w z)
    (hzC : ∃ w : LabelWord ι, LabelWord.Uses C w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
        (K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP pC) w z)
    (t : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    ((∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          (K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret B hBP pB) w t) ∧
      (∃ w : LabelWord ι, LabelWord.Uses C w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          (K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP pC) w t)) ↔
      (∃ w : LabelWord ι, LabelWord.Uses (B ∩ C) w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows z w t) := by
  let G := K.multiCosetEGraph
    (allProperCosetFamily A) hadm hgen hret
  constructor
  · rintro ⟨htB, htC⟩
    exact K.allProperCoset_selected_BC_component_inter_connected
      hadm hgen hret B C hBP hCP
      pB pC z t hzB htB hzC htC
  · rintro ⟨w, hw, hpath⟩
    obtain ⟨u, hu, hzu⟩ := hzB
    obtain ⟨v, hv, hzv⟩ := hzC
    constructor
    · exact ⟨u ++ w,
        (LabelWord.uses_append B u w).2
          ⟨hu, hw.mono Finset.inter_subset_left⟩,
        G.follows_append hzu hpath⟩
    · exact ⟨v ++ w,
        (LabelWord.uses_append C v w).2
          ⟨hv, hw.mono Finset.inter_subset_right⟩,
        G.follows_append hzv hpath⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
