import PSTSEPPA.ABO.RankTwoClusterPropertyBase
import PSTSEPPA.ABO.MultiCosetSupportSkeletonMeet

/-!
# Source-exact off-skeleton rank-two cluster-property base

Definition 3.22 of Auinger--Bitterlich--Otto concerns
B-components DISJOINT FROM THE ORIGINAL SKELETON.
Our previous rank-two component theorems instead split
according to whether a vertex belongs to the image of
a selected fully attached B-coset.

These conditions are equivalent, and it is important to
prove the equivalence by actual signed B-paths rather than
by equality of ambient group coordinates. The checked
minimal tagged-support/skeleton-meeting theorem supplies
the missing implication for all ranks.

At rank at most two, any B-component missing the original
skeleton is therefore literally a SINGLETON. Its unique
minimal tagged support is attained at that singleton,
which is exactly the non-full case of the cluster-property
base in Definition 3.22 / source Proposition 4.4.

These theorems do not assert the higher-rank cluster
property or the type-(2) augmentation itself.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- For any rank, a vertex whose true B-component
does not meet the embedded old skeleton cannot lie
in any of the selected complete tagged B-cosets.
The converse is already implicit in the checked
minimal-support/skeleton-path equivalences. -/
theorem allProperCoset_off_skeleton_no_B_presentation
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hOffSkeleton :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            B hBP).onVertex x) w z) :
    ¬ ∃ q : K.AttachedCosetVertex B,
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret B hBP q = z := by
  rintro ⟨q, hq⟩
  obtain ⟨M, hMP, p, hp, hmin⟩ :=
    K.allProperCosetVertex_exists_minimal_tagged_support
      hadm hgen hret z
  have hMB : M ⊆ B :=
    (K.allProperCoset_least_support_subset_iff_B_presentation
      hadm hgen hret z M hMP p hp hmin B hBP).mpr
      ⟨q, hq⟩
  have hPath :=
    (K.allProperCoset_least_support_subset_iff_B_skeleton_reachable
      hadm hgen hret z M hMP p hp hmin B hBP).mp hMB
  exact hOffSkeleton hPath

/-- A genuinely off-skeleton B-component of the rank-two
full proper-alphabet coset extension consists of one
vertex, with no extraneous B-labelled path endpoints. -/
theorem rank_two_off_skeleton_B_component_singleton
    (hcard : A.card ≤ 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard) hgen hret)
    (hOffSkeleton :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard) hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A)
            (K.admissible_of_card_le_two hcard)
            hgen hret B hBP).onVertex x) w z)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard) hgen hret)
    (hzy : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard) hgen hret).Follows
        z w y) :
    y = z := by
  have hOff :=
    K.allProperCoset_off_skeleton_no_B_presentation
      (K.admissible_of_card_le_two hcard)
      hgen hret B hBP z hOffSkeleton
  exact K.rank_two_off_selected_B_component_singleton
    (K.admissible_of_card_le_two hcard)
    hgen hret hcard B hBP z hOff y hzy

/-- The same singleton has its UNIQUE least component-tagged
support at its only vertex: the exact core-support clause
of the rank-two cluster-property base. -/
theorem rank_two_off_skeleton_B_component_core_support
    (hcard : A.card ≤ 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard) hgen hret)
    (hOffSkeleton :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard) hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A)
            (K.admissible_of_card_le_two hcard)
            hgen hret B hBP).onVertex x) w z) :
    ∃ (M : Finset ι)
      (hMP : M ∈ (allProperCosetFamily A).alphabets)
      (p : K.AttachedCosetVertex M),
      K.multiCosetInclude (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard)
        hgen hret M hMP p = z ∧
      ∀ (y : K.MultiCosetVertex (allProperCosetFamily A)
            (K.admissible_of_card_le_two hcard) hgen hret),
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
            K.attachedSubalphabetMap M C hMC p = q := by
  have hOff :=
    K.allProperCoset_off_skeleton_no_B_presentation
      (K.admissible_of_card_le_two hcard)
      hgen hret B hBP z hOffSkeleton
  exact K.rank_two_off_B_component_unique_minimal_support
    (K.admissible_of_card_le_two hcard)
    hgen hret hcard B hBP z hOff

end CayleySubgraphSpec
end ABO
end PSTSEPPA
