import PSTSEPPA.ABO.SourceSignedWholeClusterProperty
import PSTSEPPA.ABO.RankTwoOffSkeletonClusterProperty

/-!
# ABO Proposition 4.4: exact signed Definition 3.22 rank-two base

Source Proposition 4.4 does not merely say that every off-skeleton
B-component is a singleton, nor that every singleton has a least
support. It says the FULL proper coset extension of an arbitrary
connected two-letter old skeleton has the WHOLE cluster property.

The independently certified rank-two signed geometry proves that
every true off-skeleton B-component is a SINGLETON, and its only
vertex has an attained, uniquely least ORIGINAL component-tagged
support. We now integrate this into the EXACT source predicate
HasExactSignedWholeComponentClusterProperty from Definition 3.22:

* minimum support of the ENTIRE B-component, including correct
  old component index and attainment at its sole vertex;
* full signed B-coset or genuine PROPER translated B-cluster
  EGraph shape (positive/inverse signed edges, true old/fresh tags);
* one real support-attaining core point in all active tagged
  coatom slices.

We do not assume the higher-rank cluster property or bridge
freeness, add missing old edges, or identify equal Γ coordinates
with equal original component-tagged points. This is precisely
the base required for the cardinality induction of Theorem 4.5.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Formal source Proposition 4.4 in the exact signed whole-component
cluster API, at parent alphabet cardinality TWO.

Admissibility is NOT assumed: it comes from the separately proved
two-letter admissibility lemma. A finite generated retractable
labelled group and an arbitrary actual incomplete two-letter
Cayley skeleton suffice. No higher bridge-free assumption. -/
theorem rankTwo_hasExactSignedWholeComponentClusterProperty
    [Finite Γ]
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    K.HasExactSignedWholeComponentClusterProperty
      (K.admissible_of_card_le_two hcard.le) hgen hret := by
  classical
  let hadm := K.admissible_of_card_le_two hcard.le
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  intro B hBP anchor hOff
  obtain ⟨M, hMP, p, hp, hMinVertex⟩ :=
    K.rank_two_off_skeleton_B_component_core_support
      hcard.le hgen hret B hBP anchor hOff
  let S : Set (K.MultiCosetVertex P hadm hgen hret) :=
    {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
       G.Follows anchor w y}
  have hAnchorS : anchor ∈ S :=
    ⟨[], LabelWord.uses_nil B, EGraph.Follows.nil anchor⟩
  have hMin :
      K.IsMinimalTaggedSupportFor P hadm hgen hret S M p.1 := by
    constructor
    · exact ⟨anchor, hAnchorS, hMP, p, rfl, hp⟩
    · intro C hCP q y hy hCy
      obtain ⟨hMC, hAttach⟩ :=
        hMinVertex y hy C hCP q hCy
      exact ⟨hMC, congrArg (K.attachedIndex C) hAttach⟩
  have hShape :
      K.HasFullSignedBCosetAlternative hadm hgen hret B anchor ∨
      K.HasProperSignedBClusterAlternative hadm hgen hret B anchor :=
    K.allProperCoset_signed_full_or_proper_cluster_of_minimum
      hadm hgen hret (by omega) B anchor
      (fun _hNoFull => ⟨M, p.1, hMin⟩)
  obtain ⟨core, hReach, hTagged, hCommon⟩ :=
    K.allProperCoset_minimum_attainer_in_all_active_coatoms
      hadm hgen hret B M anchor p.1 hMin
  exact ⟨M, p.1, hMin, hShape, core, hReach, hTagged, hCommon⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
