import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.AdmissibleComponentIntersections
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Actual subalphabet component intersections at skeleton vertices in a full multi-CE

An arbitrary selected family of coset attachments may include
alphabets incomparable to B or C. If B and C themselves are
selected constituents, their completed copies are full B- and
C-components (the exact selected-component theorem).

Consequently B-path connectivity *between embedded old skeleton
vertices* in the multi-coset extension reflects B-connectivity
in the original admissible skeleton: a B-path cannot escape the
component-tagged full B-coset.

ABO Lemma 3.21 then gives the intrinsic (B∩C)-intersection
identity already at the level of the full multi-coset EGraph,
for pairs of components meeting the skeleton. This is the
both-skeleton-meeting case at the end of the proof of
Proposition 3.23, with no cluster property assumption needed
in this special case.

No global ambient-Cayley projection is treated as injective.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- When a constituent B is selected, genuine B-path reachability
between its embedded old skeleton points in the *full* multi-CE
is equivalent to intrinsic B-path reachability in the skeleton.
This remains true even with incomparable selected constituents. -/
theorem multiCoset_selected_skeleton_B_reachable_iff
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (x y : K.Vertex) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x)
        w
        ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex y)) ↔
      K.SubalphabetReachable B x y := by
  constructor
  · rintro ⟨w, hw, hpath⟩
    have hcomponent :
        ∃ q : K.AttachedCosetVertex B,
          q.1 = (K.attachedOfSkeletonVertex B x).1 ∧
          (K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex y =
            K.multiCosetInclude P hadm hgen hret B hBP q := by
      apply (K.multiCoset_selected_B_component_exact
        P hadm hgen hret B hBP
        (K.attachedOfSkeletonVertex B x)
        ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex y)).mp
      exact ⟨w, hw, hpath⟩
    obtain ⟨q, hindex, hq⟩ := hcomponent
    have hqAtt : K.attachedOfSkeletonVertex B y = q := by
      apply K.multiCosetInclude_injective P hadm hgen hret B hBP
      exact hq
    have hclasses : K.componentClass B x = K.componentClass B y := by
      calc
        K.componentClass B x = (K.attachedOfSkeletonVertex B x).1 := rfl
        _ = q.1 := hindex.symm
        _ = (K.attachedOfSkeletonVertex B y).1 :=
          (congrArg (fun t : K.AttachedCosetVertex B => t.1) hqAtt).symm
        _ = K.componentClass B y := rfl
    exact (K.componentClass_eq_iff B x y).mp hclasses
  · rintro ⟨w, hw, hpath⟩
    exact ⟨w, hw,
      hpath.map (K.skeletonToMultiCosetHom P hadm hgen hret B hBP)⟩

/-- The intersection of any B- and C-components of a full multi-CE
**through old skeleton vertices** is an intrinsic (B∩C)-component
at their embedded endpoints. The source-facing result is an iff
for actual signed-word paths in the full extension, not merely
an equality of ambient group cosets.

The family may contain incomparable other constituent alphabets.
B,C must be proper in A for the skeleton admissibility intersection
theorem; the equal/nested/empty parameter cases are handled. -/
theorem multiCoset_skeleton_BC_reachable_iff
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (hBP : B ∈ P.alphabets)
    (hCP : C ∈ P.alphabets)
    (x y : K.Vertex) :
    ((∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph P hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x)
          w
          ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex y)) ∧
      (∃ w : LabelWord ι, LabelWord.Uses C w ∧
        (K.multiCosetEGraph P hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x)
          w
          ((K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex y))) ↔
      ∃ w : LabelWord ι, LabelWord.Uses (B ∩ C) w ∧
        (K.multiCosetEGraph P hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x)
          w
          ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex y) := by
  have hBA : B ⊂ A := P.proper B hBP
  have hCA : C ⊂ A := P.proper C hCP
  constructor
  · rintro ⟨hB, hC⟩
    have hBskel :=
      (K.multiCoset_selected_skeleton_B_reachable_iff
        P hadm hgen hret B hBP x y).mp hB
    have hCskel :=
      (K.multiCoset_selected_skeleton_B_reachable_iff
        P hadm hgen hret C hCP x y).mp hC
    have hBC :=
      (K.subalphabetReachable_inter_iff
        hadm hgen hret B C hBA hCA x y).mp
        ⟨hBskel, hCskel⟩
    obtain ⟨w, hw, hpath⟩ := hBC
    exact ⟨w, hw,
      hpath.map
        (K.skeletonToMultiCosetHom P hadm hgen hret B hBP)⟩
  · rintro ⟨w, hw, hpath⟩
    constructor
    · exact ⟨w, hw.mono Finset.inter_subset_left, hpath⟩
    · have hMapped :
        (K.multiCosetEGraph P hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x)
          w
          ((K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex y) := by
        rw [K.skeletonToMultiCosetHom_vertex_independent
          P hadm hgen hret B C hBP hCP x,
          K.skeletonToMultiCosetHom_vertex_independent
            P hadm hgen hret B C hBP hCP y] at hpath
        exact hpath
      exact ⟨w, hw.mono Finset.inter_subset_right, hMapped⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
