import PSTSEPPA.ABO.AugmentedCluster
import PSTSEPPA.ABO.ClusterComponentIntersections

/-!
# Subalphabet slices of augmented clusters

Preparatory, exact vertex/edge identities for ABO Corollary 3.15.
When the attached B-coset meets the chosen ambient C-coset, their
intersection is exactly one (B ∩ C)-coset. Hence the C-labelled slice of
the augmented cluster equals the original C-slice plus that lower coset.

When the ambient C-coset does not meet the attached B-coset, nothing is
added to its slice.  These are identities of actual vertex and directed edge
sets, not merely bijections or informal statements about connectivity.

The remaining step for the full corollary is to identify the connected
C-components when the two contributions to a slice are disjoint.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- Exact decomposition of the vertex slice of an augmented cluster when
the attached B-coset meets the ambient C-coset at z. -/
theorem augmentedComponentSlice_eq_union
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C u) :
    P.AugmentedComponentSlice gen B v C u =
      P.ComponentSlice gen C u ∪
        generatedLeftCoset gen (B ∩ C) z := by
  have hcoset :=
    generatedLeftCoset_inter gen hgen hret B C v u z hzB hzC
  ext x
  constructor
  · rintro ⟨hxAug, hxC⟩
    rcases hxAug with hxCluster | hxAttach
    · exact Or.inl ⟨hxCluster, hxC⟩
    · apply Or.inr
      rw [← hcoset]
      exact ⟨hxAttach, hxC⟩
  · intro hx
    rcases hx with hxCluster | hxAttach
    · exact ⟨Or.inl hxCluster.1, hxCluster.2⟩
    · have hxBC :
          x ∈ generatedLeftCoset gen B v ∩
            generatedLeftCoset gen C u := by
        rw [hcoset]
        exact hxAttach
      exact ⟨Or.inr hxBC.1, hxBC.2⟩

/-- Directed-edge version: both the source-position test and the label
restriction are intersected, so the added edges are exactly the
(B ∩ C)-labelled edges of one (B ∩ C)-coset. -/
theorem augmentedComponentEdgeSlice_eq_union
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C u) :
    P.AugmentedComponentEdgeSlice gen B v C u =
      P.ComponentEdgeSlice gen C u ∪
        FullCosetEdgeSet gen (B ∩ C) z := by
  have hcoset :=
    generatedLeftCoset_inter gen hgen hret B C v u z hzB hzC
  ext e
  constructor
  · rintro ⟨heAug, hsC, hlC⟩
    rcases heAug with heCluster | heAttach
    · exact Or.inl ⟨heCluster, hsC, hlC⟩
    · apply Or.inr
      refine ⟨?_, Finset.mem_inter.mpr ⟨heAttach.2, hlC⟩⟩
      rw [← hcoset]
      exact ⟨heAttach.1, hsC⟩
  · intro he
    rcases he with heCluster | heAttach
    · exact ⟨Or.inl heCluster.1, heCluster.2.1, heCluster.2.2⟩
    · have hsBC :
          (cayleyGraph gen).source e ∈
            generatedLeftCoset gen B v ∩
              generatedLeftCoset gen C u := by
        rw [hcoset]
        exact heAttach.1
      have hlBC := Finset.mem_inter.mp heAttach.2
      exact ⟨Or.inr ⟨hsBC.1, hlBC.1⟩, hsBC.2, hlBC.2⟩

/-- Joint vertex/edge form, existentially choosing the common point.
This avoids a noncanonical choice of basepoint in downstream applications. -/
theorem augmentedComponentSlices_of_cosets_meet
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ)
    (C : Finset ι) (u : Γ)
    (hne :
      (generatedLeftCoset gen B v ∩
        generatedLeftCoset gen C u).Nonempty) :
    ∃ z : Γ,
      z ∈ generatedLeftCoset gen B v ∩
        generatedLeftCoset gen C u ∧
      (P.AugmentedComponentSlice gen B v C u =
        P.ComponentSlice gen C u ∪
          generatedLeftCoset gen (B ∩ C) z) ∧
      (P.AugmentedComponentEdgeSlice gen B v C u =
        P.ComponentEdgeSlice gen C u ∪
          FullCosetEdgeSet gen (B ∩ C) z) := by
  rcases hne with ⟨z, hzB, hzC⟩
  exact ⟨z, ⟨hzB, hzC⟩,
    P.augmentedComponentSlice_eq_union
      gen hgen hret B v C u z hzB hzC,
    P.augmentedComponentEdgeSlice_eq_union
      gen hgen hret B v C u z hzB hzC⟩

/-- A C-coset disjoint from the attached B-coset has exactly its
original cluster vertex slice. -/
theorem augmentedComponentSlice_eq_original_of_disjoint
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) (C : Finset ι) (u : Γ)
    (hdisj :
      generatedLeftCoset gen B v ∩ generatedLeftCoset gen C u = ∅) :
    P.AugmentedComponentSlice gen B v C u =
      P.ComponentSlice gen C u := by
  ext x
  constructor
  · rintro ⟨hxAug, hxC⟩
    rcases hxAug with hxCluster | hxAttach
    · exact ⟨hxCluster, hxC⟩
    · have hxEmpty : x ∈ (∅ : Set Γ) := by
        rw [← hdisj]
        exact ⟨hxAttach, hxC⟩
      have hf : False := by simpa using hxEmpty
      exact hf.elim
  · rintro ⟨hxCluster, hxC⟩
    exact ⟨Or.inl hxCluster, hxC⟩

/-- The corresponding disjointness statement for directed edges. -/
theorem augmentedComponentEdgeSlice_eq_original_of_disjoint
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) (C : Finset ι) (u : Γ)
    (hdisj :
      generatedLeftCoset gen B v ∩ generatedLeftCoset gen C u = ∅) :
    P.AugmentedComponentEdgeSlice gen B v C u =
      P.ComponentEdgeSlice gen C u := by
  ext e
  constructor
  · rintro ⟨heAug, hsC, hlC⟩
    rcases heAug with heCluster | heAttach
    · exact ⟨heCluster, hsC, hlC⟩
    · have hxEmpty :
          (cayleyGraph gen).source e ∈ (∅ : Set Γ) := by
        rw [← hdisj]
        exact ⟨heAttach.1, hsC⟩
      have hf : False := by simpa using hxEmpty
      exact hf.elim
  · rintro ⟨heCluster, hsC, hlC⟩
    exact ⟨Or.inl heCluster, hsC, hlC⟩

end ClusterSpec

end ABO
end PSTSEPPA
