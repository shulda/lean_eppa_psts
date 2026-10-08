import PSTSEPPA.ABO.AugmentedComponentSlices
import PSTSEPPA.ABO.ClusterComponentGraph

/-!
# Attached-component structure for augmented clusters

This file formalizes the nontrivial meeting case of ABO Corollary 3.15:
when the attached B-coset meets a C-component of the original A-cluster,
the augmented C-slice is either the full C-coset or the translate of a
(B ∩ C)-augmentation of a lower C-cluster.

Both the exact vertex set and the exact directed-edge set are identified.
The no-overlap case, where a C-slice of the augmentation may split into
two connected components, is left for the genuine graph-connectivity layer.
This theorem does not yet claim the full connected-component corollary.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- Left translation converts a lower cluster augmented at t⁻¹w into
the corresponding union of the translated cluster and the coset wG[D]. -/
theorem leftTranslate_augmentedVertexSet
    (gen : ι → Γ) {C : Finset ι} (R : ClusterSpec C)
    (D : Finset ι) (t w : Γ) :
    LeftTranslateSet t
        (R.AugmentedVertexSet gen D (t⁻¹ * w)) =
      LeftTranslateSet t (R.VertexSet gen) ∪
        generatedLeftCoset gen D w := by
  ext x
  change
    (t⁻¹ * x ∈ R.VertexSet gen ∨
      (t⁻¹ * w)⁻¹ * (t⁻¹ * x) ∈ generatedSubgroup gen D) ↔
    (t⁻¹ * x ∈ R.VertexSet gen ∨
      w⁻¹ * x ∈ generatedSubgroup gen D)
  simp [mul_assoc]

/-- The same left-translation identity for directed edge data. -/
theorem leftTranslate_augmentedEdgeSet
    (gen : ι → Γ) {C : Finset ι} (R : ClusterSpec C)
    (D : Finset ι) (t w : Γ) :
    LeftTranslateEdgeSet t
        (R.AugmentedEdgeSet gen D (t⁻¹ * w)) =
      LeftTranslateEdgeSet t (R.EdgeSet gen) ∪
        FullCosetEdgeSet gen D w := by
  ext e
  rcases e with ⟨x, s⟩
  change
    ((t⁻¹ * x, s) ∈ R.EdgeSet gen ∨
      ((t⁻¹ * w)⁻¹ * (t⁻¹ * x) ∈ generatedSubgroup gen D ∧
        signedBase s ∈ D)) ↔
    ((t⁻¹ * x, s) ∈ R.EdgeSet gen ∨
      (w⁻¹ * x ∈ generatedSubgroup gen D ∧
        signedBase s ∈ D))
  simp [mul_assoc]

/-- Graph-data form of the meeting case of ABO Corollary 3.15.

Assume w lies in the original C-slice and in the B-coset attached to
the ambient A-cluster. Then the C-slice in the augmentation is either
the full ambient C-coset, or a translated (B ∩ C)-augmented C-cluster
with its attachment based at the translated image of w.

The statement gives exact sets of vertices and signed directed edges,
and does not merely classify them abstractly up to isomorphism. -/
theorem augmentedComponentGraph_fullCoset_or_lowerAugmented
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (C : Finset ι) (u w : Γ)
    (hwOld : w ∈ P.ComponentSlice gen C u)
    (hwAttach : w ∈ generatedLeftCoset gen B v) :
    (P.AugmentedComponentSlice gen B v C u =
        generatedLeftCoset gen C u ∧
      P.AugmentedComponentEdgeSlice gen B v C u =
        FullCosetEdgeSet gen C u) ∨
    ∃ t : Γ, ∃ R : ClusterSpec C,
      t⁻¹ * w ∈ R.VertexSet gen ∧
      (P.AugmentedComponentSlice gen B v C u =
        LeftTranslateSet t
          (R.AugmentedVertexSet gen (B ∩ C) (t⁻¹ * w))) ∧
      (P.AugmentedComponentEdgeSlice gen B v C u =
        LeftTranslateEdgeSet t
          (R.AugmentedEdgeSet gen (B ∩ C) (t⁻¹ * w))) := by
  have hcoset :=
    generatedLeftCoset_inter gen hgen hret B C v u w
      hwAttach hwOld.2
  have hV :=
    P.augmentedComponentSlice_eq_union
      gen hgen hret B v C u w hwAttach hwOld.2
  have hE :=
    P.augmentedComponentEdgeSlice_eq_union
      gen hgen hret B v C u w hwAttach hwOld.2
  rcases
      P.componentGraph_fullCoset_or_lowerCluster
        gen hgen hret C u with hfull | hlower
  · left
    constructor
    · rw [hV, hfull.1]
      ext x
      constructor
      · intro hx
        rcases hx with hx | hx
        · exact hx
        · have hxBC :
              x ∈ generatedLeftCoset gen B v ∩
                generatedLeftCoset gen C u := by
            rw [hcoset]
            exact hx
          exact hxBC.2
      · exact Or.inl
    · rw [hE, hfull.2]
      ext e
      constructor
      · intro he
        rcases he with he | he
        · exact he
        · have hsBC :
              (cayleyGraph gen).source e ∈
                generatedLeftCoset gen B v ∩
                  generatedLeftCoset gen C u := by
            rw [hcoset]
            exact he.1
          exact ⟨hsBC.2, (Finset.mem_inter.mp he.2).2⟩
      · exact Or.inl
  · rcases hlower with ⟨t, R, hRV, hRE⟩
    right
    have hwR : t⁻¹ * w ∈ R.VertexSet gen := by
      have htranslated :
          w ∈ LeftTranslateSet t (R.VertexSet gen) := by
        rw [← hRV]
        exact hwOld
      exact htranslated
    refine ⟨t, R, hwR, ?_, ?_⟩
    · rw [hV, hRV]
      exact (R.leftTranslate_augmentedVertexSet gen (B ∩ C) t w).symm
    · rw [hE, hRE]
      exact (R.leftTranslate_augmentedEdgeSet gen (B ∩ C) t w).symm

end ClusterSpec

end ABO
end PSTSEPPA
