import PSTSEPPA.ABO.AugmentedComponentSlices

/-!
# Separation of components in an augmented cluster

The remaining geometric case of ABO Corollary 3.15 occurs when the
attached B-coset meets an ambient C-coset, but does not meet the original
C-slice of the cluster.  The vertex slice is then the disjoint union of
the old C-slice and a new (B ∩ C)-coset.

We also verify the essential directed-edge separation: every C-labelled
edge of the augmented slice has both endpoints in the same one of these
two pieces.  The actual path-connectivity assertion is an independent
remaining graph-theoretic gate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- A C-labelled edge inside the original C-slice has both endpoints
inside that slice, not just the correct source and label. -/
theorem componentEdgeSlice_source_target_mem
    (gen : ι → Γ) (P : ClusterSpec A)
    (C : Finset ι) (u : Γ)
    {e : ActionEdge Γ ι}
    (he : e ∈ P.ComponentEdgeSlice gen C u) :
    (cayleyGraph gen).source e ∈ P.ComponentSlice gen C u ∧
      (cayleyGraph gen).target e ∈ P.ComponentSlice gen C u := by
  constructor
  · exact ⟨P.edge_source_mem gen he.1, he.2.1⟩
  · refine ⟨P.edge_target_mem gen he.1, ?_⟩
    exact
      fullCosetEdge_target_mem gen C u ⟨he.2.1, he.2.2⟩

/-- Every edge of an augmented C-slice stays within either the original
C-slice or the newly attached (B ∩ C)-coset. -/
theorem augmentedComponentEdge_slice_piecewise_closed
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C u)
    {e : ActionEdge Γ ι}
    (he : e ∈ P.AugmentedComponentEdgeSlice gen B v C u) :
    ((cayleyGraph gen).source e ∈ P.ComponentSlice gen C u ∧
      (cayleyGraph gen).target e ∈ P.ComponentSlice gen C u) ∨
    ((cayleyGraph gen).source e ∈ generatedLeftCoset gen (B ∩ C) z ∧
      (cayleyGraph gen).target e ∈ generatedLeftCoset gen (B ∩ C) z) := by
  have hslice :=
    P.augmentedComponentEdgeSlice_eq_union
      gen hgen hret B v C u z hzB hzC
  rw [hslice] at he
  rcases he with heOld | heAdded
  · exact Or.inl (P.componentEdgeSlice_source_target_mem gen C u heOld)
  · exact Or.inr
      ⟨heAdded.1, fullCosetEdge_target_mem gen (B ∩ C) z heAdded⟩

/-- If the original C-slice avoids the attached B-coset, it is also
disjoint from the (B ∩ C)-coset inside the chosen ambient C-coset. -/
theorem componentSlice_disjoint_attachedIntersectionCoset
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C u)
    (hdisj :
      P.ComponentSlice gen C u ∩ generatedLeftCoset gen B v = ∅) :
    P.ComponentSlice gen C u ∩
      generatedLeftCoset gen (B ∩ C) z = ∅ := by
  have hcoset :=
    generatedLeftCoset_inter gen hgen hret B C v u z hzB hzC
  ext x
  constructor
  · rintro ⟨hxOld, hxNew⟩
    have hxBoth :
        x ∈ generatedLeftCoset gen B v ∩
          generatedLeftCoset gen C u := by
      rw [hcoset]
      exact hxNew
    have hxEmpty : x ∈ (∅ : Set Γ) := by
      rw [← hdisj]
      exact ⟨hxOld, hxBoth.1⟩
    have hf : False := by simpa using hxEmpty
    exact hf.elim
  · intro hx
    have hf : False := by simpa using hx
    exact hf.elim

/-- Exact disjoint-piece graph-data decomposition in the second case of
ABO Corollary 3.15.  In addition to the vertex and edge identities, we
record the absence of shared vertices and of edges joining the two pieces. -/
theorem augmentedComponentGraph_disjoint_split
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C u)
    (hdisj :
      P.ComponentSlice gen C u ∩ generatedLeftCoset gen B v = ∅) :
    (P.AugmentedComponentSlice gen B v C u =
      P.ComponentSlice gen C u ∪
        generatedLeftCoset gen (B ∩ C) z) ∧
    (P.AugmentedComponentEdgeSlice gen B v C u =
      P.ComponentEdgeSlice gen C u ∪
        FullCosetEdgeSet gen (B ∩ C) z) ∧
    (P.ComponentSlice gen C u ∩
      generatedLeftCoset gen (B ∩ C) z = ∅) ∧
    (∀ e : ActionEdge Γ ι,
      e ∈ P.AugmentedComponentEdgeSlice gen B v C u →
      ((cayleyGraph gen).source e ∈ P.ComponentSlice gen C u ∧
        (cayleyGraph gen).target e ∈ P.ComponentSlice gen C u) ∨
      ((cayleyGraph gen).source e ∈
          generatedLeftCoset gen (B ∩ C) z ∧
        (cayleyGraph gen).target e ∈
          generatedLeftCoset gen (B ∩ C) z)) := by
  refine ⟨
    P.augmentedComponentSlice_eq_union
      gen hgen hret B v C u z hzB hzC,
    P.augmentedComponentEdgeSlice_eq_union
      gen hgen hret B v C u z hzB hzC,
    P.componentSlice_disjoint_attachedIntersectionCoset
      gen hgen hret B v C u z hzB hzC hdisj,
    ?_⟩
  intro e he
  exact
    P.augmentedComponentEdge_slice_piecewise_closed
      gen hgen hret B v C u z hzB hzC he

end ClusterSpec

end ABO
end PSTSEPPA
