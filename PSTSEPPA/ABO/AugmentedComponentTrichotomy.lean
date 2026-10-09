import PSTSEPPA.ABO.AugmentedMeetingComponentPaths
import PSTSEPPA.ABO.AugmentedDisjointComponentExact

/-!
# A source-facing intrinsic C-component trichotomy for augmented clusters

Fix any ambient C-coset uG[C]. Its intersection with an augmented
cluster behaves as follows, as a statement about *actual realised
C-labelled paths*:

* If the new B-coset meets the original cluster's C-slice, the
  entire augmented C-slice is one connected piece.
* If the B-coset misses the ambient C-coset, no C-vertices are
  added and the (possibly empty) old cluster C-slice is connected.
* Otherwise the C-slice is the disjoint union of the old C-slice
  and the new (B∩C)-coset, and the C-path components are exactly
  those two pieces.

We package the two connected possibilities together and expose
the disjoint alternative with a literal common coset point.
This is the missing path-component interpretation behind the
already proved exact graph-data alternatives of ABO Corollary 3.15.

No arbitrary ambient Cayley projection is assumed injective.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- An augmented C-slice is either intrinsically C-connected,
or its actual C-path reachability is exactly membership in the
same old/new disjoint piece, with the new piece given by one
literal (B∩C)-coset. -/
theorem augmented_C_component_connected_or_disjoint
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (C : Finset ι) (u : Γ) :
    (∀ (x y : (P.augmentedCayleySubgraph gen B hBA v).Vertex),
      x.1 ∈ generatedLeftCoset gen C u →
      y.1 ∈ generatedLeftCoset gen C u →
      (P.augmentedCayleySubgraph gen B hBA v).SubalphabetReachable
        C x y) ∨
    ∃ z : Γ,
      z ∈ generatedLeftCoset gen B v ∩
        generatedLeftCoset gen C u ∧
      (P.ComponentSlice gen C u ∩
        generatedLeftCoset gen B v = ∅) ∧
      ∀ (x y : (P.augmentedCayleySubgraph gen B hBA v).Vertex),
        x.1 ∈ generatedLeftCoset gen C u →
        y.1 ∈ generatedLeftCoset gen C u →
        ((P.augmentedCayleySubgraph gen B hBA v).SubalphabetReachable
          C x y ↔
            ((x.1 ∈ P.ComponentSlice gen C u ∧
              y.1 ∈ P.ComponentSlice gen C u) ∨
            (x.1 ∈ generatedLeftCoset gen (B ∩ C) z ∧
              y.1 ∈ generatedLeftCoset gen (B ∩ C) z))) := by
  let K := P.augmentedCayleySubgraph gen B hBA v
  by_cases hOldMeet :
      (P.ComponentSlice gen C u ∩
        generatedLeftCoset gen B v).Nonempty
  · left
    intro x y hx hy
    exact P.augmented_meeting_component_connected
      gen hgen hret B hBA v C u hOldMeet x y hx hy
  · by_cases hAmbientMeet :
        (generatedLeftCoset gen B v ∩
          generatedLeftCoset gen C u).Nonempty
    · right
      obtain ⟨z, hzB, hzC⟩ := hAmbientMeet
      have hdisj :
          P.ComponentSlice gen C u ∩
            generatedLeftCoset gen B v = ∅ := by
        apply Set.Subset.antisymm
        · intro t ht
          exact (hOldMeet ⟨t, ht⟩).elim
        · exact Set.empty_subset _
      refine ⟨z, ⟨hzB, hzC⟩, hdisj, ?_⟩
      intro x y hx hy
      exact P.augmented_disjoint_C_reachable_iff_same_piece
        gen hgen hret B hBA v C u z hzB hzC
        hdisj x y hx hy
    · left
      intro x y hx hy
      have hxOld : x.1 ∈ P.VertexSet gen := by
        rcases x.2 with h | h
        · exact h
        · exact (hAmbientMeet ⟨x.1, h, hx⟩).elim
      have hyOld : y.1 ∈ P.VertexSet gen := by
        rcases y.2 with h | h
        · exact h
        · exact (hAmbientMeet ⟨y.1, h, hy⟩).elim
      let xOld : (P.toCayleySubgraph gen).Vertex :=
        ⟨x.1, hxOld⟩
      let yOld : (P.toCayleySubgraph gen).Vertex :=
        ⟨y.1, hyOld⟩
      have hOld :=
        P.componentSlice_actual_reachable gen hgen hret
          C u xOld yOld hx hy
      have hAug :=
        P.cluster_reachable_in_augmented gen B hBA v
          C xOld yOld hOld
      have hxEq :
          (P.clusterSkeletonToAugmentedHom gen B hBA v).onVertex xOld =
            x := by
        apply Subtype.ext
        rfl
      have hyEq :
          (P.clusterSkeletonToAugmentedHom gen B hBA v).onVertex yOld =
            y := by
        apply Subtype.ext
        rfl
      rw [hxEq, hyEq] at hAug
      exact hAug

end ClusterSpec
end ABO
end PSTSEPPA
