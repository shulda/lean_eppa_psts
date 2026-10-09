import PSTSEPPA.ABO.ClusterCayleySkeleton
import PSTSEPPA.ABO.AugmentedComponentSeparation
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Real C-path separation in augmented clusters

The disjoint case of ABO Corollary 3.15 has two vertex pieces:
the original C-slice of the cluster and the newly attached
(B∩C)-coset. Earlier work proved that every C-labelled edge
stays inside one piece and that the pieces are disjoint.

Here we upgrade this edge separation to an intrinsic path
invariant: a realised C-word path beginning in the old C-slice
cannot leave it. Consequently no C-path connects an old-slice
vertex to a new attached intersection-coset vertex.

This is a literal graph-path theorem, not an inference from
the ambient C-coset equality. Formal inverse edge tokens and
arbitrary word lengths are covered by induction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- Under disjointness from the attached B-coset, every actual
C-labelled path starting in the old C-slice remains in that
original slice, regardless of the path length. -/
theorem augmented_old_C_slice_path_invariant
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C u)
    (hdisj :
      P.ComponentSlice gen C u ∩
        generatedLeftCoset gen B v = ∅)
    {x y : (P.augmentedCayleySubgraph gen B hBA v).Vertex}
    {w : LabelWord ι}
    (hpath :
      (P.augmentedCayleySubgraph gen B hBA v).toEGraph.Follows
        x w y)
    (hw : LabelWord.Uses C w)
    (hxOld : x.1 ∈ P.ComponentSlice gen C u) :
    y.1 ∈ P.ComponentSlice gen C u := by
  let K := P.augmentedCayleySubgraph gen B hBA v
  have hdisjSmall :=
    P.componentSlice_disjoint_attachedIntersectionCoset
      gen hgen hret B v C u z hzB hzC hdisj
  revert hw hxOld
  induction hpath with
  | nil x =>
      intro _ hxOld
      exact hxOld
  | @cons x mid s w e hs hl hrest ih =>
      intro hw hxOld
      have hsourceOld :
          (cayleyGraph gen).source e.1 ∈
            P.ComponentSlice gen C u := by
        have hsValue := congrArg
          (fun t : K.Vertex => t.1) hs
        change (cayleyGraph gen).source e.1 = x.1 at hsValue
        rw [hsValue]
        exact hxOld
      have hlabelC :
          signedBase ((cayleyGraph gen).label e.1) ∈ C := by
        change signedBase ((K.toEGraph).label e) ∈ C
        rw [hl]
        exact hw.1
      have hslice :
          e.1 ∈ P.AugmentedComponentEdgeSlice
            gen B v C u :=
        ⟨e.2, hsourceOld.2, hlabelC⟩
      rcases P.augmentedComponentEdge_slice_piecewise_closed
        gen hgen hret B v C u z hzB hzC hslice with
          hOld | hNew
      · exact ih hw.2 hOld.2
      · have hmeet :
            (cayleyGraph gen).source e.1 ∈
              P.ComponentSlice gen C u ∩
                generatedLeftCoset gen (B ∩ C) z :=
          ⟨hsourceOld, hNew.1⟩
        have hempty :
            (cayleyGraph gen).source e.1 ∈ (∅ : Set Γ) := by
          rw [← hdisjSmall]
          exact hmeet
        have hf : False := by simpa using hempty
        exact hf.elim

/-- No actual C-path crosses from the original C-slice into the
disjoint newly attached (B∩C)-coset. -/
theorem augmented_disjoint_old_new_not_C_reachable
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C u)
    (hdisj :
      P.ComponentSlice gen C u ∩
        generatedLeftCoset gen B v = ∅)
    (x y : (P.augmentedCayleySubgraph gen B hBA v).Vertex)
    (hxOld : x.1 ∈ P.ComponentSlice gen C u)
    (hyAdded :
      y.1 ∈ generatedLeftCoset gen (B ∩ C) z) :
    ¬ (P.augmentedCayleySubgraph gen B hBA v).SubalphabetReachable
        C x y := by
  rintro ⟨w, hw, hpath⟩
  have hyOld :=
    P.augmented_old_C_slice_path_invariant gen hgen hret
      B hBA v C u z hzB hzC hdisj hpath hw hxOld
  have hdisjSmall :=
    P.componentSlice_disjoint_attachedIntersectionCoset
      gen hgen hret B v C u z hzB hzC hdisj
  have hempty : y.1 ∈ (∅ : Set Γ) := by
    rw [← hdisjSmall]
    exact ⟨hyOld, hyAdded⟩
  have hf : False := by simpa using hempty
  exact hf

end ClusterSpec
end ABO
end PSTSEPPA
