import PSTSEPPA.ABO.AdmissibleComponentOverlap
import PSTSEPPA.ABO.ComponentIndexMonotonicity

/-!
# Connected intersections of intrinsic skeleton components

This is the path-theoretic core of ABO Lemma 3.21.

If B and C are proper subalphabets of A and the skeleton K is
admissible, two vertices are both B-connected and C-connected exactly
when they are (B ∩ C)-connected. The group-theoretic intersection
G[B] ∩ G[C] = G[B ∩ C] first shows that the corresponding lower
ambient cosets meet; admissibility reflects that ambient intersection
to an actual (B ∩ C)-path in K.

The nested/equal-alphabet case is handled separately, since the strict
subalphabet hypothesis in admissibility must never be invoked with
B ∩ C = B. This is also a direct regression check for repair R5.

We then identify the *actual* intersection of a B-component and a
C-component, when nonempty, with one (B ∩ C)-component, rather than
with just an ambient coset intersection.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- ABO Lemma 3.21 in path form: simultaneous intrinsic B- and
C-reachability is precisely intrinsic (B ∩ C)-reachability, for
proper B,C ⊂ A. -/
theorem subalphabetReachable_inter_iff
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (hBA : B ⊂ A) (_hCA : C ⊂ A)
    (x y : K.Vertex) :
    (K.SubalphabetReachable B x y ∧
      K.SubalphabetReachable C x y) ↔
      K.SubalphabetReachable (B ∩ C) x y := by
  constructor
  · rintro ⟨hxyB, hxyC⟩
    by_cases hBC : B ⊆ C
    · rw [Finset.inter_eq_left.mpr hBC]
      exact hxyB
    · have hDproper : B ∩ C ⊂ B := by
        refine ⟨Finset.inter_subset_left, ?_⟩
        intro hBD
        apply hBC
        intro i hi
        exact (Finset.mem_inter.mp (hBD hi)).2
      have hxyBCoset :=
        K.subalphabetReachable_implies_coset B x y hxyB
      have hxyCCoset :=
        K.subalphabetReachable_implies_coset C x y hxyC
      change x.1⁻¹ * y.1 ∈ generatedSubgroup gen B at hxyBCoset
      change x.1⁻¹ * y.1 ∈ generatedSubgroup gen C at hxyCCoset
      have hxyD :
          x.1⁻¹ * y.1 ∈ generatedSubgroup gen (B ∩ C) := by
        have hm :
            x.1⁻¹ * y.1 ∈
              generatedSubgroup gen B ⊓ generatedSubgroup gen C :=
          ⟨hxyBCoset, hxyCCoset⟩
        rwa [generatedSubgroup_inf gen hgen hret B C] at hm
      have hcosets :
          (generatedLeftCoset gen (B ∩ C) x.1 ∩
            generatedLeftCoset gen (B ∩ C) y.1).Nonempty :=
        ⟨y.1, hxyD,
          self_mem_generatedLeftCoset gen (B ∩ C) y.1⟩
      obtain ⟨z, hxz, hyz⟩ :=
        hadm B (B ∩ C) (B ∩ C)
          hBA hDproper hDproper x y hxyB hcosets
      exact K.subalphabetReachable_trans (B ∩ C)
        hxz (K.subalphabetReachable_symm (B ∩ C) hyz)
  · intro hxy
    exact ⟨K.subalphabetReachable_mono
        (B ∩ C) B Finset.inter_subset_left hxy,
      K.subalphabetReachable_mono
        (B ∩ C) C Finset.inter_subset_right hxy⟩

/-- The intersection of two intrinsic components through the same
basepoint is exactly its (B ∩ C)-component. This is an equality of
sets of actual skeleton vertices, not ambient cosets. -/
theorem subalphabetComponent_inter
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (hBA : B ⊂ A) (hCA : C ⊂ A)
    (z : K.Vertex) :
    K.SubalphabetComponent B z ∩ K.SubalphabetComponent C z =
      K.SubalphabetComponent (B ∩ C) z := by
  ext x
  exact K.subalphabetReachable_inter_iff
    hadm hgen hret B C hBA hCA z x

/-- Full component-intersection form of ABO Lemma 3.21.
A nonempty intersection of a B-component and a C-component is one
(B ∩ C)-component based at any chosen common vertex. -/
theorem subalphabetComponent_inter_of_common
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (hBA : B ⊂ A) (hCA : C ⊂ A)
    (x y z : K.Vertex)
    (hzB : z ∈ K.SubalphabetComponent B x)
    (hzC : z ∈ K.SubalphabetComponent C y) :
    K.SubalphabetComponent B x ∩ K.SubalphabetComponent C y =
      K.SubalphabetComponent (B ∩ C) z := by
  have hB :
      K.SubalphabetComponent B x = K.SubalphabetComponent B z :=
    K.subalphabetComponent_eq_of_reachable B hzB
  have hC :
      K.SubalphabetComponent C y = K.SubalphabetComponent C z :=
    K.subalphabetComponent_eq_of_reachable C hzC
  rw [hB, hC]
  exact K.subalphabetComponent_inter
    hadm hgen hret B C hBA hCA z

/-- If the component intersection is nonempty, an intersection
component can be chosen without fixing a representative in advance. -/
theorem subalphabetComponent_inter_of_nonempty
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (hBA : B ⊂ A) (hCA : C ⊂ A)
    (x y : K.Vertex)
    (hne :
      (K.SubalphabetComponent B x ∩
        K.SubalphabetComponent C y).Nonempty) :
    ∃ z : K.Vertex,
      z ∈ K.SubalphabetComponent B x ∩
        K.SubalphabetComponent C y ∧
      K.SubalphabetComponent B x ∩ K.SubalphabetComponent C y =
        K.SubalphabetComponent (B ∩ C) z := by
  obtain ⟨z, hzB, hzC⟩ := hne
  exact ⟨z, ⟨hzB, hzC⟩,
    K.subalphabetComponent_inter_of_common
      hadm hgen hret B C hBA hCA x y z hzB hzC⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
