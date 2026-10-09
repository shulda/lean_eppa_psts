import PSTSEPPA.ABO.MultiCosetVertexSupport

/-!
# Unique least component-tagged support of a coset-extension vertex

ABO §3.3.3, preceding Definition 3.22, observes that every
*individual vertex* of the full proper-subalphabet coset extension
has a unique minimal support. This file gives a proof independent of
the cluster property, which concerns supports of whole components.

The key argument is finite intersection, not a choice of shortest
word: the family of supporting alphabets is nonempty, finite and
closed under binary intersection. Its finite intersection is
therefore itself a support and lies inside any other support.

We then recover the exact component-indexed tagged support point:
every other representation of the same quotient vertex at alphabet
C is the image of this least tagged point under alphabet inclusion.

The distinction from the *whole-component* minimal-support clause
of Definition 3.22 is essential. Only the singleton statement is
established here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every nonempty finite family of supporting alphabets has a
supporting common lower bound. This uses exact intersection
refinement of tagged cosets (ABO 3.11), not mere equality of
their ambient Cayley coordinates. -/
theorem allProperCosetVertex_supports_common_lower
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (S : Finset (Finset ι))
    (hsupp : ∀ B ∈ S,
      K.MultiCosetVertexSupported (allProperCosetFamily A)
        hadm hgen hret B z)
    (hne : S.Nonempty) :
    ∃ M : Finset ι,
      K.MultiCosetVertexSupported (allProperCosetFamily A)
        hadm hgen hret M z ∧
      ∀ B ∈ S, M ⊆ B := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      obtain ⟨B, hB⟩ := hne
      simp at hB
  | @insert B S hBS ih =>
      have hB : K.MultiCosetVertexSupported
          (allProperCosetFamily A) hadm hgen hret B z :=
        hsupp B (Finset.mem_insert_self B S)
      by_cases hSne : S.Nonempty
      · have hsuppS : ∀ C ∈ S,
            K.MultiCosetVertexSupported (allProperCosetFamily A)
              hadm hgen hret C z := by
          intro C hC
          exact hsupp C (Finset.mem_insert_of_mem hC)
        obtain ⟨M, hM, hMlower⟩ := ih hsuppS hSne
        refine ⟨B ∩ M,
          K.allProperCosetVertex_support_inter hadm hgen hret
            z B M hB hM, ?_⟩
        intro C hC
        rcases Finset.mem_insert.mp hC with hCB | hCS
        · subst C
          exact Finset.inter_subset_left
        · exact Finset.inter_subset_right.trans (hMlower C hCS)
      · refine ⟨B, hB, ?_⟩
        intro C hC
        rcases Finset.mem_insert.mp hC with hCB | hCS
        · subst C
          exact subset_rfl
        · exact False.elim (hSne ⟨C, hCS⟩)

/-- Every vertex of the full proper-alphabet multi-coset extension
has a least *supporting alphabet* contained in all its others.
This is the alphabet part of source §3.3.3 singleton minimal
support, and needs no global injectivity of the Cayley morphism. -/
theorem allProperCosetVertex_exists_least_support_alphabet
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    ∃ M : Finset ι,
      K.MultiCosetVertexSupported (allProperCosetFamily A)
        hadm hgen hret M z ∧
      ∀ C : Finset ι,
        K.MultiCosetVertexSupported (allProperCosetFamily A)
          hadm hgen hret C z → M ⊆ C := by
  classical
  let S : Finset (Finset ι) :=
    (allProperCosetFamily A).alphabets.filter
      (fun B => K.MultiCosetVertexSupported
        (allProperCosetFamily A) hadm hgen hret B z)
  have hS : S.Nonempty := by
    obtain ⟨B, hB⟩ :=
      K.multiCosetVertex_exists_support
        (allProperCosetFamily A) hadm hgen hret z
    obtain ⟨hBP, p, hp⟩ := hB
    refine ⟨B, Finset.mem_filter.mpr ?_⟩
    exact ⟨hBP, ⟨hBP, p, hp⟩⟩
  have hSsupport : ∀ B ∈ S,
      K.MultiCosetVertexSupported (allProperCosetFamily A)
        hadm hgen hret B z := by
    intro B hB
    exact (Finset.mem_filter.mp hB).2
  obtain ⟨M, hM, hmin⟩ :=
    K.allProperCosetVertex_supports_common_lower
      hadm hgen hret z S hSsupport hS
  refine ⟨M, hM, ?_⟩
  intro C hC
  obtain ⟨hCP, q, hq⟩ := hC
  exact hmin C (Finset.mem_filter.mpr
    ⟨hCP, ⟨hCP, q, hq⟩⟩)

/-- The smallest supporting alphabet is unique as a finite set,
including the empty-alphabet case. -/
theorem allProperCosetVertex_least_support_alphabet_unique
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (M N : Finset ι)
    (hM : K.MultiCosetVertexSupported (allProperCosetFamily A)
      hadm hgen hret M z)
    (hN : K.MultiCosetVertexSupported (allProperCosetFamily A)
      hadm hgen hret N z)
    (hminM : ∀ C : Finset ι,
       K.MultiCosetVertexSupported (allProperCosetFamily A)
         hadm hgen hret C z → M ⊆ C)
    (hminN : ∀ C : Finset ι,
       K.MultiCosetVertexSupported (allProperCosetFamily A)
         hadm hgen hret C z → N ⊆ C) :
    M = N :=
  Finset.Subset.antisymm (hminM N hN) (hminN M hM)

/-- An inclusion-minimal supporting tagged point determines
each of its larger-alphabet presentations uniquely, including
the intrinsic skeleton-component tag.

It is false without the exact intersection-support quotient:
ambient group-coordinate equality alone would not imply this. -/
theorem allProperCosetVertex_minimal_tag_refines
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (M C : Finset ι)
    (hMP : M ∈ (allProperCosetFamily A).alphabets)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (p : K.AttachedCosetVertex M)
    (q : K.AttachedCosetVertex C)
    (hp : K.multiCosetInclude (allProperCosetFamily A)
      hadm hgen hret M hMP p = z)
    (hq : K.multiCosetInclude (allProperCosetFamily A)
      hadm hgen hret C hCP q = z)
    (hMC : M ⊆ C) :
    K.attachedSubalphabetMap M C hMC p = q := by
  have hD := allProperCosetFamily_inter_mem A M C hMP hCP
  obtain ⟨r, _, hrp, hrq⟩ :=
    K.multiCosetVertex_two_supports_intersection
      (allProperCosetFamily A) hadm hgen hret z
      M C hMP hCP hD p q hp hq
  calc
    K.attachedSubalphabetMap M C hMC p =
        K.attachedSubalphabetMap M C hMC
          (K.attachedSubalphabetMap (M ∩ C) M
            Finset.inter_subset_left r) :=
      congrArg _ hrp.symm
    _ = K.attachedSubalphabetMap (M ∩ C) C
          (Finset.inter_subset_left.trans hMC) r :=
      K.attachedSubalphabetMap_comp (M ∩ C) M C
        Finset.inter_subset_left hMC r
    _ = K.attachedSubalphabetMap (M ∩ C) C
          Finset.inter_subset_right r := rfl
    _ = q := hrq

/-- Full component-tagged singleton minimal support in ABO §3.3.3:
there exists a support (M,p) of z whose alphabet is included
in every supporting alphabet C, and whose tagged coset point
maps to *every* C-supporting presentation q.

This does not assert minimal support for an entire off-skeleton
connected component, which is the separate and stronger
cluster-property hypothesis in Definition 3.22. -/
theorem allProperCosetVertex_exists_minimal_tagged_support
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    ∃ (M : Finset ι)
      (hMP : M ∈ (allProperCosetFamily A).alphabets)
      (p : K.AttachedCosetVertex M),
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret M hMP p = z ∧
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets)
        (q : K.AttachedCosetVertex C),
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP q = z →
        ∃ hMC : M ⊆ C,
          K.attachedSubalphabetMap M C hMC p = q := by
  obtain ⟨M, hM, hleast⟩ :=
    K.allProperCosetVertex_exists_least_support_alphabet
      hadm hgen hret z
  obtain ⟨hMP, p, hp⟩ := hM
  refine ⟨M, hMP, p, hp, ?_⟩
  intro C hCP q hq
  let hMC : M ⊆ C := hleast C ⟨hCP, q, hq⟩
  exact ⟨hMC,
    K.allProperCosetVertex_minimal_tag_refines
      hadm hgen hret z M C hMP hCP p q hp hq hMC⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
