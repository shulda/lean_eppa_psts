import PSTSEPPA.ABO.CoatomConstituentCover
import PSTSEPPA.ABO.MultiCosetMinimalSupportPaths
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# A common genuine skeleton anchor for two overlapping tagged constituents

The next geometric issue in the proof of ABO Lemma 4.3 is not merely
that two ambient cosets intersect. The two presentations of a glued
multi-coset vertex must have a common *intrinsic skeleton anchor*,
whose actual C- and D-component indices are those of BOTH tagged
constituents. This holds without a whole-component cluster property.

For a vertex z presented in selected C- and D-copies, obtain its
least component-tagged support M. Minimality gives M⊆C∩D,
and the support-accessibility theorem supplies a realised M-path
from one skeleton vertex x to z. Since M⊆C,D, the same path can
be interpreted inside either completed tagged constituent.
Inclusion-injectivity then shows that the intrinsic C and D
tags of x coincide with those of the original presentations.

If C,D are distinct coatoms in A, the least alphabet M is
strictly smaller than each. This yields a common rank-decreasing
skeleton anchor at every two-coatom overlap, without appealing to
global ambient Cayley injectivity or bridge-freeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Two selected tagged-coset presentations of the SAME quotient vertex
have one common skeleton anchor and one realised word using only their
shared, least support M⊆C∩D. The skeleton anchor belongs to the
precise original C and D component tags. -/
theorem allProperCoset_two_supports_common_tagged_skeleton_anchor
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C D : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hDP : D ∈ (allProperCosetFamily A).alphabets)
    (pC : K.AttachedCosetVertex C)
    (pD : K.AttachedCosetVertex D)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hCz :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP pC = z)
    (hDz :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret D hDP pD = z) :
    ∃ (M : Finset ι)
      (hMP : M ∈ (allProperCosetFamily A).alphabets)
      (x : K.Vertex) (w : LabelWord ι),
      M ⊆ C ∩ D ∧
      LabelWord.Uses M w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            C hCP).onVertex x) w z ∧
      K.componentClass C x = pC.1 ∧
      K.componentClass D x = pD.1 := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨M, hMP, pM, x, w, hMz, hwM, hpathM, hmin⟩ :=
    K.allProperCosetVertex_minimal_support_accessible
      hadm hgen hret z
  obtain ⟨hMC, _⟩ := hmin C hCP pC hCz
  obtain ⟨hMD, _⟩ := hmin D hDP pD hDz
  have hMCD : M ⊆ C ∩ D := by
    intro t ht
    exact Finset.mem_inter.mpr ⟨hMC ht, hMD ht⟩
  have hSkelC :
      (K.skeletonToMultiCosetHom P hadm hgen hret
        M hMP).onVertex x =
      (K.skeletonToMultiCosetHom P hadm hgen hret
        C hCP).onVertex x :=
    K.skeletonToMultiCosetHom_vertex_independent
      P hadm hgen hret M C hMP hCP x
  have hPathC :
      G.Follows
        ((K.skeletonToMultiCosetHom P
          hadm hgen hret C hCP).onVertex x) w z := by
    rw [← hSkelC]
    exact hpathM
  have hCtag : K.componentClass C x = pC.1 := by
    have hPathC' :
        G.Follows
          (K.multiCosetInclude P hadm hgen hret
            C hCP (K.attachedOfSkeletonVertex C x)) w z :=
      hPathC
    obtain ⟨qC, hidx, hqz⟩ :=
      K.multiCoset_selected_B_path_stays_in_coset
        P hadm hgen hret C hCP w (hwM.mono hMC)
        (K.attachedOfSkeletonVertex C x) z hPathC'
    have hqp : qC = pC :=
      K.multiCosetInclude_injective P hadm hgen hret C hCP
        (hqz.symm.trans hCz.symm)
    calc
      K.componentClass C x = qC.1 := hidx.symm
      _ = pC.1 := congrArg Sigma.fst hqp
  have hSkelD :
      (K.skeletonToMultiCosetHom P hadm hgen hret
        M hMP).onVertex x =
      (K.skeletonToMultiCosetHom P hadm hgen hret
        D hDP).onVertex x :=
    K.skeletonToMultiCosetHom_vertex_independent
      P hadm hgen hret M D hMP hDP x
  have hPathD :
      G.Follows
        ((K.skeletonToMultiCosetHom P
          hadm hgen hret D hDP).onVertex x) w z := by
    rw [← hSkelD]
    exact hpathM
  have hDtag : K.componentClass D x = pD.1 := by
    have hPathD' :
        G.Follows
          (K.multiCosetInclude P hadm hgen hret
            D hDP (K.attachedOfSkeletonVertex D x)) w z :=
      hPathD
    obtain ⟨qD, hidx, hqz⟩ :=
      K.multiCoset_selected_B_path_stays_in_coset
        P hadm hgen hret D hDP w (hwM.mono hMD)
        (K.attachedOfSkeletonVertex D x) z hPathD'
    have hqp : qD = pD :=
      K.multiCosetInclude_injective P hadm hgen hret D hDP
        (hqz.symm.trans hDz.symm)
    calc
      K.componentClass D x = qD.1 := hidx.symm
      _ = pD.1 := congrArg Sigma.fst hqp
  exact ⟨M, hMP, x, w, hMCD, hwM, hPathC, hCtag, hDtag⟩

/-- For DISTINCT selected coatoms C,D, every point of their tagged
intersection is anchored to the skeleton by a word on a common
support M which is strict below both coatoms. The SAME skeleton
anchor simultaneously has both prescribed intrinsic component tags. -/
theorem allProperCoset_distinct_coatoms_common_lower_anchor
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C D : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hDP : D ∈ (allProperCosetFamily A).alphabets)
    (hCcard : C.card + 1 = A.card)
    (hDcard : D.card + 1 = A.card)
    (hCD : C ≠ D)
    (pC : K.AttachedCosetVertex C)
    (pD : K.AttachedCosetVertex D)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hCz :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP pC = z)
    (hDz :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret D hDP pD = z) :
    ∃ (M : Finset ι)
      (hMP : M ∈ (allProperCosetFamily A).alphabets)
      (x : K.Vertex) (w : LabelWord ι),
      M ⊂ C ∧ M ⊂ D ∧
      LabelWord.Uses M w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            C hCP).onVertex x) w z ∧
      K.componentClass C x = pC.1 ∧
      K.componentClass D x = pD.1 := by
  obtain ⟨M, hMP, x, w, hMCD, hwM, hpath, htagC, htagD⟩ :=
    K.allProperCoset_two_supports_common_tagged_skeleton_anchor
      hadm hgen hret C D hCP hDP pC pD z hCz hDz
  have hMC : M ⊆ C := hMCD.trans Finset.inter_subset_left
  have hMD : M ⊆ D := hMCD.trans Finset.inter_subset_right
  have hStrictC : M ⊂ C := by
    refine ⟨hMC, ?_⟩
    intro hCM
    have hCDsub : C ⊆ D := hCM.trans hMD
    have hDCeq : D = C :=
      allProperCoset_coatom_maximal A C hCcard D hDP hCDsub
    exact hCD hDCeq.symm
  have hStrictD : M ⊂ D := by
    refine ⟨hMD, ?_⟩
    intro hDM
    have hDCsub : D ⊆ C := hDM.trans hMC
    have hCDeq : C = D :=
      allProperCoset_coatom_maximal A D hDcard C hCP hDCsub
    exact hCD hCDeq
  exact ⟨M, hMP, x, w, hStrictC, hStrictD,
    hwM, hpath, htagC, htagD⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
