import PSTSEPPA.ABO.Lemma43FiniteCoatomWholeComponentMinimum
import PSTSEPPA.ABO.MultiCosetMinimalSupportPaths

/-!
# ABO Lemma 4.3: one OLD skeleton anchor for an arbitrary common tagged core

The accepted finite-coatom induction produces one actual quotient vertex z
in every selected original component-tagged C-constituent. To apply the
source's cluster identification via Corollary 3.12 we must show there is
ONE vertex x of the ORIGINAL skeleton having all the prescribed intrinsic
C-component indices. It is not enough to use a Cayley-group coordinate.

Choose the exact least tagged support (M,m) of z and its real signed
M-word path from an original skeleton point x to z. For EACH C-copy
containing z, minimum support gives M⊆C, so the SAME original M-word
path stays inside that exact original C-component-tagged complete
constituent. The verified source path-reflection and injectivity yield
componentClass C x equal to its ORIGINAL C-tag. One x works for ALL
constituents, not separately chosen anchors for pairs.

This is the common-original-skeleton-anchor gate of the existing
published Lemma 4.3, not yet the final labelled B-cluster isomorphism.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- For any finite family of genuine original tagged C-constituents
containing the SAME actual multiCE vertex z, one old skeleton x
simultaneously realizes ALL their original C-component indices and
has a REAL signed M-word path to z using a common subalphabet M⊆C. -/
theorem allProperCoset_common_point_one_original_skeleton_anchor
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (I : Finset K.ProperCosetTag)
    (hAll : ∀ t ∈ I,
      z ∈ K.properCosetTagSlice hadm hgen hret B anchor t) :
    ∃ (M : Finset ι)
      (hMP : M ∈ (allProperCosetFamily A).alphabets)
      (x : K.Vertex) (w : LabelWord ι),
      LabelWord.Uses M w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
        ((K.skeletonToMultiCosetHom
          (allProperCosetFamily A) hadm hgen hret
          M hMP).onVertex x) w z ∧
      ∀ t ∈ I,
        M ⊆ K.properCosetTagAlphabet t ∧
        K.componentClass (K.properCosetTagAlphabet t) x =
          K.properCosetTagIndex t := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨M, hMP, pM, x, w, hMz, hwM, hReal, hMin⟩ :=
    K.allProperCosetVertex_minimal_support_accessible
      hadm hgen hret z
  refine ⟨M, hMP, x, w, hwM, hReal, ?_⟩
  intro t ht
  let C := K.properCosetTagAlphabet t
  let hCP : C ∈ P.alphabets :=
    K.properCosetTagAlphabet_mem t
  obtain ⟨_hReach, pC, hIdxC, hCz⟩ := hAll t ht
  have hCpresent : K.multiCosetInclude P hadm hgen hret
      C hCP pC = z := hCz.symm
  obtain ⟨hMC, _hAgree⟩ := hMin C hCP pC hCpresent
  have hSkel :
      (K.skeletonToMultiCosetHom P hadm hgen hret M hMP).onVertex x =
      (K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x :=
    K.skeletonToMultiCosetHom_vertex_independent
      P hadm hgen hret M C hMP hCP x
  have hRealC :
      G.Follows
        (K.multiCosetInclude P hadm hgen hret
          C hCP (K.attachedOfSkeletonVertex C x)) w z := by
    change G.Follows
      ((K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x)
      w z
    rw [← hSkel]
    exact hReal
  obtain ⟨q, hqIdx, hqZ⟩ :=
    K.multiCoset_selected_B_path_stays_in_coset
      P hadm hgen hret C hCP w (hwM.mono hMC)
      (K.attachedOfSkeletonVertex C x) z hRealC
  have hqp : q = pC :=
    K.multiCosetInclude_injective P hadm hgen hret
      C hCP (hqZ.symm.trans hCpresent.symm)
  refine ⟨hMC, ?_⟩
  calc
    K.componentClass C x = q.1 := hqIdx.symm
    _ = pC.1 := congrArg Sigma.fst hqp
    _ = K.properCosetTagIndex t := hIdxC

end CayleySubgraphSpec
end ABO
end PSTSEPPA
