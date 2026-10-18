import PSTSEPPA.ABO.MultiCosetVertexQuotient
import PSTSEPPA.ABO.MultiCosetOverlap
import PSTSEPPA.ABO.CosetIntersections
import PSTSEPPA.ABO.ComponentIndexMonotonicity

/-!
# ABO Lemma 4.3: ambient values ARE faithful between copies with ONE old skeleton anchor

The source proof's final B-cluster representation uses constituent
cosets v_i H[C_i] all based at one common original skeleton point x.
In this SPECIAL configuration the otherwise NONINJECTIVE ambient
Cayley-coordinate projection becomes faithful on the union of the
corresponding old-C-component-tagged completed constituent copies.

This theorem proves the exact pairwise injectivity statement:
For actual selected C,D-coset vertices pC,pD, suppose both
intrinsic ORIGINAL skeleton component tags are respectively
componentClass C x and componentClass D x for ONE actual skeleton
vertex x, and their ambient group coordinates are equal.

Retractability gives the exact algebraic coset intersection
xH[C] ∩ xH[D] = xH[C∩D]. The common ambient group point
therefore has a genuine attached (C∩D)-coset representative
over the ORIGINAL (C∩D)-component of x. Its canonical
attached-subalphabet maps have EXACTLY the specified C/D
tags and coordinates, hence equal the original pC,pD.

The literal original ABO equation (3.10) gluing quotient
then identifies their vertices. This uses the TRUE old
component tags; an analogous statement without a common
old skeleton anchor is FALSE in general.

This is a key injectivity ingredient in the source's final
finite-cluster labelled-graph isomorphism via Corollary 3.12,
but does not yet assert that whole isomorphism or add old edges.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- In the original signed component-tagged proper-coset quotient,
two selected completed coset vertices over the SAME original
old skeleton anchor x coincide whenever they have the SAME
ambient Cayley coordinate, even across different alphabets.

The common anchor/tag assumptions are ESSENTIAL. -/
theorem multiCosetInclude_eq_of_same_old_anchor_and_ambient_value
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C D : Finset ι)
    (hCP : C ∈ P.alphabets)
    (hDP : D ∈ P.alphabets)
    (x : K.Vertex)
    (pC : K.AttachedCosetVertex C)
    (pD : K.AttachedCosetVertex D)
    (hCtag : pC.1 = K.componentClass C x)
    (hDtag : pD.1 = K.componentClass D x)
    (hValue : pC.2.1 = pD.2.1) :
    K.multiCosetInclude P hadm hgen hret C hCP pC =
      K.multiCosetInclude P hadm hgen hret D hDP pD := by
  let E := C ∩ D
  have hCcoset : pC.2.1 ∈ generatedLeftCoset gen C x.1 := by
    have hh := pC.2.2
    rw [hCtag, K.componentAmbientCoset_class] at hh
    exact hh
  have hDcoset : pD.2.1 ∈ generatedLeftCoset gen D x.1 := by
    have hh := pD.2.2
    rw [hDtag, K.componentAmbientCoset_class] at hh
    exact hh
  have hPInD : pC.2.1 ∈ generatedLeftCoset gen D x.1 := by
    rw [hValue]
    exact hDcoset
  have hInter :
      generatedLeftCoset gen C x.1 ∩
        generatedLeftCoset gen D x.1 =
        generatedLeftCoset gen E x.1 :=
    generatedLeftCoset_inter gen hgen hret C D
      x.1 x.1 x.1
      (self_mem_generatedLeftCoset gen C x.1)
      (self_mem_generatedLeftCoset gen D x.1)
  have hEcoset : pC.2.1 ∈ generatedLeftCoset gen E x.1 := by
    rw [← hInter]
    exact ⟨hCcoset, hPInD⟩
  let pE : K.AttachedCosetVertex E :=
    ⟨K.componentClass E x, ⟨pC.2.1, hEcoset⟩⟩
  have hMapC :
      K.attachedSubalphabetMap E C
          Finset.inter_subset_left pE = pC := by
    apply K.attachedValue_injective_of_same_index C
    · calc
        (K.attachedSubalphabetMap E C
            Finset.inter_subset_left pE).1 =
          K.componentClass C x :=
            K.componentIndexMap_class E C
              Finset.inter_subset_left x
        _ = pC.1 := hCtag.symm
    · rfl
  have hMapD :
      K.attachedSubalphabetMap E D
          Finset.inter_subset_right pE = pD := by
    apply K.attachedValue_injective_of_same_index D
    · calc
        (K.attachedSubalphabetMap E D
            Finset.inter_subset_right pE).1 =
          K.componentClass D x :=
            K.componentIndexMap_class E D
              Finset.inter_subset_right x
        _ = pD.1 := hDtag.symm
    · exact hValue
  apply Quotient.sound
  change K.ShareIntersectionSupport C D pC pD
  exact ⟨pE, hMapC, hMapD⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
