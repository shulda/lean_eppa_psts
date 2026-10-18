import PSTSEPPA.ABO.Lemma43LowerTaggedSupportNaturality
import PSTSEPPA.ABO.ComponentCosetNaturality

/-!
# ABO Lemma 4.3: transfer a minimum support across the actual lower-stage embedding

This theorem is the next PUBLISHED step of the proof of ABO I,
Lemma 4.3 (PDF pp.35–36), following lower-stage intersection
nonemptiness and connectedness. A genuine lower whole-subgraph
minimum support (D,c), attained at a vertex of the lower
subgraph S, continues to be the minimum tagged support for
the EXACT image of S inside the upper full proper coset extension.

The difficult direction is that an upper support of an image
point can be indexed by an arbitrary E ⊊ A, possibly
incomparable with the lower parent C. It cannot simply be
treated as a lower-stage support.

The proof follows the source's genuine support intersection
(3.11). Intersect this arbitrary E-support with any existing
lower F⊊C support of the SAME vertex, obtaining a true tagged
H=E∩F support. Because H⊊C, independently checked support
reflection for the exact lower embedding supplies a lower
H-support. Apply the lower MINIMUM property to that actual
support, then use naturality of original old-component index
enlargements to conclude that D⊆E and the original upper
D-component index maps to the exact E-component tag.

The source statements refer to entire off-skeleton pieces B_i.
This theorem is deliberately for the EMBEDDED LOWER SUBGRAPH
S, not for all points of B_i outside that lower image.
The subsequent source Lemma-4.3 support-extension argument
and cross-constituent synchronization are not asserted here.

All supports are actual original-component-tagged CE quotient
points; no false global Cayley embedding, fake old edges,
new axiom or sorry is assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The MINIMUM (D,d) support of any genuine lower-stage
vertex subset S remains a minimum support of its exactly
embedded image in the upper source's full tagged multiCE.

This holds for arbitrary upper competing support alphabets
E⊊A, not just E⊆C. The actual (E∩F) gluing support and
the support-reflection theorem supply the necessary reduction
from arbitrary E to a lower support. -/
theorem lowerComponentToFull_minimalTaggedSupport_image
    (C : Finset ι) (hCA : C ⊂ A)
    (root : K.Vertex)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (S : Set ((K.subalphabetComponentSubgraph C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret))
    (D : Finset ι) (hDC : D ⊂ C)
    (d : (K.subalphabetComponentSubgraph C root).ComponentIndex D)
    (hMin :
      (K.subalphabetComponentSubgraph C root).IsMinimalTaggedSupportFor
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret S D d) :
    K.IsMinimalTaggedSupportFor (allProperCosetFamily A)
      hadm hgen hret
      ((K.lowerComponentToFullMultiCosetHom
        C hCA root hadm hgen hret).onVertex '' S)
      D (K.componentSubgraphIndexMap C D hDC.subset root d) := by
  let L := K.subalphabetComponentSubgraph C root
  let J := K.lowerComponentToFullMultiCosetHom
    C hCA root hadm hgen hret
  let Q := allProperCosetFamily C
  let P := allProperCosetFamily A
  let hAdmL := K.subalphabetComponentSubgraph_admissible
    hadm C hCA root
  obtain ⟨⟨x0, hx0, hSupport0⟩, hMinEvery⟩ := hMin
  constructor
  · refine ⟨J.onVertex x0, ⟨x0, hx0, rfl⟩, ?_⟩
    exact K.lowerComponentToFull_hasTaggedSupportAt
      C hCA root hadm hgen hret D hDC d x0 hSupport0
  · intro E hEP q y hy hE
    obtain ⟨x, hxS, rfl⟩ := hy
    obtain ⟨F, ⟨hFP, pF, hpFx⟩⟩ :=
      L.multiCosetVertex_exists_support
        Q hAdmL hgen hret x
    have hFC : F ⊂ C :=
      (mem_allProperCosetFamily C F).mp hFP
    have hUpperF :
        K.HasTaggedSupportAt P hadm hgen hret
          F (K.componentSubgraphIndexMap C F
            hFC.subset root pF.1) (J.onVertex x) :=
      K.lowerComponentToFull_hasTaggedSupportAt
        C hCA root hadm hgen hret F hFC pF.1 x
        ⟨hFP, pF, rfl, hpFx⟩
    obtain ⟨hFAP, pUpperF, hpFtag, hpFz⟩ := hUpperF
    let H : Finset ι := E ∩ F
    have hHAP : H ∈ P.alphabets :=
      allProperCosetFamily_inter_mem A E F hEP hFAP
    obtain ⟨r, hrz, hrE, _hrF⟩ :=
      K.multiCosetVertex_two_supports_intersection
        P hadm hgen hret (J.onVertex x)
        E F hEP hFAP hHAP
        q pUpperF hE hpFz
    have hHC : H ⊂ C := by
      refine ⟨Finset.inter_subset_right.trans hFC.subset, ?_⟩
      intro hCH
      exact hFC.2 (hCH.trans Finset.inter_subset_right)
    have hUpperH :
        K.HasTaggedSupportAt P hadm hgen hret
          H r.1 (J.onVertex x) :=
      ⟨hHAP, r, rfl, hrz⟩
    obtain ⟨cH, ⟨hHP, pH, hTagLower, hpHz⟩, hTagUpper⟩ :=
      K.lowerComponentToFull_reflectTaggedSupportAt
        C hCA root hadm hgen hret H hHC r.1 x hUpperH
    obtain ⟨hDH, hMinTag⟩ :=
      hMinEvery H hHP pH x hxS hpHz
    let hDE : D ⊆ E := hDH.trans Finset.inter_subset_left
    refine ⟨hDE, ?_⟩
    have hUpperHIdx :
        K.componentSubgraphIndexMap C H hHC.subset root pH.1 =
          r.1 := by
      calc
        K.componentSubgraphIndexMap C H hHC.subset root pH.1 =
          K.componentSubgraphIndexMap C H hHC.subset root cH :=
            congrArg
              (K.componentSubgraphIndexMap C H hHC.subset root)
              hTagLower
        _ = r.1 := hTagUpper
    have hDToH :
        K.componentIndexMap D H hDH
            (K.componentSubgraphIndexMap C D hDC.subset root d) =
          r.1 := by
      calc
        _ = K.componentSubgraphIndexMap C H hHC.subset root
              (L.componentIndexMap D H hDH d) :=
            (K.componentSubgraphIndexMap_natural
              C D H hDH hHC.subset root d).symm
        _ = K.componentSubgraphIndexMap C H hHC.subset root
              pH.1 :=
            congrArg
              (K.componentSubgraphIndexMap C H hHC.subset root)
              hMinTag
        _ = r.1 := hUpperHIdx
    have hRToE :
        K.componentIndexMap H E Finset.inter_subset_left r.1 =
          q.1 :=
      congrArg (K.attachedIndex E) hrE
    calc
      K.componentIndexMap D E hDE
          (K.componentSubgraphIndexMap C D hDC.subset root d) =
        K.componentIndexMap H E Finset.inter_subset_left
          (K.componentIndexMap D H hDH
            (K.componentSubgraphIndexMap C D hDC.subset root d)) :=
        (K.componentIndexMap_comp
          D H E hDH Finset.inter_subset_left
          (K.componentSubgraphIndexMap C D hDC.subset root d)).symm
      _ = K.componentIndexMap H E Finset.inter_subset_left r.1 :=
        congrArg (K.componentIndexMap H E Finset.inter_subset_left) hDToH
      _ = q.1 := hRToE

end CayleySubgraphSpec
end ABO
end PSTSEPPA
