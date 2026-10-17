import PSTSEPPA.ABO.Lemma43LowerIntersectionBridgeConnected
import PSTSEPPA.ABO.ComponentAttachmentRange
import PSTSEPPA.ABO.MultiCosetVertexSupport

/-!
# ABO Lemma 4.3: a proper-support point belongs to the lower stage

The published Lemma 4.3 (PDF p.36) uses two separate facts:
  * a B-component portion B_i inside a maximal C-constituent
    has a vertex supported on some proper alphabet D ⊊ C;
  * therefore B_i MEETS the actual embedded lower extension
    CE(H, A_i; P_C) of the intrinsic old C-component A_i.

The first support-drop geometry has already been certified in
MultiCosetWholeComponentBoundarySupport.lean. The present lemma
formalizes the precise SECOND implication on the original
COMPONENT-TAGGED multi-coset quotient, including original
old-component indices and the actual lower→upper labelled
graph embedding of Lemma43LowerIntersectionBridgeConnected.lean.

At an upper quotient vertex z presented both inside one
specific tagged full C-constituent pC and by a genuine proper
D⊊C support pD, the exact (3.10)/(3.11) quotient
identifications force the D-support's intrinsic parent-C
tag to be pC's tag. The already certified original
component-indexed attached-coset surjectivity lifts
pD into the lower C-component's D-attachment.
Its image in the upper full proper CE is EXACTLY z.

This is an EXISTENCE statement for a lower-stage meeting
point. It does not claim every vertex of B_i lies in
that lower stage; that would be false in general. The
source needs the separate bridge-freeness of the lower
extension to prove the INTERSECTION is B-connected.

There are no assumed fictitious old edges or ambient
Cayley coordinate identifications across component tags.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- ORIGINAL proper-support contact with a maximal C-piece
enters the ACTUAL embedded lower C-component coset extension.

More generally C only needs to be properly contained in A
and D properly contained in C; no maximality is needed
for this particular source Lemma-4.3 step.

The lower root carries the GENUINE old C-component tag
of the selected pC constituent. The preimage z is a
literal lower old/fresh proper-coset point. -/
theorem allProperCoset_lower_support_point_in_embedded_lower_stage
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C D : Finset ι)
    (hCA : C ⊂ A)
    (hDC : D ⊂ C)
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
    ∃ (root : K.Vertex)
      (x :
        (K.subalphabetComponentSubgraph C root).MultiCosetVertex
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C hCA root) hgen hret),
      K.componentClass C root = pC.1 ∧
        (K.lowerComponentToFullMultiCosetHom
          C hCA root hadm hgen hret).onVertex x = z := by
  let P := allProperCosetFamily A
  have hCmap :
      K.multiCosetInclude P hadm hgen hret
        D hDP pD =
      K.multiCosetInclude P hadm hgen hret
        C hCP
          (K.attachedSubalphabetMap D C hDC.subset pD) :=
    K.multiCosetInclude_alphabet_mono
      P hadm hgen hret
      D C hDC.subset hDP hCP pD
  have hAtt :
      K.attachedSubalphabetMap D C hDC.subset pD = pC :=
    (K.multiCosetInclude_injective
      P hadm hgen hret C hCP)
      (hCmap.symm.trans (hDz.trans hCz.symm))
  obtain ⟨root, hRootTag⟩ :=
    K.componentClass_surjective C pC.1
  have hParent :
      K.componentIndexMap D C hDC.subset pD.1 =
        K.componentClass C root := by
    calc
      K.componentIndexMap D C hDC.subset pD.1 =
          (K.attachedSubalphabetMap D C hDC.subset pD).1 := rfl
      _ = pC.1 := congrArg Sigma.fst hAtt
      _ = K.componentClass C root := hRootTag.symm
  obtain ⟨q, hq⟩ :=
    K.componentSubgraphAttachedMap_surj_of_parent
      C D hDC.subset root pD hParent
  have hDPsmall : D ∈ (allProperCosetFamily C).alphabets :=
    (mem_allProperCosetFamily C D).mpr hDC
  let L := K.subalphabetComponentSubgraph C root
  let x : L.MultiCosetVertex
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret :=
    L.multiCosetInclude (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret
      D hDPsmall q
  refine ⟨root, x, hRootTag, ?_⟩
  change
    K.multiCosetInclude P hadm hgen hret D
      (lowerAllProperFamily_subset C hCA hDPsmall)
      (K.componentSubgraphAttachedMap
        C D hDC.subset root q) = z
  rw [hq]
  exact hDz

end CayleySubgraphSpec
end ABO
end PSTSEPPA
