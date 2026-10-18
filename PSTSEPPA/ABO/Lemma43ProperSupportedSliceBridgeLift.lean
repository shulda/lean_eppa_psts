import PSTSEPPA.ABO.Lemma43LowerTaggedSupportNaturality
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.MultiCosetVertexSupport
import PSTSEPPA.ABO.ComponentAttachmentRange

/-!
# ABO Lemma 4.3: reflect proper-supported B-slice points into the lower stage

This is the published Lemma 4.3's further lower-stage
intersection argument, beyond the previously checked
nonempty intersection and bridge-free connectedness.

Fix one ORIGINAL intrinsically tagged C-coset constituent
of CE(K; P_A), an old C-component root with exactly that
tag, and a proper D⊊C. If a REAL signed D-path from the
embedded lower stage leads to a point y in that C-constituent,
then y need not itself lie in the lower stage: the ambient
C-constituent is a full coset while lower CE may be partial.

But suppose y has another genuine E-support with C not
contained in E. Actual (3.11) intersection support with its
C-presentation produces the smaller alphabet H=C∩E⊊C,
and the exact original attached H-component index lies over
the SELECTED old C-component tag. Hence H-support lifts
to the same lower C-component's full proper coset extension.
Lower BRIDGE-FREENESS then turns the ambient D-connection
from the original lower point into an actual signed D-path
inside the lower extension.

This is an explicit and necessary step toward passing
a lower *whole-subgraph* minimum support to the entire
ambient slice B_i in the source proof. It uses the genuine
old/fresh quotient, not abstract equality in Cayley(K).
The lower bridge-free hypothesis is exactly source Lemma 4.3
assumption (1); it is not inferred from admissibility.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Suppose a real D⊊C path starts at the embedded lower C-stage
point x and ends at y, and x starts inside a specific selected
C-constituent with the same intrinsic old C-component tag as
the lower root. If y has an upper E-support not containing C,
then y lies in the SAME lower stage image and is genuinely
D-connected to x inside that lower stage.

No assumption that the whole global B-component lies in
the lower image, and no assumption of upper bridge-freeness.
The proof explicitly uses lower bridge-freeness and tagged
C∩E support transport. -/
theorem lowerComponent_properSupportedSlice_reflect_D_path
    (C : Finset ι) (hCA : C ⊂ A)
    (root : K.Vertex)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D : Finset ι) (hDC : D ⊂ C)
    (hBridge :
      (K.subalphabetComponentSubgraph C root).MultiCosetBridgeFree
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (pC : K.AttachedCosetVertex C)
    (hpCRoot : pC.1 = K.componentClass C root)
    (x : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret)
    (hxC :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP pC =
      (K.lowerComponentToFullMultiCosetHom
        C hCA root hadm hgen hret).onVertex x)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hDPath :
      ∃ w : LabelWord ι, LabelWord.Uses D w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex x) w y)
    (E : Finset ι)
    (hEP : E ∈ (allProperCosetFamily A).alphabets)
    (pE : K.AttachedCosetVertex E)
    (hEy :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret E hEP pE = y)
    (hNotSup : ¬ C ⊆ E) :
    ∃ x' : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret,
      (K.lowerComponentToFullMultiCosetHom
        C hCA root hadm hgen hret).onVertex x' = y ∧
      ∃ w : LabelWord ι, LabelWord.Uses D w ∧
        ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C hCA root) hgen hret).Follows x w x' ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex x)
          w
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex x') := by
  let P := allProperCosetFamily A
  let Q := allProperCosetFamily C
  let L := K.subalphabetComponentSubgraph C root
  let J := K.lowerComponentToFullMultiCosetHom
    C hCA root hadm hgen hret
  let U := K.multiCosetEGraph P hadm hgen hret
  let hAdmL := K.subalphabetComponentSubgraph_admissible
    hadm C hCA root
  obtain ⟨w0, hw0, hPath0⟩ := hDPath
  have hFromC : U.Follows
      (K.multiCosetInclude P hadm hgen hret C hCP pC)
      w0 y := by
    rw [hxC]
    exact hPath0
  obtain ⟨pCy, hpCindex, hpCy⟩ :=
    K.multiCoset_selected_B_path_stays_in_coset
      P hadm hgen hret C hCP w0
      (hw0.mono hDC.subset) pC y hFromC
  let H : Finset ι := C ∩ E
  have hHP : H ∈ P.alphabets :=
    allProperCosetFamily_inter_mem A C E hCP hEP
  obtain ⟨pH, hHy, hpHC, _hpHE⟩ :=
    K.multiCosetVertex_two_supports_intersection
      P hadm hgen hret y
      C E hCP hEP hHP
      pCy pE hpCy.symm hEy
  have hHC : H ⊂ C := by
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro hCH
    apply hNotSup
    intro t ht
    exact (Finset.mem_inter.mp (hCH ht)).2
  have hParent :
      K.componentIndexMap H C Finset.inter_subset_left pH.1 =
        K.componentClass C root := by
    calc
      K.componentIndexMap H C Finset.inter_subset_left pH.1 =
        pCy.1 := congrArg (K.attachedIndex C) hpHC
      _ = pC.1 := hpCindex
      _ = K.componentClass C root := hpCRoot
  obtain ⟨pLowerH, hpLift⟩ :=
    K.componentSubgraphAttachedMap_surj_of_parent
      C H Finset.inter_subset_left root pH hParent
  have hHQ : H ∈ Q.alphabets :=
    (mem_allProperCosetFamily C H).mpr hHC
  let x' : L.MultiCosetVertex Q hAdmL hgen hret :=
    L.multiCosetInclude Q hAdmL hgen hret H hHQ pLowerH
  have hJx' : J.onVertex x' = y := by
    calc
      J.onVertex x' =
        K.multiCosetInclude P hadm hgen hret H
          (lowerAllProperFamily_subset C hCA hHQ)
          (K.componentSubgraphAttachedMap C H
            hHC.subset root pLowerH) :=
        K.lowerComponentToFullMultiCosetHom_include
          C hCA root hadm hgen hret H hHQ pLowerH
      _ = K.multiCosetInclude P hadm hgen hret H
          hHP pH := by rw [hpLift]
      _ = y := hHy
  have hPathUpper :
      ∃ w : LabelWord ι, LabelWord.Uses D w ∧
        U.Follows (J.onVertex x) w (J.onVertex x') := by
    refine ⟨w0, hw0, ?_⟩
    rw [hJx']
    exact hPath0
  obtain ⟨w, hw, hLower, hUpper⟩ :=
    K.lowerComponent_bridgeFree_reflect_upper_path
      C hCA root hadm hgen hret
      D hDC hBridge x x' hPathUpper
  exact ⟨x', hJx', w, hw, hLower, hUpper⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
