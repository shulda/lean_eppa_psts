import PSTSEPPA.ABO.Lemma43ProperSupportedSliceBridgeLift
import PSTSEPPA.ABO.Lemma43LowerMinimumSupportImageTransfer

/-!
# ABO Lemma 4.3: extend the lower minimum to the ENTIRE upper coset slice

This is the next source-specific step of the published Lemma 4.3
(PDF pp.35–36). A B-component piece B_i inside one maximal
complete constituent vH[C] is a D=B∩C coset, with D⊊C in
the genuine off-skeleton cluster case. Its intersection with
the lower CE of the selected original old C-component is a
nonempty D-component: bridge freeness makes the intersection
D-connected.

Assume the lower D-component S has minimum original tagged
support (M,m), as furnished by the lower-rank cluster-property
induction. We prove the SAME transported pair is a genuine
minimum support of the ENTIRE upper D-component of the
selected lower basepoint, even if some of its vertices do
not lie in the lower stage.

For any competing upper support (E,q) of a vertex y in this
larger D-component, distinguish two exact source cases:

(1) C ⊆ E: the actual D-path stays in the very same tagged
    complete C-copy. The minimum tag of the lower basepoint
    maps to this C tag; the existing C-to-E inclusion from
    true quotient equality then proves M⊆E and the original
    E-component index equality.

(2) C ⊄ E: the tagged (C∩E) support is STRICTLY BELOW C.
    The previously independently checked source support
    intersection/bridge-free path lemma lifts y to a
    lower D-reachable x'. The lower minimum transported to
    the full upper IMAGE of S then controls y's E support.

Thus the source minimum support actually controls the
ENTIRE upper D-slice, not just the already embedded lower
intersection, with its original intrinsic OLD-component tag
and attainment at a genuine vertex of the slice.

This remains a CONDITIONAL Lemma-4.3 induction step:
lower bridge freeness and lower whole-component minimum
support are explicit hypotheses. Synchronizing minima of
TWO different maximal pieces by retractability (Figure 7/
Figure 8 in ABO) and the finite common-core/cluster step
are still separate and not assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Published ABO Lemma 4.3: from the LOWER D-component's
minimum tagged support to the ENTIRE actual upper D-path
component inside the selected C-constituent.

The explicit lower-rank bridge-free assumption is source
condition (1), and the lower minimum-support assumption is
the source lower-rank cluster property (2). There is no
globally unqualified cluster theorem here. -/
theorem lowerComponent_minimalTaggedSupport_entire_upper_slice
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
    (x0 : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret)
    (hx0C :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP pC =
      (K.lowerComponentToFullMultiCosetHom
        C hCA root hadm hgen hret).onVertex x0)
    (S : Set ((K.subalphabetComponentSubgraph C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret))
    (hS : ∀ x,
      x ∈ S ↔
        ∃ w : LabelWord ι, LabelWord.Uses D w ∧
          ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
            (allProperCosetFamily C)
            (K.subalphabetComponentSubgraph_admissible
              hadm C hCA root) hgen hret).Follows x0 w x)
    (M : Finset ι) (hMC : M ⊂ C)
    (m : (K.subalphabetComponentSubgraph C root).ComponentIndex M)
    (hMin :
      (K.subalphabetComponentSubgraph C root).IsMinimalTaggedSupportFor
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret S M m) :
    K.IsMinimalTaggedSupportFor (allProperCosetFamily A)
      hadm hgen hret
      { y | ∃ w : LabelWord ι, LabelWord.Uses D w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex x0) w y }
      M (K.componentSubgraphIndexMap C M hMC.subset root m) := by
  let L := K.subalphabetComponentSubgraph C root
  let Q := allProperCosetFamily C
  let P := allProperCosetFamily A
  let hAdmL := K.subalphabetComponentSubgraph_admissible
    hadm C hCA root
  let J := K.lowerComponentToFullMultiCosetHom
    C hCA root hadm hgen hret
  let U := K.multiCosetEGraph P hadm hgen hret
  let mUpper := K.componentSubgraphIndexMap C M hMC.subset root m
  have hMinImage :
      K.IsMinimalTaggedSupportFor P hadm hgen hret
        (J.onVertex '' S) M mUpper :=
    K.lowerComponentToFull_minimalTaggedSupport_image
      C hCA root hadm hgen hret
      S M hMC m hMin
  constructor
  · obtain ⟨⟨y, hyImage, hyMinSupport⟩, _⟩ := hMinImage
    obtain ⟨x, hxS, hJx⟩ := hyImage
    obtain ⟨w, hw, hLowerPath⟩ := (hS x).mp hxS
    refine ⟨y, ?_, hyMinSupport⟩
    refine ⟨w, hw, ?_⟩
    rw [← hJx]
    exact hLowerPath.map J
  · intro E hEP pE y hySlice hEy
    obtain ⟨w, hw, hPath⟩ := hySlice
    by_cases hCE : C ⊆ E
    · have hX0S : x0 ∈ S :=
        (hS x0).mpr
          ⟨[], LabelWord.uses_nil D, EGraph.Follows.nil x0⟩
      have hX0Image : J.onVertex x0 ∈ J.onVertex '' S :=
        ⟨x0, hX0S, rfl⟩
      obtain ⟨hMEatC, hMtagC⟩ :=
        hMinImage.2 C hCP pC (J.onVertex x0) hX0Image hx0C
      have hFromC : U.Follows
          (K.multiCosetInclude P hadm hgen hret C hCP pC)
          w y := by
        rw [hx0C]
        exact hPath
      obtain ⟨pCy, hpCyIndex, hpCy⟩ :=
        K.multiCoset_selected_B_path_stays_in_coset
          P hadm hgen hret C hCP w
          (hw.mono hDC.subset) pC y hFromC
      have hEfromC :
          K.attachedSubalphabetMap C E hCE pCy = pE := by
        apply K.multiCosetInclude_injective
          P hadm hgen hret E hEP
        calc
          K.multiCosetInclude P hadm hgen hret
              E hEP (K.attachedSubalphabetMap C E hCE pCy) =
            K.multiCosetInclude P hadm hgen hret C hCP pCy :=
              (K.multiCosetInclude_alphabet_mono
                P hadm hgen hret C E hCE hCP hEP pCy).symm
          _ = y := hpCy.symm
          _ = K.multiCosetInclude P hadm hgen hret E hEP pE :=
            hEy.symm
      have hEtag :
          K.componentIndexMap C E hCE pCy.1 = pE.1 :=
        congrArg (K.attachedIndex E) hEfromC
      let hME : M ⊆ E := hMEatC.trans hCE
      refine ⟨hME, ?_⟩
      calc
        K.componentIndexMap M E hME mUpper =
          K.componentIndexMap C E hCE
            (K.componentIndexMap M C hMEatC mUpper) :=
          (K.componentIndexMap_comp
            M C E hMEatC hCE mUpper).symm
        _ = K.componentIndexMap C E hCE pC.1 :=
          congrArg (K.componentIndexMap C E hCE) hMtagC
        _ = K.componentIndexMap C E hCE pCy.1 :=
          congrArg (K.componentIndexMap C E hCE) hpCyIndex.symm
        _ = pE.1 := hEtag
    · obtain ⟨x', hx'Image, w', hw', hLowerPath, _hUpperPath⟩ :=
        K.lowerComponent_properSupportedSlice_reflect_D_path
          C hCA root hadm hgen hret D hDC hBridge
          hCP pC hpCRoot x0 hx0C y
          ⟨w, hw, hPath⟩ E hEP pE hEy hCE
      have hx'S : x' ∈ S :=
        (hS x').mpr ⟨w', hw', hLowerPath⟩
      have hyImage : y ∈ J.onVertex '' S :=
        ⟨x', hx'S, hx'Image⟩
      exact hMinImage.2 E hEP pE y hyImage hEy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
