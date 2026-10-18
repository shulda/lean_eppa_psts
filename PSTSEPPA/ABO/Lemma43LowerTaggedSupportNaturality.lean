import PSTSEPPA.ABO.Lemma43LowerSupportMeetsEmbeddedStage
import PSTSEPPA.ABO.Definition322WholeComponentMinimalSupport
import PSTSEPPA.ABO.ComponentParentIndexControl
import PSTSEPPA.ABO.ComponentAttachmentRange

/-!
# ABO Lemma 4.3: genuine tagged support transport and reflection

In the published proof of Lemma 4.3, the minimum support of the
lower component piece is transferred to the corresponding upper
maximal-constituent piece before supports of different pieces
are synchronized by retractability.

We first establish the *pointwise* structural fact needed for that
transfer, in BOTH directions. For an actual old+fresh quotient point
x of the lower CE(H, A_i; P_{A_i}), any genuine D-support with
D ⊊ A_i:
  (i) maps to a genuine upper support with its ORIGINAL component
      tag transported through the intrinsic skeleton inclusion;
  (ii) conversely, EVERY upper tagged D-support of its upper image
       has an actual lower tagged D-support mapping to it, with the
       same old-component index in H.

For the converse, the upper D-presentation meets an existing
lower E-presentation of x. The TRUE quotient rule (3.11) supplies
a (D∩E)-component-tagged intersection witness. The old
C-parent tag of this witness is the selected root component
by the accepted parent-index invariant, so the exact
attached-coset lifting theorem supplies the lower D-point.
Finally injectivity of the ACTUAL lower→upper multiCE graph
embedding recovers equality of quotient points.

No false global ambient Cayley injection, arbitrary old-edge
completion, newly assumed cluster property, or asserted
synchronization between distinct lower pieces is used.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Literal inclusion formula for a genuine component-tagged D
attachment in the source lower CE, sent through the exact
full proper upper multiCE graph morphism. -/
theorem lowerComponentToFullMultiCosetHom_include
    (C : Finset ι) (hCA : C ⊂ A)
    (root : K.Vertex)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D : Finset ι)
    (hDP : D ∈ (allProperCosetFamily C).alphabets)
    (p : (K.subalphabetComponentSubgraph C root).AttachedCosetVertex D) :
    (K.lowerComponentToFullMultiCosetHom
      C hCA root hadm hgen hret).onVertex
        ((K.subalphabetComponentSubgraph C root).multiCosetInclude
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C hCA root) hgen hret D hDP p) =
    K.multiCosetInclude (allProperCosetFamily A)
      hadm hgen hret D
      (lowerAllProperFamily_subset C hCA hDP)
      (K.componentSubgraphAttachedMap C D
        (((mem_allProperCosetFamily C D).mp hDP).subset)
        root p) := by
  rfl

/-- Genuine lower tagged D-support transports to the upper original
coset extension, with EXACT original D-component index.
The proof works for both old and newly attached vertices and
both orientations of signed graph edges. -/
theorem lowerComponentToFull_hasTaggedSupportAt
    (C : Finset ι) (hCA : C ⊂ A)
    (root : K.Vertex)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D : Finset ι)
    (hDC : D ⊂ C)
    (d : (K.subalphabetComponentSubgraph C root).ComponentIndex D)
    (x : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret)
    (hSupport :
      (K.subalphabetComponentSubgraph C root).HasTaggedSupportAt
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret D d x) :
    K.HasTaggedSupportAt (allProperCosetFamily A)
      hadm hgen hret D
      (K.componentSubgraphIndexMap C D hDC.subset root d)
      ((K.lowerComponentToFullMultiCosetHom
        C hCA root hadm hgen hret).onVertex x) := by
  let L := K.subalphabetComponentSubgraph C root
  let J := K.lowerComponentToFullMultiCosetHom
    C hCA root hadm hgen hret
  obtain ⟨hDP, p, hpIndex, hpx⟩ := hSupport
  refine ⟨lowerAllProperFamily_subset C hCA hDP,
    K.componentSubgraphAttachedMap C D hDC.subset root p, ?_, ?_⟩
  · change K.componentSubgraphIndexMap C D hDC.subset root p.1 =
      K.componentSubgraphIndexMap C D hDC.subset root d
    exact congrArg (K.componentSubgraphIndexMap
      C D hDC.subset root) hpIndex
  · calc
      K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret D (lowerAllProperFamily_subset C hCA hDP)
          (K.componentSubgraphAttachedMap
            C D hDC.subset root p) =
        J.onVertex (L.multiCosetInclude
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C hCA root) hgen hret D hDP p) :=
        (K.lowerComponentToFullMultiCosetHom_include
          C hCA root hadm hgen hret D hDP p).symm
      _ = J.onVertex x := congrArg J.onVertex hpx

/-- Crucial converse for ABO Lemma 4.3.

If an ACTUAL embedded lower-stage vertex has any upper
D-support with D ⊊ C, then that very support (including
the intrinsic OLD skeleton D-component tag) comes from
a genuine lower D-attachment supporting its lower vertex.

This is NOT a claim for support alphabets D outside C, and
does not assert the whole-source cluster property. -/
theorem lowerComponentToFull_reflectTaggedSupportAt
    (C : Finset ι) (hCA : C ⊂ A)
    (root : K.Vertex)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D : Finset ι) (hDC : D ⊂ C)
    (d : K.ComponentIndex D)
    (x : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret)
    (hUpper :
      K.HasTaggedSupportAt (allProperCosetFamily A)
        hadm hgen hret D d
        ((K.lowerComponentToFullMultiCosetHom
          C hCA root hadm hgen hret).onVertex x)) :
    ∃ c : (K.subalphabetComponentSubgraph C root).ComponentIndex D,
      (K.subalphabetComponentSubgraph C root).HasTaggedSupportAt
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret D c x ∧
      K.componentSubgraphIndexMap C D hDC.subset root c = d := by
  let L := K.subalphabetComponentSubgraph C root
  let J := K.lowerComponentToFullMultiCosetHom
    C hCA root hadm hgen hret
  let P := allProperCosetFamily A
  let Q := allProperCosetFamily C
  obtain ⟨hDP, pD, hpDtag, hpDupper⟩ := hUpper
  induction x using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨E, pE⟩
      let hEC : E.1 ⊆ C :=
        ((mem_allProperCosetFamily C E.1).mp E.2).subset
      let pUpperE : K.AttachedCosetVertex E.1 :=
        K.componentSubgraphAttachedMap C E.1 hEC root pE
      have hEP : E.1 ∈ P.alphabets :=
        lowerAllProperFamily_subset C hCA E.2
      have hEqUpper :
          K.multiCosetInclude P hadm hgen hret
            D hDP pD =
          K.multiCosetInclude P hadm hgen hret
            E.1 hEP pUpperE := by
        calc
          K.multiCosetInclude P hadm hgen hret D hDP pD =
            J.onVertex
              (L.multiCosetInclude Q
                (K.subalphabetComponentSubgraph_admissible
                  hadm C hCA root)
                hgen hret E.1 E.2 pE) := hpDupper
          _ = K.multiCosetInclude P hadm hgen hret
                E.1 hEP pUpperE :=
            K.lowerComponentToFullMultiCosetHom_include
              C hCA root hadm hgen hret E.1 E.2 pE
      have hShared :
          K.ShareIntersectionSupport D E.1 pD pUpperE := by
        have he := Quotient.exact hEqUpper
        change K.ShareIntersectionSupport D E.1 pD pUpperE at he
        exact he
      obtain ⟨r, hrD, hrE⟩ := hShared
      have hrEidx :
          K.componentIndexMap (D ∩ E.1) E.1
            Finset.inter_subset_right r.1 = pUpperE.1 :=
        congrArg (K.attachedIndex E.1) hrE
      have hParentInter :
          K.componentIndexMap (D ∩ E.1) C
            (Finset.inter_subset_right.trans hEC) r.1 =
            K.componentClass C root := by
        calc
          K.componentIndexMap (D ∩ E.1) C
              (Finset.inter_subset_right.trans hEC) r.1 =
            K.componentIndexMap E.1 C hEC
              (K.componentIndexMap (D ∩ E.1) E.1
                Finset.inter_subset_right r.1) :=
              (K.componentIndexMap_comp
                (D ∩ E.1) E.1 C
                Finset.inter_subset_right hEC r.1).symm
          _ = K.componentIndexMap E.1 C hEC pUpperE.1 :=
            congrArg (K.componentIndexMap E.1 C hEC) hrEidx
          _ = K.componentClass C root :=
            K.componentSubgraphAttachedMap_parent C E.1 hEC root pE
      have hrDidx :
          K.componentIndexMap (D ∩ E.1) D
            Finset.inter_subset_left r.1 = pD.1 :=
        congrArg (K.attachedIndex D) hrD
      have hParentD :
          K.componentIndexMap D C hDC.subset pD.1 =
            K.componentClass C root := by
        calc
          K.componentIndexMap D C hDC.subset pD.1 =
            K.componentIndexMap D C hDC.subset
              (K.componentIndexMap (D ∩ E.1) D
                Finset.inter_subset_left r.1) :=
              congrArg (K.componentIndexMap D C hDC.subset)
                hrDidx.symm
          _ = K.componentIndexMap (D ∩ E.1) C
              (Finset.inter_subset_left.trans hDC.subset) r.1 :=
            K.componentIndexMap_comp
              (D ∩ E.1) D C
              Finset.inter_subset_left hDC.subset r.1
          _ = K.componentIndexMap (D ∩ E.1) C
              (Finset.inter_subset_right.trans hEC) r.1 := rfl
          _ = K.componentClass C root := hParentInter
      obtain ⟨pLowerD, hpLift⟩ :=
        K.componentSubgraphAttachedMap_surj_of_parent
          C D hDC.subset root pD hParentD
      have hDPsmall : D ∈ Q.alphabets :=
        (mem_allProperCosetFamily C D).mpr hDC
      let y : L.MultiCosetVertex Q
          (K.subalphabetComponentSubgraph_admissible
            hadm C hCA root) hgen hret :=
        L.multiCosetInclude Q
          (K.subalphabetComponentSubgraph_admissible
            hadm C hCA root) hgen hret D hDPsmall pLowerD
      have hJy :
          J.onVertex y =
            J.onVertex (L.multiCosetInclude Q
              (K.subalphabetComponentSubgraph_admissible
                hadm C hCA root) hgen hret E.1 E.2 pE) := by
        calc
          J.onVertex y =
            K.multiCosetInclude P hadm hgen hret
              D (lowerAllProperFamily_subset C hCA hDPsmall)
                (K.componentSubgraphAttachedMap
                  C D hDC.subset root pLowerD) :=
              K.lowerComponentToFullMultiCosetHom_include
                C hCA root hadm hgen hret D hDPsmall pLowerD
          _ = K.multiCosetInclude P hadm hgen hret D hDP pD := by
            rw [hpLift]
          _ = J.onVertex (L.multiCosetInclude Q
                (K.subalphabetComponentSubgraph_admissible
                  hadm C hCA root) hgen hret E.1 E.2 pE) :=
            hEqUpper
      have hy :
          y = L.multiCosetInclude Q
            (K.subalphabetComponentSubgraph_admissible
              hadm C hCA root) hgen hret E.1 E.2 pE :=
        (K.lowerComponentToFullMultiCosetHom_vertex_injective
          C hCA root hadm hgen hret) hJy
      refine ⟨pLowerD.1, ?_, ?_⟩
      · refine ⟨hDPsmall, pLowerD, rfl, ?_⟩
        exact hy
      · have hTag :=
          congrArg (K.attachedIndex D) hpLift
        exact hTag.trans hpDtag

end CayleySubgraphSpec
end ABO
end PSTSEPPA
