import PSTSEPPA.ABO.Lemma43ClusterVertexImage
import PSTSEPPA.ABO.CoatomEdgeCover
import PSTSEPPA.ABO.MultiCosetEdgeQuotient

/-!
# ABO Lemma 4.3: exact SIGNED-EDGE image of one common-core B-component

The existing source-realized signed B-component Q of the original
incomplete component-tagged multiCE has its ambient vertex image
identified with the translated union of full lower-alphabet cosets
ambient(z) G[B∩C], one for each active maximal coatom tag.
This module proves the corresponding oriented signed EDGE-SET
equality required to identify the source with the translated
B-cluster in published ABO I Lemma 4.3 / Corollary 3.12.

Fix an ACTUAL quotient core z belonging to every active tagged
coatom constituent of Q. Then the ambient projections of the
ACTUAL signed B-edge tokens with source in Q are EXACTLY the
full Cayley edges (g,s) with:
  - source g in ambient(z) G[B∩C] for some active C-tag;
  - underlying signed letter s in B∩C.

The forward direction retains the source signed edge token and
uses the true coatom completed edge presentation of
CoatomEdgeCover; hence its chosen coatom C CONTAINS the
actual signed base letter of the edge. It is not enough
merely that the original edge endpoints happen to lie
in one C-constituent.

Conversely, for any such full Cayley (g,s) edge, construct a
genuine point with ORIGINAL C-component tag from the core,
then the real completed-C signed s-edge token from the
source quotient. Its source is in Q because the exact
tagged C-slice theorem gives a REAL B-labelled path from
the original Q anchor. Thus the edge exists in the
original incomplete multiCE; it is NOT invented in the
old skeleton or by the later legal completion.

This is EDGE IMAGE surjectivity and equality, not an
unqualified global injection. Combined with accepted
restricted vertex faithfulness #743 and the separately
verified signed edge injection #744, it is the exact
set-level content needed for the source's final
labelled-cluster graph isomorphism.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- For one REAL common-core B-component of the ORIGINAL
old+fresh full proper multiCE, the projected ORIGINAL
oriented signed B-edge token set equals the translated
union of FULL B∩C-Cayley edge sets over active exact
original component-tagged maximal C-constituents.

The original B-edges may come from genuine old skeleton
edges or fresh completed coset edges; both are preserved
with formal inverse signs and original tag identities. -/
theorem allProperCoset_B_component_ambient_signed_edge_image_eq_cluster
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι)
    (anchor z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        z ∈ K.properCosetTagSlice hadm hgen hret B anchor t) :
    { a : ActionEdge Γ ι |
      ∃ e : K.MultiCosetEdgeVertexIncidenceQuotient
          (allProperCosetFamily A) hadm hgen hret,
        (signedBase
          ((K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).label e) ∈ B ∧
        ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w
              ((K.multiCosetEGraph (allProperCosetFamily A)
                hadm hgen hret).source e)) ∧
        K.multiCosetEdgeQuotientAmbient
          (allProperCosetFamily A) hadm hgen hret e = a } =
    { a : ActionEdge Γ ι |
      ∃ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        (cayleyGraph gen).source a ∈
          generatedLeftCoset gen
            (B ∩ K.properCosetTagAlphabet t)
            (K.multiCosetAmbientValue
              (allProperCosetFamily A) hadm hgen hret z) ∧
        signedBase ((cayleyGraph gen).label a) ∈
          B ∩ K.properCosetTagAlphabet t } := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let H := K.multiCosetAmbientHom P hadm hgen hret
  ext a
  constructor
  · rintro ⟨e, ⟨hLabelB, hReach⟩, hProj⟩
    obtain ⟨C, hCP, p, s, hCcard, he⟩ :=
      K.allProperCosetEdge_exists_coatom_completed_presentation
        hadm hgen hret hcard e
    let t : K.ProperCosetTag := ⟨⟨C, hCP⟩, p.1⟩
    have hSource : G.source e =
        K.multiCosetInclude P hadm hgen hret C hCP p := by
      rw [← he]
      rfl
    have hLabelC : signedBase (G.label e) ∈ C := by
      rw [← he]
      exact s.2
    have hSourceSlice :
        G.source e ∈ K.properCosetTagSlice
          hadm hgen hret B anchor t := by
      exact ⟨hReach, p, rfl, hSource⟩
    have ht : t ∈
        K.activeTaggedCoatoms hadm hgen hret B anchor :=
      (K.mem_activeTaggedCoatoms_iff
        hadm hgen hret B anchor t).mpr
        ⟨hCcard, ⟨G.source e, hSourceSlice⟩⟩
    have hCore : z ∈ K.properCosetTagSlice
        hadm hgen hret B anchor t := hAll t ht
    have hSourceProjected :
        K.multiCosetAmbientValue P hadm hgen hret (G.source e) =
          (cayleyGraph gen).source a := by
      change H.onVertex (G.source e) =
          (cayleyGraph gen).source a
      calc
        H.onVertex (G.source e) =
            (cayleyGraph gen).source (H.onEdge e) :=
          (H.map_source e).symm
        _ = (cayleyGraph gen).source a :=
          congrArg (cayleyGraph gen).source hProj
    have hSmall :
        (cayleyGraph gen).source a ∈
          generatedLeftCoset gen (B ∩ C)
            (K.multiCosetAmbientValue P hadm hgen hret z) :=
      (K.allProperCoset_tagged_slice_ambient_range_iff
        hadm hgen hret B anchor C hCP p.1 z hCore
        ((cayleyGraph gen).source a)).mp
          ⟨G.source e, hSourceSlice, hSourceProjected⟩
    have hLabelProjected :
        (cayleyGraph gen).label a = G.label e := by
      calc
        (cayleyGraph gen).label a =
            (cayleyGraph gen).label (H.onEdge e) :=
          congrArg (cayleyGraph gen).label hProj.symm
        _ = G.label e := H.map_label e
    have hSmallLabel :
        signedBase ((cayleyGraph gen).label a) ∈ B ∩ C := by
      rw [hLabelProjected]
      exact Finset.mem_inter.mpr ⟨hLabelB, hLabelC⟩
    exact ⟨t, ht, hSmall, hSmallLabel⟩
  · rintro ⟨t, ht, hSmall, hSmallLabel⟩
    let C := K.properCosetTagAlphabet t
    let hCP : C ∈ P.alphabets :=
      K.properCosetTagAlphabet_mem t
    have hCore :
        z ∈ K.properCosetTagSlice hadm hgen hret B anchor t :=
      hAll t ht
    obtain ⟨⟨wz, hwz, hAZ⟩, pZ, hpZtag, hzEq⟩ := hCore
    have hMeet :
        ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          G.Follows
            (K.multiCosetInclude P hadm hgen hret C hCP pZ)
            w anchor := by
      refine ⟨PSTS.SignedWord.inv wz, hwz.inv, ?_⟩
      rw [← hzEq]
      exact G.follows_inverse hAZ
    have hZValue :
        K.multiCosetAmbientValue P hadm hgen hret z =
          pZ.2.1 := by
      rw [hzEq]
      rfl
    have hSourceSmall :
        (cayleyGraph gen).source a ∈
          generatedLeftCoset gen (B ∩ C) pZ.2.1 := by
      change (cayleyGraph gen).source a ∈
        generatedLeftCoset gen (B ∩ C)
          (K.multiCosetAmbientValue P hadm hgen hret z) at hSmall
      rw [hZValue] at hSmall
      exact hSmall
    have hSourceBig :
        (cayleyGraph gen).source a ∈
          generatedLeftCoset gen C pZ.2.1 :=
      generatedSubgroup_mono gen Finset.inter_subset_right
        hSourceSmall
    have hCosetEq : K.componentAmbientCoset C pZ.1 =
        generatedLeftCoset gen C pZ.2.1 :=
      K.componentAmbientCoset_eq_generatedLeftCoset_of_member
        C pZ.1 pZ.2.1 pZ.2.2
    have hSourceMember :
        (cayleyGraph gen).source a ∈
          K.componentAmbientCoset C pZ.1 := by
      rw [hCosetEq]
      exact hSourceBig
    let p : K.AttachedCosetVertex C :=
      ⟨pZ.1, ⟨(cayleyGraph gen).source a, hSourceMember⟩⟩
    let s : {s : SignedLabel ι // signedBase s ∈ C} :=
      ⟨(cayleyGraph gen).label a,
        (Finset.mem_inter.mp hSmallLabel).2⟩
    have hToP :
        ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          G.Follows anchor w
            (K.multiCosetInclude P hadm hgen hret C hCP p) :=
      (K.multiCoset_B_component_selected_C_slice_exact
        P hadm hgen hret B C hCP pZ anchor hMeet p rfl).mpr
          hSourceSmall
    let e : K.MultiCosetEdgeVertexIncidenceQuotient
        P hadm hgen hret :=
      K.multiCosetEdgeInclude P hadm hgen hret
        C hCP (Sum.inr (p, s))
    have hLabelB : signedBase (G.label e) ∈ B := by
      change signedBase s.1 ∈ B
      exact (Finset.mem_inter.mp hSmallLabel).1
    have hReach :
        ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          G.Follows anchor w (G.source e) := by
      have hSourceE : G.source e =
          K.multiCosetInclude P hadm hgen hret C hCP p := rfl
      rw [hSourceE]
      exact hToP
    have hProj :
        K.multiCosetEdgeQuotientAmbient P hadm hgen hret e = a := by
      change ((cayleyGraph gen).source a,
        (cayleyGraph gen).label a) = a
      cases a
      rfl
    exact ⟨e, ⟨hLabelB, hReach⟩, hProj⟩

end CayleySubgraphSpec
end ABO
