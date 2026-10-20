import PSTSEPPA.ABO.Lemma43LowerOffSkeletonGate
import PSTSEPPA.ABO.Lemma43EntireUpperCosetSliceMinimalSupport
import PSTSEPPA.ABO.Lemma43LowerSupportMeetsEmbeddedStage
import PSTSEPPA.ABO.Lemma43TaggedSliceBInterCPaths

/-!
# ABO Lemma 4.3: derive the ENTIRE coatom-slice minimum from the lower induction

This is the remaining SOURCE transfer from the lower-rank
cluster property in ABO I Lemma 4.3 (PDF pp.35–36).

Fix a genuine original signed B-component Q of the
uncompleted component-tagged full proper coset extension
and a selected actual C-constituent slice S = Q ∩ vH[C].
Let D = B∩C be a proper subalphabet of C, as guaranteed
in the true non-full-coset branch by the checked
Lemma43NoLargeCoatomLowerRank. Assume S contains an
ACTUAL quotient point with genuine support over some
D₀⊊C. This is exactly the SOURCE "lower support at
the maximal-constituent boundary" property.

The already verified lower-stage contact theorem lifts
that point to an actual vertex x₀ of the original
intrinsic old C-component's lower CE(H,A_i;P_C),
with the exact original C-component tag unchanged.

The published lower-rank induction assumes that
this lower CE is bridge-free and has the cluster
property ONLY FOR COMPONENTS OFF ITS OWN OLD SKELETON.
The new source signed path lemma proves that off-skeleton premise
from the upper off-skeleton B-component; it is not assumed. We express its needed concrete consequence
as the existence of a tagged minimum support (M,m)
for the actual LOWER D-component of x₀.

By the verified Lemma43EntireUpperCosetSliceMinimalSupport
theorem, this minimum transfers to the ENTIRE UPPER
D-component of the image x₀. The independently
certified selected C-constituent path reflection
shows that upper D-component is EXACTLY the whole
original tagged slice S = Q∩vH[C], not merely its
intersection with the lower stage. Thus S itself
has an attained original-tagged minimum support.

This is a real induction step from the published proof,
not a new cluster argument. Bridge freeness and the
lower minimum are EXPLICIT premises, rather than
being asserted for arbitrary incomplete skeletons.
The source's preliminary coatom-slice support-drop,
single-constituent alternative and final B-cluster
identification remain separate upstream/downstream
gates; this theorem intentionally does NOT solve them.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- TRUE Lemma-4.3 lower-to-upper whole-slice minimum
transfer under the printed lower-rank hypotheses.

For a tagged C-slice S of one REAL B-component,
D=B∩C⊊C and one actual lower-supported point y∈S,
assume every lower rooted C-stage is bridge-free and
its relevant D-component has an attained minimum
component-tagged support of proper C-rank.

Then S has an attained minimum tagged support,
including its exact original old skeleton component
index. No additional support or path outside the
selected source objects is postulated. -/
theorem allProperCoset_tagged_slice_minimum_from_off_skeleton_lower_induction
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hDC : B ∩ C ⊂ C)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hy :
      y ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c)
    (hSmall :
      ∃ D₀ : Finset ι,
        D₀ ⊂ C ∧
        K.MultiCosetVertexSupported
          (allProperCosetFamily A)
          hadm hgen hret D₀ y)
    (hUpperOff :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            B hBP).onVertex x)
          w anchor)
    (hBridge :
      ∀ root : K.Vertex,
        (K.subalphabetComponentSubgraph C root).MultiCosetBridgeFree
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
          hgen hret)
    (hLowerMin :
      ∀ root : K.Vertex,
        ∀ x₀ : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
          hgen hret,
        (¬ ∃ (v : (K.subalphabetComponentSubgraph C root).Vertex)
          (w : LabelWord ι),
          LabelWord.Uses (B ∩ C) w ∧
          ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
            (allProperCosetFamily C)
            (K.subalphabetComponentSubgraph_admissible
              hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
            hgen hret).Follows
              (((K.subalphabetComponentSubgraph C root).skeletonToMultiCosetHom
                (allProperCosetFamily C)
                (K.subalphabetComponentSubgraph_admissible
                  hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
                hgen hret (B ∩ C)
                ((mem_allProperCosetFamily C (B ∩ C)).mpr hDC)).onVertex v)
              w x₀) →
        ∃ (M : Finset ι) (hMC : M ⊂ C)
          (m : (K.subalphabetComponentSubgraph C root).ComponentIndex M),
          (K.subalphabetComponentSubgraph C root).IsMinimalTaggedSupportFor
            (allProperCosetFamily C)
            (K.subalphabetComponentSubgraph_admissible
              hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
            hgen hret
            { x | ∃ w : LabelWord ι,
              LabelWord.Uses (B ∩ C) w ∧
              ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
                (allProperCosetFamily C)
                (K.subalphabetComponentSubgraph_admissible
                  hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
                hgen hret).Follows x₀ w x }
            M m) :
    ∃ (M : Finset ι) (m : K.ComponentIndex M),
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        (K.allProperCoset_taggedConstituentSlice
          hadm hgen hret B anchor C hCP c) M m := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let hCA : C ⊂ A := (mem_allProperCosetFamily A C).mp hCP
  obtain ⟨hyReach, pC, hpCtag, hCy⟩ := hy
  have hySlice :
      y ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c :=
    ⟨hyReach, pC, hpCtag, hCy⟩
  obtain ⟨D₀, hD₀C, ⟨hD₀P, pD₀, hD₀y⟩⟩ := hSmall
  obtain ⟨root, x₀, hRootTag, hJx₀⟩ :=
    K.allProperCoset_lower_support_point_in_embedded_lower_stage
      hadm hgen hret C D₀ hCA hD₀C
      hCP hD₀P pC pD₀ y hCy.symm hD₀y
  let L := K.subalphabetComponentSubgraph C root
  let hAdmL := K.subalphabetComponentSubgraph_admissible
    hadm C hCA root
  let Q := allProperCosetFamily C
  let J := K.lowerComponentToFullMultiCosetHom
    C hCA root hadm hgen hret
  let D := B ∩ C
  let S : Set (L.MultiCosetVertex Q hAdmL hgen hret) :=
    { x | ∃ w : LabelWord ι, LabelWord.Uses D w ∧
      (L.multiCosetEGraph Q hAdmL hgen hret).Follows x₀ w x }
  have hUpperReachJ :
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        G.Follows anchor w (J.onVertex x₀) := by
    obtain ⟨w, hw, hp⟩ := hyReach
    refine ⟨w, hw, ?_⟩
    rw [hJx₀]
    exact hp
  have hLowerOff :=
    K.lowerComponent_off_skeleton_of_upper_off_skeleton
      hadm hgen hret C hCA root B hBP (B ∩ C)
      hDC Finset.inter_subset_left anchor x₀
      hUpperReachJ hUpperOff
  obtain ⟨M, hMC, m, hMinS⟩ := hLowerMin root x₀ hLowerOff
  have hCroot : pC.1 = K.componentClass C root :=
    hRootTag.symm
  have hCx₀ :
      K.multiCosetInclude P hadm hgen hret C hCP pC =
        J.onVertex x₀ :=
    hCy.symm.trans hJx₀.symm
  have hUpperMin :=
    K.lowerComponent_minimalTaggedSupport_entire_upper_slice
      C hCA root hadm hgen hret
      D hDC (hBridge root)
      hCP pC hCroot x₀ hCx₀
      S (by intro x; rfl) M hMC m hMinS
  have hSliceEq :
      { t : K.MultiCosetVertex P hadm hgen hret |
        ∃ w : LabelWord ι, LabelWord.Uses D w ∧
          G.Follows (J.onVertex x₀) w t } =
      K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c := by
    ext t
    constructor
    · rintro ⟨w, hwD, hReal⟩
      have hFromC :
          G.Follows
            (K.multiCosetInclude P hadm hgen hret C hCP pC) w t := by
        rw [hCx₀]
        exact hReal
      obtain ⟨qC, hqIndex, hqTarget⟩ :=
        K.multiCoset_selected_B_path_stays_in_coset
          P hadm hgen hret C hCP w
          (hwD.mono Finset.inter_subset_right)
          pC t hFromC
      obtain ⟨w₀, hw₀, hAnchorY⟩ := hyReach
      have hYt : G.Follows y w t := by
        rw [← hJx₀]
        exact hReal
      have hAnchorT : ∃ v : LabelWord ι,
          LabelWord.Uses B v ∧ G.Follows anchor v t :=
        ⟨w₀ ++ w,
          (LabelWord.uses_append B _ _).mpr
            ⟨hw₀, hwD.mono Finset.inter_subset_left⟩,
          G.follows_append hAnchorY hYt⟩
      exact ⟨hAnchorT, qC, hqIndex.trans hpCtag, hqTarget⟩
    · intro ht
      obtain ⟨w, hwD, hReal⟩ :=
        K.allProperCoset_taggedSlice_B_inter_C_connected
          hadm hgen hret B C hCP
          anchor c y t hySlice ht
      refine ⟨w, hwD, ?_⟩
      rw [hJx₀]
      exact hReal
  refine ⟨M, K.componentSubgraphIndexMap C M hMC.subset root m, ?_⟩
  rw [← hSliceEq]
  exact hUpperMin

end CayleySubgraphSpec
end ABO
end PSTSEPPA
