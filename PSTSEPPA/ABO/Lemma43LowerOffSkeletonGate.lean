import PSTSEPPA.ABO.Lemma43LowerIntersectionBridgeConnected
import PSTSEPPA.ABO.MultiCosetComponentSupportDichotomy

/-!
# ABO Lemma 4.3: actual lower stages inherit the off-skeleton condition

Definition 3.22 requires whole-component minimum tagged support ONLY
for components avoiding the OLD skeleton. An unrestricted minimum
hypothesis on all lower D-components is generally false, even if
D is strictly smaller than its parent alphabet.

We prove three genuine signed graph facts:
(1) lower OLD skeleton vertices embed literally as upper OLD vertices;
(2) an upper off-skeleton B-component forces each embedded lower
D-component (D subset B, D proper C) that it meets to avoid the
lower original old C-skeleton;
(3) no selected full B-constituent supporting the upper component
implies this off-skeleton property, by genuine B-path invariance.

This repairs the induction-premise scope without identifying distinct
old-component tags, adding old edges or global ambient retractability.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The lower rooted old C-skeleton embeds into the upper FULL
multiCE as the exact original old signed skeleton vertex. -/
theorem lowerComponentToFullMultiCosetHom_skeleton
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCA : C ⊂ A) (root : K.Vertex)
    (D : Finset ι) (hDC : D ⊂ C)
    (x : (K.subalphabetComponentSubgraph C root).Vertex) :
    (K.lowerComponentToFullMultiCosetHom
       C hCA root hadm hgen hret).onVertex
      (((K.subalphabetComponentSubgraph C root).skeletonToMultiCosetHom
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible hadm C hCA root)
          hgen hret D
          ((mem_allProperCosetFamily C D).mpr hDC)).onVertex x) =
    (K.skeletonToMultiCosetHom
        (allProperCosetFamily A) hadm hgen hret
        D ((mem_allProperCosetFamily A D).mpr (lt_trans hDC hCA))).onVertex
      ((K.subalphabetComponentSubgraphHom C root).onVertex x) := by
  let Q := allProperCosetFamily C
  let P := allProperCosetFamily A
  let L := K.subalphabetComponentSubgraph C root
  let hAdmL := K.subalphabetComponentSubgraph_admissible hadm C hCA root
  let hDP : D ∈ Q.alphabets := (mem_allProperCosetFamily C D).mpr hDC
  change
    K.multiCosetFamilyVertexMap
      (Q.intoLarger hCA) P hadm hgen hret
      (lowerAllProperFamily_subset C hCA)
      (K.componentMultiCosetVertexMap C hCA root Q hadm hgen hret
        (L.multiCosetInclude Q hAdmL hgen hret D hDP
          (L.attachedOfSkeletonVertex D x))) =
    K.multiCosetInclude P hadm hgen hret D
      ((mem_allProperCosetFamily A D).mpr (lt_trans hDC hCA))
      (K.attachedOfSkeletonVertex D
        ((K.subalphabetComponentSubgraphHom C root).onVertex x))
  rw [K.componentMultiCosetVertexMap_skeleton
    C hCA root Q hadm hgen hret D hDP x]
  -- The enlarged-family membership proof is definitionally the
  -- same as hDP, but the rewrite tactic does not see through the
  -- family wrapper. The concrete inclusion computes definitionally.
  rfl

/-- If the upper B-component is off the original old skeleton,
then the corresponding lower D-component of an embedded vertex
is off the lower old C-skeleton. The reason is path transport,
not equality of ambient Cayley group coordinates. -/
theorem lowerComponent_off_skeleton_of_upper_off_skeleton
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCA : C ⊂ A) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (D : Finset ι) (hDC : D ⊂ C) (hDB : D ⊆ B)
    (anchor : K.MultiCosetVertex
       (allProperCosetFamily A) hadm hgen hret)
    (x0 : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
       (allProperCosetFamily C)
       (K.subalphabetComponentSubgraph_admissible hadm C hCA root)
       hgen hret)
    (hUpperReach :
       ∃ w : LabelWord ι, LabelWord.Uses B w ∧
       (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows anchor w
         ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex x0))
    (hUpperOff :
       ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
          LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows
              ((K.skeletonToMultiCosetHom
                (allProperCosetFamily A) hadm hgen hret
                B hBP).onVertex x)
              w anchor) :
    ¬ ∃ (x : (K.subalphabetComponentSubgraph C root).Vertex)
       (w : LabelWord ι),
          LabelWord.Uses D w ∧
          ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
             (allProperCosetFamily C)
             (K.subalphabetComponentSubgraph_admissible
               hadm C hCA root) hgen hret).Follows
              (((K.subalphabetComponentSubgraph C root).skeletonToMultiCosetHom
                (allProperCosetFamily C)
                (K.subalphabetComponentSubgraph_admissible
                  hadm C hCA root) hgen hret
                D ((mem_allProperCosetFamily C D).mpr hDC)).onVertex x)
              w x0 := by
  let P := allProperCosetFamily A
  let Q := allProperCosetFamily C
  let L := K.subalphabetComponentSubgraph C root
  let U := K.multiCosetEGraph P hadm hgen hret
  let J := K.lowerComponentToFullMultiCosetHom
    C hCA root hadm hgen hret
  let hDP : D ∈ Q.alphabets :=
    (mem_allProperCosetFamily C D).mpr hDC
  let hDAP : D ∈ P.alphabets :=
    (mem_allProperCosetFamily A D).mpr (lt_trans hDC hCA)
  rintro ⟨x, w, hw, hLocalPath⟩
  obtain ⟨v, hv, hAnchorToLower⟩ := hUpperReach
  have hMapped :
      U.Follows
        ((K.skeletonToMultiCosetHom
           P hadm hgen hret B hBP).onVertex
           ((K.subalphabetComponentSubgraphHom C root).onVertex x))
        w (J.onVertex x0) := by
    have hp := hLocalPath.map J
    rw [K.lowerComponentToFullMultiCosetHom_skeleton
      hadm hgen hret C hCA root D hDC x] at hp
    rw [K.skeletonToMultiCosetHom_vertex_independent
      P hadm hgen hret D B hDAP hBP
      ((K.subalphabetComponentSubgraphHom C root).onVertex x)] at hp
    exact hp
  apply hUpperOff
  refine ⟨(K.subalphabetComponentSubgraphHom C root).onVertex x,
    w ++ PSTS.SignedWord.inv v, ?_, ?_⟩
  · exact (LabelWord.uses_append B _ _).mpr
      ⟨hw.mono hDB, hv.inv⟩
  · exact U.follows_append hMapped (U.follows_inverse hAnchorToLower)

/-- The no-full-B-constituent branch is OFF the old skeleton,
by exact invariance of tagged B-support under ACTUAL signed B-paths. -/
theorem allProperCoset_noFull_implies_B_off_skeleton
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (hNoFull :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
          B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C anchor) :
    ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
         hadm hgen hret).Follows
        ((K.skeletonToMultiCosetHom
          (allProperCosetFamily A) hadm hgen hret B hBP).onVertex x)
        w anchor := by
  rintro ⟨x, w, hw, hpath⟩
  let P := allProperCosetFamily A
  let y :=
    (K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x
  have hSupportOld :
      K.MultiCosetVertexSupported P hadm hgen hret B y := by
    refine ⟨hBP, K.attachedOfSkeletonVertex B x, ?_⟩
    rfl
  have hSupportAtAnchor :
      K.MultiCosetVertexSupported P hadm hgen hret B anchor :=
    (K.multiCoset_selected_superset_support_invariant
      P hadm hgen hret B B (subset_rfl) y anchor
      ⟨w, hw, hpath⟩).mp hSupportOld
  exact hNoFull B hBP (subset_rfl) hSupportAtAnchor

end CayleySubgraphSpec
end ABO
end PSTSEPPA
