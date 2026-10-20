import PSTSEPPA.ABO.ForwardInductionUniformOffSkeletonLower
import PSTSEPPA.ABO.Lemma43OneCoatomMinimumOffSkeleton
import PSTSEPPA.ABO.CoatomConstituentCover

/-!
# ABO Definition 3.22: MINIMUM SUPPORT OF OFF-SKELETON FULL B-COSETS

An important source-facing correction: Definition 3.22(2)
requires an attained unique minimum original-component-tagged
support for EVERY B-component avoiding the old skeleton,
INCLUDING the alternative in which that component is a FULL B-COSET,
not only for proper B-clusters.

If an off-skeleton B-component is supported in a C-constituent
with B⊆C, extend that constituent to a genuine tagged coatom.
Because the B-component avoids the old skeleton, B must be
STRICTLY smaller than the coatom alphabet: a B-support itself
would give a REAL B-word path from a skeleton vertex.

Every real signed B-word path stays in that one coatom copy,
so the already formalized source one-coatom off-skeleton
minimum theorem applies, provided the source's uniform LOWER
bridgefreeness and off-skeleton tagged minimum hypotheses hold.

No ambient-coordinate quotienting of different tagged vertices
and no invented old signed edge is involved.  This closes the
remaining FULL-COSET minimum clause needed to formulate EXACTLY
the published Definition 3.22 at higher rank. The forward stage
and the reflecting group remain separate obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An off-skeleton full B-coset actually supported at B is
impossible: the selected completed B-constituent has a
genuine old skeleton vertex, with a REAL B-word path to
every point of its attached B-coset. -/
theorem offSkeleton_B_not_B_supported
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hOff :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
            ((K.skeletonToMultiCosetHom
              (allProperCosetFamily A) hadm hgen hret
              B hBP).onVertex x)
            w anchor) :
    ¬ K.MultiCosetVertexSupported
      (allProperCosetFamily A) hadm hgen hret B anchor := by
  intro hSupported
  obtain ⟨_hBP, p, hp⟩ := hSupported
  obtain ⟨x, hx⟩ := K.componentClass_surjective B p.1
  obtain ⟨w, hw, hPath⟩ :=
    K.singleCosetEGraph_connected_on_index
      B (K.attachedOfSkeletonVertex B x) p hx
  have hMapped := hPath.map
    (K.singleCosetToMultiHom
      (allProperCosetFamily A) hadm hgen hret B hBP)
  change
    (K.multiCosetEGraph (allProperCosetFamily A)
      hadm hgen hret).Follows
       ((K.skeletonToMultiCosetHom
         (allProperCosetFamily A) hadm hgen hret B hBP).onVertex x)
       w
       (K.multiCosetInclude (allProperCosetFamily A)
         hadm hgen hret B hBP p) at hMapped
  apply hOff
  refine ⟨x, w, hw, ?_⟩
  rwa [hp] at hMapped

/-- The exact MISSING full-B-coset minimum of the published
cluster property. Even when a FULL B-coset is disjoint from
the original skeleton, its ENTIRE original signed B-component
has an ATTAINED minimum (M,m) with the literal old component
index m. Lower minima are only requested for off-skeleton
lower components of strictly smaller parent rank. -/
theorem offSkeleton_full_B_component_has_minimum
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hUniform : K.HasUniformOffSkeletonLowerComponentInput hadm hgen hret)
    (hOff :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
            ((K.skeletonToMultiCosetHom
              (allProperCosetFamily A) hadm hgen hret
              B hBP).onVertex x)
            w anchor)
    (hFull :
      ∃ (D : Finset ι)
        (hDP : D ∈ (allProperCosetFamily A).alphabets),
        B ⊆ D ∧
        K.MultiCosetVertexSupported
          (allProperCosetFamily A) hadm hgen hret D anchor) :
    ∃ (M : Finset ι) (m : K.ComponentIndex M),
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y} M m := by
  classical
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨D, hDP, hBD, ⟨_hDP', pD, hpD⟩⟩ := hFull
  obtain ⟨C, hCP, hDC, hCcard, hCInc⟩ :=
    K.allProperCoset_constituent_extend_to_coatom
      hadm hgen hret D hDP pD
  let pC : K.AttachedCosetVertex C :=
    K.attachedSubalphabetMap D C hDC pD
  have hCAnchor :
      K.multiCosetInclude P hadm hgen hret C hCP pC = anchor :=
    hCInc.trans hpD
  have hBC : B ⊆ C := hBD.trans hDC
  have hBCstrict : B ⊂ C := by
    refine ⟨hBC, ?_⟩
    intro hCB
    have hEq : B = C := Finset.Subset.antisymm hBC hCB
    subst C
    have hSupportB : K.MultiCosetVertexSupported P
        hadm hgen hret B anchor :=
      ⟨hBP, pC, hCAnchor⟩
    exact (K.offSkeleton_B_not_B_supported
      hadm hgen hret B hBP anchor hOff) hSupportB
  have hDlocal : B ∩ C ⊂ C := by
    simpa only [Finset.inter_eq_left.mpr hBC] using hBCstrict
  have hContained :
      ∀ y : K.MultiCosetVertex P hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          G.Follows anchor w y) →
        ∃ q : K.AttachedCosetVertex C,
          q.1 = pC.1 ∧
          y = K.multiCosetInclude P hadm hgen hret C hCP q := by
    intro y hy
    obtain ⟨w, hw, hPath⟩ := hy
    have hp :
        ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          G.Follows
            (K.multiCosetInclude P hadm hgen hret C hCP pC) w y :=
      ⟨w, hw, by rw [hCAnchor]; exact hPath⟩
    obtain ⟨q, hqIndex, _hqCoset, hqy⟩ :=
      (K.multiCoset_selected_C_subalphabet_B_component_exact
        P hadm hgen hret C hCP B hBC pC y).mp hp
    exact ⟨q, hqIndex, hqy⟩
  exact
    K.allProperCoset_one_coatom_component_minimum_of_off_skeleton_lower_induction
      hadm hgen hret B C hCP hBP hCcard hDlocal
      anchor pC.1 hContained hOff
      (hUniform.1 C hCP)
      (fun root x₀ hoff =>
        hUniform.2 C hCP (B ∩ C) hDlocal root x₀ hoff)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
