import PSTSEPPA.ABO.ForwardInductionUniformOffSkeletonLower

/-!
# ABO Definition 3.22 / Lemma 4.3: EXACT whole signed cluster property

The source property is NOT merely a dichotomy between two graph shapes,
nor an unconditional minimum-support assertion on complete B-cosets.

For each genuine B⊊A component of the ACTUAL original signed
component-tagged full proper-coset extension, exactly the source
alternatives are:
* a FULL B-coset supported in one original tagged completed C-copy,
  with every REAL signed B-edge and positive/inverse B-step; OR
* an ATTAINED minimum ORIGINAL old-component-tagged support for the
  ENTIRE B-component, AND an honest labelled EGraph isomorphism onto
  one translated PROPER B-cluster, including both oriented signed
  edge tokens.

This module combines the separately verified source lemmas without
losing the whole-component minimum in the proper branch.  The induction
input is ONLY lower bridgefreeness and lower off-skeleton component
minima on strictly smaller local alphabets D=B∩C⊊C, as the printed
Definition 3.22 allows, NOT minima on arbitrary skeleton-meeting
full lower D-cosets.

This is a conditional higher-rank forward theorem, not the
unconditional assertion that all source stages satisfy its
hypotheses.  Exact source stage history, upward Theorem 4.7,
reflecting groups and PSTS EPPA still require separate proofs.
No global ambient coordinate identifications, new axioms or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Precisely the FULL-vs-PROPER signed whole-component cluster property
of ABO Definition 3.22, including the ACTUAL attained tagged minimum
only in the proper branch, not for a skeleton-meeting full B-coset.

The group Γ must be finite here to construct the literal finite signed
proper B-cluster; it remains a separate hypothesis on this generic
global-retractability model, later localized to the actual H[A]. -/
def HasSignedWholeComponentClusterProperty
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) : Prop :=
  ∀ (B : Finset ι)
    (_hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret),
    K.HasFullSignedBCosetAlternative hadm hgen hret B anchor ∨
    ∃ (M : Finset ι) (m : K.ComponentIndex M),
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
        M m ∧
      K.HasProperSignedBClusterAlternative hadm hgen hret B anchor

/-- The source's complete SIGNED whole-component cluster property
follows from lower bridgefreeness plus genuinely off-skeleton
lower D-component tagged minima, uniformly for every B⊊A.

This is the exact source-facing Lemma 4.3 induction result,
rather than the older overstrong uniform lower-minima condition. -/
theorem hasSignedWholeComponentClusterProperty_of_offSkeletonLower
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (hUniform : K.HasUniformOffSkeletonLowerComponentInput
      hadm hgen hret) :
    K.HasSignedWholeComponentClusterProperty hadm hgen hret := by
  classical
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  intro B hBP anchor
  by_cases hFull :
      ∃ (C : Finset ι) (hCP : C ∈ P.alphabets),
        B ⊆ C ∧
        K.MultiCosetVertexSupported P hadm hgen hret C anchor
  · left
    obtain ⟨C, hCP, hBC, ⟨_hC, p, hp⟩⟩ := hFull
    refine ⟨C, hCP, hBC, p, hp, ?_, ?_⟩
    · intro e he
      have he' :
          e ∈ G.BComponentEdgeSet B
            (K.multiCosetInclude P hadm hgen hret C hCP p) := by
        simpa only [hp] using he
      exact K.multiCoset_full_B_component_all_signed_edges_in_C
        P hadm hgen hret C hCP B hBC p e he'
    · intro y hy s hs
      have hy' :
          y ∈ G.BComponentVertexSet B
            (K.multiCosetInclude P hadm hgen hret C hCP p) := by
        simpa only [hp] using hy
      obtain ⟨e, he, heSource, heLabel⟩ :=
        K.multiCoset_full_B_component_all_signed_steps_exist
          P hadm hgen hret C hCP B hBC p y hy' s hs
      refine ⟨e, ?_, heSource, heLabel⟩
      simpa only [hp] using he
  · right
    have hNoFull :
        ∀ (C : Finset ι) (hCP : C ∈ P.alphabets),
          B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            P hadm hgen hret C anchor := by
      intro C hCP hBC hSupported
      exact hFull ⟨C, hCP, hBC, hSupported⟩
    obtain ⟨M, m, hMinimum, hCluster⟩ :=
      K.allProperCoset_uniform_forward_noFull_minimum_and_signed_cluster_off_skeleton
        hadm hgen hret hAcard hUniform B hBP anchor hNoFull
    exact ⟨M, m, hMinimum, hCluster⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
