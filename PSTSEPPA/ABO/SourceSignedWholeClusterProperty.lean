import PSTSEPPA.ABO.OffFullBCosetMinimalSupport
import PSTSEPPA.ABO.Lemma43CoatomMinimumCommonClusterCore

/-!
# EXACT ABO Definition 3.22 (signed whole-component cluster property)

Definition 3.22 quantifies over B-components that AVOID the original
old skeleton. In BOTH alternatives -- full B-coset OR proper
B-cluster -- it requires an attained ORIGINAL component-tagged
minimum support for the ENTIRE B-component; in the cluster case
the minimum must be attained at some genuine core vertex.

The previous source Lemma 4.3 signed dichotomy proved the signed
graph-shape alternatives, and a whole-component minimum in the
no-full-constituent branch. OffFullBCosetMinimalSupport now
supplies the missing attained minimum for off-skeleton FULL
B-cosets, using genuine signed old-component paths and source
one-coatom induction. The accepted Lemma43CoatomMinimumCommonClusterCore
promotes the minimum's attainer to a real common tagged core point.

The predicate and theorem below encode all these clauses at once,
rather than an overstrong all-component minimum or a weaker
proper-branch-only one. The lower induction minima are requested
only for actual off-skeleton D-components, exactly as permitted
by the published source. No new axioms, sorry, fictitious old
edges, or ambient-coordinate tag identification.

The result is conditional on lower bridgefreeness/minima; the
induction of Theorem 4.5 removing lower cluster hypotheses
and the upward induction of Theorem 4.7 are separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Source Definition 3.22, including actual signed graph shape,
a single attained ORIGINAL tagged minimum of the WHOLE off-skeleton
B-component, and an ATTAINING common tagged core point.

The condition applies ONLY to B-components not meeting the old
skeleton, whether they are full B-cosets or proper B-clusters. -/
def HasExactSignedWholeComponentClusterProperty
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) : Prop :=
  ∀ (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret),
    (¬ ∃ (x : K.Vertex) (w : LabelWord ι),
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            B hBP).onVertex x)
          w anchor) →
    ∃ (M : Finset ι) (m : K.ComponentIndex M),
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
        M m ∧
      (K.HasFullSignedBCosetAlternative hadm hgen hret B anchor ∨
       K.HasProperSignedBClusterAlternative hadm hgen hret B anchor) ∧
      ∃ core : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w core) ∧
        K.HasTaggedSupportAt (allProperCosetFamily A)
          hadm hgen hret M m core ∧
        ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
          core ∈ K.properCosetTagSlice
            hadm hgen hret B anchor t

/-- Source EXACT signed Definition-3.22 cluster property, higher
rank, from the published lower bridge-free/cluster hypotheses
with minima ONLY requested for lower OFF-SKELETON D-components.

In both off-skeleton branches the minimum is ATTAINED on the
original entire B-component and the attainer is a genuine core
vertex in all active coatom slices. -/
theorem hasExactSignedWholeComponentClusterProperty_of_offSkeletonLower
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (hUniform : K.HasUniformOffSkeletonLowerComponentInput
      hadm hgen hret) :
    K.HasExactSignedWholeComponentClusterProperty
      hadm hgen hret := by
  classical
  let P := allProperCosetFamily A
  intro B hBP anchor hOff
  have hShape :
      K.HasFullSignedBCosetAlternative hadm hgen hret B anchor ∨
      K.HasProperSignedBClusterAlternative hadm hgen hret B anchor :=
    K.allProperCoset_uniform_forward_signed_dichotomy_of_off_skeleton_lower
      hadm hgen hret hAcard hUniform B hBP anchor
  have hMinimum :
      ∃ (M : Finset ι) (m : K.ComponentIndex M),
        K.IsMinimalTaggedSupportFor P hadm hgen hret
          {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
            (K.multiCosetEGraph P hadm hgen hret).Follows anchor w y}
          M m := by
    by_cases hFull :
        ∃ (C : Finset ι) (hCP : C ∈ P.alphabets),
          B ⊆ C ∧
          K.MultiCosetVertexSupported P hadm hgen hret C anchor
    · exact K.offSkeleton_full_B_component_has_minimum
        hadm hgen hret B hBP anchor hUniform hOff hFull
    · have hNoFull :
          ∀ (C : Finset ι) (hCP : C ∈ P.alphabets),
            B ⊆ C →
            ¬ K.MultiCosetVertexSupported
              P hadm hgen hret C anchor := by
        intro C hCP hBC hSupp
        exact hFull ⟨C, hCP, hBC, hSupp⟩
      obtain ⟨M, m, hMin, _hProper⟩ :=
        K.allProperCoset_uniform_forward_noFull_minimum_and_signed_cluster_off_skeleton
          hadm hgen hret hAcard hUniform B hBP anchor hNoFull
      exact ⟨M, m, hMin⟩
  obtain ⟨M, m, hMin⟩ := hMinimum
  obtain ⟨core, hReach, hTagged, hCommon⟩ :=
    K.allProperCoset_minimum_attainer_in_all_active_coatoms
      hadm hgen hret B M anchor m hMin
  exact ⟨M, m, hMin, hShape, core, hReach, hTagged, hCommon⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
