import PSTSEPPA.ABO.Lemma43CoatomMinimumCommonClusterCore
import PSTSEPPA.ABO.MultiCosetComponentSupportDichotomy
import PSTSEPPA.ABO.Lemma43ActualTranslatedLowerClusterSignedGraphIso

/-!
# ABO Lemma 4.3: the entire non-full-B branch is a genuine signed proper B-cluster

The published proof divides true B-components of the original
incomplete old+fresh coset extension into TWO alternatives:

* FULL B-COSET: some completed selected constituent E⊇B
  supports the component. The component is already the
  complete B-coset inside that tagged E-copy.
* PROPER B-CLUSTER: no such E⊇B supports the component.
  The lower-rank induction supplies an attained minimum
  ORIGINAL old-component-tagged support (M,m) of the
  ENTIRE component; its completed tagged constituents
  are lower B∩E-pieces with B∩E ⊊ B.

This module formalizes the SOURCE graph conclusion of the
SECOND case, without requiring M itself be a coatom and
without postulating a new common-core hypothesis.

The accepted minimum-support theorem yields ONE ACTUAL
quotient point core in every original component-tagged
coatom slice. For each selected coatom E meeting the
chosen true B-component, support invariance along ACTUAL
signed B-word paths implies that E CANNOT contain B:
otherwise its genuine E-support at the meeting point
would transport to the component anchor, contradicting
the explicit non-full-coset hypothesis.

Thus every B∩E is PROPER in B. The accepted source
translated lower B-cluster SIGNED EGraph theorem gives
an honest original oriented signed B-component graph
isomorphism with a translated proper B-cluster, on
BOTH vertices and oriented edge tokens.

This is a direct connection of the source's exact
Definition-3.22 whole-component minimum to the FINAL
cluster-shape clause of ABO Lemma 4.3, retaining all
original old skeleton component tags. The lower-rank
derivation of that minimum is a separate previously
certified induction step; the full-B-coset alternative
is addressed by another existing source lemma.

No unsupported ambient Cayley injection, imaginary
old signed edge, new axiom or sorry is introduced.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If NO selected alphabet E⊇B supports the anchor of
an original signed B-component, then every ACTIVE
original component-tagged coatom slice uses a lower
intersection alphabet B∩E ⊊ B.

This uses genuine support-invariance under realised
signed paths, not equality of ambient Γ coordinates. -/
theorem allProperCoset_no_full_B_component_all_active_pieces_proper
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoFull :
      ∀ (E : Finset ι)
        (hEP : E ∈ (allProperCosetFamily A).alphabets),
          B ⊆ E →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret E anchor) :
    ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
      B ∩ K.properCosetTagAlphabet t ⊂ B := by
  let P := allProperCosetFamily A
  intro t ht
  obtain ⟨_hCard, ⟨y, hySlice⟩⟩ :=
    (K.mem_activeTaggedCoatoms_iff
      hadm hgen hret B anchor t).mp ht
  obtain ⟨hyReach, pE, _hpTag, hyE⟩ := hySlice
  let E := K.properCosetTagAlphabet t
  let hEP : E ∈ P.alphabets := K.properCosetTagAlphabet_mem t
  have hBnotE : ¬ B ⊆ E := by
    intro hBE
    have hSuppY : K.MultiCosetVertexSupported
        P hadm hgen hret E y :=
      ⟨hEP, pE, hyE.symm⟩
    have hSuppAnchor : K.MultiCosetVertexSupported
        P hadm hgen hret E anchor :=
      (K.multiCoset_selected_superset_support_invariant
        P hadm hgen hret B E hBE anchor y hyReach).mpr hSuppY
    exact hNoFull E hEP hBE hSuppAnchor
  change B ∩ E ⊂ B
  refine ⟨Finset.inter_subset_left, ?_⟩
  intro hSub
  apply hBnotE
  intro i hi
  exact (Finset.mem_inter.mp (hSub hi)).2

/-- SOURCE Lemma 4.3 second branch, with the published
whole-component minimum as its only geometric induction
input. There is no coatom-minimum restriction:

IF the original signed B-component has one attained
minimal ORIGINAL tagged support and no full E⊇B
completed constituent supports its anchor, THEN
it is genuinely isomorphic on vertices and both
oriented signed edge tokens to a TRANSLATED PROPER
B-CLUSTER, with one ACTUAL common-core witness.

The distinct first branch, where some E⊇B supports
the anchor, is the full B-coset case and excluded. -/
theorem allProperCoset_no_full_B_component_signedClusterIso_of_minimum
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B M : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (m : K.ComponentIndex M)
    (hNoFull :
      ∀ (E : Finset ι)
        (hEP : E ∈ (allProperCosetFamily A).alphabets),
          B ⊆ E →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret E anchor)
    (hMinimum :
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
        M m) :
    ∃ (core : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret)
      (hProper :
        ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
          B ∩ K.properCosetTagAlphabet t ⊂ B),
      (∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows anchor w core) ∧
      (∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        core ∈ K.properCosetTagSlice hadm hgen hret B anchor t) ∧
      ∃ (T : EGraph
          {g : Γ // g ∈
            ClusterSpec.LeftTranslateSet
              (K.multiCosetAmbientValue
                (allProperCosetFamily A) hadm hgen hret core)
              ((K.activeTaggedLowerClusterSpec
                hadm hgen hret B anchor hProper).VertexSet gen)}
          {a : ActionEdge Γ ι // a ∈
            ClusterSpec.LeftTranslateEdgeSet
              (K.multiCosetAmbientValue
                (allProperCosetFamily A) hadm hgen hret core)
              ((K.activeTaggedLowerClusterSpec
                hadm hgen hret B anchor hProper).EdgeSet gen)} ι)
        (f : LabelledGraphHom
          ((K.multiCosetEGraph
            (allProperCosetFamily A) hadm hgen hret).BComponentEGraph
              B anchor).toLabelledGraph
          T.toLabelledGraph),
        Function.Bijective f.onVertex ∧
        Function.Bijective f.onEdge := by
  obtain ⟨core, hReach, _hSupport, hAll⟩ :=
    K.allProperCoset_minimum_attainer_in_all_active_coatoms
      hadm hgen hret B M anchor m hMinimum
  have hProper :=
    K.allProperCoset_no_full_B_component_all_active_pieces_proper
      hadm hgen hret B anchor hNoFull
  refine ⟨core, hProper, hReach, hAll, ?_⟩
  exact K.allProperCoset_B_component_translatedLowerCluster_signedGraphIso
    hadm hgen hret hcard B anchor core hAll hProper

end CayleySubgraphSpec
end ABO
