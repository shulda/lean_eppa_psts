import PSTSEPPA.ABO.Lemma43CoatomMinimumCommonClusterCore
import PSTSEPPA.ABO.Lemma43ActualTranslatedLowerClusterSignedGraphIso

/-!
# ABO Lemma 4.3: maximal minimum support gives a true signed B-cluster isomorphism

The PUBLISHED proof of Lemma 4.3 distinguishes the special case
where a true B-component has an attained minimum support on one
maximal selected alphabet C. If B⊄C, it is a genuine proper
B-cluster, not the separately treated full-B-coset alternative.

The preceding source-certified minimum-support bridge constructs
one ACTUAL old+fresh quotient vertex core in every active
original component-tagged coatom constituent and proves the
intersection alphabet B∩E is PROPER in B for every such
coatom E. The already accepted SOURCE signed-graph theorem
`allProperCoset_B_component_translatedLowerCluster_signedGraphIso`
then constructs the precise signed B-component-to-cluster
isomorphism: both vertices AND original oriented signed edges
are in bijection with those of the translated proper B-cluster.

This module packages that implication as a convenient
SOURCE theorem whose mathematical hypothesis is the attained
original-component-tagged minimum (C,c), rather than the
previously exposed technical common-core/proper-family predicates.

Consequently the independently verified one-coatom/no-smaller-
support theorem immediately instantiates this result whenever
B⊄C. The other published case B⊆C is an actual FULL B-COSET
and is intentionally excluded from the proper-cluster conclusion.

No assertion of global multiCE ambient injectivity, no invented
missing old signed edge and no new axioms or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Published Lemma 4.3: an attained coatom minimum (C,c)
with B⊄C yields a true orientation-sensitive isomorphism
from the ORIGINAL signed B-component to one translated
proper B-cluster of the finite labelled group.

The output supplies its actual quotient core vertex,
the genuine source signed-word path to that core, the
complete component-tagged lower-cluster family, and an
actual labelled graph morphism bijective on BOTH vertices
and oriented signed edge tokens.

Only the source finite generated/retractable-group hypotheses
and the attained WHOLE B-component minimum are assumed;
all technical core-propagation and properness witnesses
are derived by the previous source lemma. -/
theorem allProperCoset_coatom_minimum_gives_true_signedClusterIso
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B C : Finset ι)
    (hCcard : C.card + 1 = A.card)
    (hBnotC : ¬ B ⊆ C)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (hMinimum :
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
        C c) :
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
      hadm hgen hret B C anchor c hMinimum
  have hProper :=
    K.allProperCoset_coatom_minimum_all_active_pieces_proper
      hadm hgen hret B C hCcard hBnotC
      anchor c hMinimum
  refine ⟨core, hProper, hReach, hAll, ?_⟩
  exact K.allProperCoset_B_component_translatedLowerCluster_signedGraphIso
    hadm hgen hret hcard B anchor core hAll hProper

end CayleySubgraphSpec
end ABO
end PSTSEPPA
