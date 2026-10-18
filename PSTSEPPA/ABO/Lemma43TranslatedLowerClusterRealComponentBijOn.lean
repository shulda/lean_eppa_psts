import PSTSEPPA.ABO.Lemma43TrueComponentVertexSignedEdgeBijections
import PSTSEPPA.ABO.Lemma43TranslatedLowerClusterGraphSets

/-!
# ABO Lemma 4.3: bijections onto the actual translated lower-cluster graph

The accepted source results establish both facts needed for the
published signed graph isomorphism conclusion:

1. A genuine original B-component of the incomplete old+fresh
   multi-coset extension has a vertex map and a formally oriented
   signed-edge map bijective onto their true images in the ambient
   Cayley graph, when a true original quotient core belongs to every
   selected component-tagged coatom slice.
2. These two actual graph images are precisely the vertex and
   signed-edge sets of the left translate of the finite lower
   B-cluster, whose pieces B∩C are properly contained in B.

This file combines the two with direct Set.BijOn certificates
ONTO the explicit translated-cluster vertices and signed edges.

The morphism equations (source, reversal, signed label)
are certified by the original multiCosetAmbientHom. The final
target graph type and its labelled graph equivalence are a
separate graph-transport/API construction.

Original component tags stay genuine, inverse signed edge tokens
stay distinct, and no global ambient embedding or fake old edges
are asserted.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Genuine original B-component vertex and oriented signed-edge
bijections ONTO the left translate of the finite proper B-cluster
with constituent pieces B∩C. -/
theorem allProperCoset_B_component_translated_lower_cluster_bijOn
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι)
    (anchor core : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        core ∈ K.properCosetTagSlice hadm hgen hret B anchor t)
    (hProper :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B) :
    Set.BijOn
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret)
      {y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret |
        ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
      (ClusterSpec.LeftTranslateSet
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret core)
        ((K.activeTaggedLowerClusterSpec
          hadm hgen hret B anchor hProper).VertexSet gen)) ∧
    Set.BijOn
      (K.multiCosetEdgeQuotientAmbient
        (allProperCosetFamily A) hadm hgen hret)
      {e : K.MultiCosetEdgeVertexIncidenceQuotient
          (allProperCosetFamily A) hadm hgen hret |
        signedBase ((K.multiCosetEGraph
          (allProperCosetFamily A) hadm hgen hret).label e) ∈ B ∧
        ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w
              ((K.multiCosetEGraph
                (allProperCosetFamily A) hadm hgen hret).source e)}
      (ClusterSpec.LeftTranslateEdgeSet
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret core)
        ((K.activeTaggedLowerClusterSpec
          hadm hgen hret B anchor hProper).EdgeSet gen)) := by
  obtain ⟨hV, hE⟩ :=
    K.allProperCoset_B_component_vertex_and_signed_edge_images_eq_lower_cluster
      hadm hgen hret hcard B anchor core hAll hProper
  constructor
  · rw [← hV]
    exact K.allProperCoset_B_component_ambient_vertex_bijOn
      hadm hgen hret B anchor core hAll
  · rw [← hE]
    exact K.allProperCoset_B_component_ambient_signed_edge_bijOn
      hadm hgen hret hcard B anchor core hAll

end CayleySubgraphSpec
end ABO
end PSTSEPPA
