import PSTSEPPA.ABO.Lemma43ClusterSignedEdgeImage
import PSTSEPPA.ABO.ClusterComponentGraph

/-!
# ABO Lemma 4.3: the genuine B-component images are a translated B-cluster

The preceding two independently verified source lemmas identify the
ambient VERTEX set and the actual ORIENTED SIGNED EDGE set of one
true component-tagged B-component of the original incomplete full
coset extension as the unions of genuine lower-alphabet cosets
and their completed signed edges.

If each active coatom alphabet C satisfies B∩C ⊊ B, those lower
alphabets form an actual finite `ClusterSpec B` in the sense of
ABO Definition 3.11. This module proves that the TWO exact
set-theoretic representations (vertices AND signed edges) are
literally left translates of the cluster's true graph sets.

This is the SOURCE graph-SHAPE assertion in published ABO I
Lemma 4.3 and Corollary 3.12, conditional on one real
quotient core z in ALL the active original tagged coatom copies
and on the explicit properness of their overlap alphabets.
Neither old edge tokens nor old skeleton component tags are
identified merely because their ambient coordinates coincide:
the previous source lemmas construct all set elements by
actual signed paths and original completed-coset edges.

The map's INJECTIVITY on the chosen actual component's
vertices and oriented edges is separately certified by
Lemma43WholeComponentAmbientFaithful and
Lemma43WholeComponentSignedEdgeFaithful. Combining these
with this source image identification will give the
corresponding bijective labelled graph representation.

This theorem is not a new global ambient embedding or
a claim that every proper-subalphabet coset extension has
the cluster property.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The actual finite lower-cluster alphabet family obtained
from the original-component-tagged active coatom constituents.
Original indices are retained in the indexing set even though
duplicate lower alphabets collapse in the resulting cluster
family (which is a graph union, not a tagged disjoint union). -/
noncomputable def activeTaggedLowerClusterSpec
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hProper :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B) :
    ClusterSpec B where
  pieces :=
    (K.activeTaggedCoatoms hadm hgen hret B anchor).image
      (fun t => B ∩ K.properCosetTagAlphabet t)
  proper := by
    classical
    intro D hD
    obtain ⟨t, ht, hDt⟩ := Finset.mem_image.mp hD
    subst D
    exact hProper t ht

/-- Membership in the translated lower cluster's TRUE vertex set
is exactly membership in one active translated B∩C coset,
with original C-component tags only used to select the family. -/
theorem activeTaggedLowerCluster_vertex_iff
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hProper :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B)
    (core g : Γ) :
    g ∈ ClusterSpec.LeftTranslateSet core
      ((K.activeTaggedLowerClusterSpec
        hadm hgen hret B anchor hProper).VertexSet gen) ↔
      ∃ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        g ∈ generatedLeftCoset gen
          (B ∩ K.properCosetTagAlphabet t) core := by
  classical
  change
    (∃ D ∈ (K.activeTaggedCoatoms hadm hgen hret B anchor).image
      (fun t => B ∩ K.properCosetTagAlphabet t),
      core⁻¹ * g ∈ generatedSubgroup gen D) ↔ _
  constructor
  · rintro ⟨D, hD, hg⟩
    obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp hD
    refine ⟨t, ht, ?_⟩
    simpa only [hEq] using hg
  · rintro ⟨t, ht, hg⟩
    exact ⟨B ∩ K.properCosetTagAlphabet t,
      Finset.mem_image.mpr ⟨t, ht, rfl⟩, hg⟩

/-- Membership in the translated lower cluster's TRUE signed
EDGE set is exactly a Cayley source inside one active B∩C
coset together with an actual signed label FROM B∩C. -/
theorem activeTaggedLowerCluster_edge_iff
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hProper :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B)
    (core : Γ) (a : ActionEdge Γ ι) :
    a ∈ ClusterSpec.LeftTranslateEdgeSet core
      ((K.activeTaggedLowerClusterSpec
        hadm hgen hret B anchor hProper).EdgeSet gen) ↔
      ∃ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        (cayleyGraph gen).source a ∈
          generatedLeftCoset gen
            (B ∩ K.properCosetTagAlphabet t) core ∧
        signedBase ((cayleyGraph gen).label a) ∈
          B ∩ K.properCosetTagAlphabet t := by
  classical
  rcases a with ⟨g, s⟩
  change
    (∃ D ∈ (K.activeTaggedCoatoms hadm hgen hret B anchor).image
      (fun t => B ∩ K.properCosetTagAlphabet t),
      core⁻¹ * g ∈ generatedSubgroup gen D ∧
        signedBase s ∈ D) ↔ _
  constructor
  · rintro ⟨D, hD, hg, hs⟩
    obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp hD
    refine ⟨t, ht, ?_, ?_⟩
    · simpa only [hEq] using hg
    · simpa only [hEq] using hs
  · rintro ⟨t, ht, hg, hs⟩
    exact ⟨B ∩ K.properCosetTagAlphabet t,
      Finset.mem_image.mpr ⟨t, ht, rfl⟩, hg, hs⟩

/-- Source Lemma 4.3 graph-shape conclusion, NOT JUST VERTICES:
the ambient image sets of every original true signed B-component
with one genuine common quotient core are LITERALLY the left
translates of a single true lower `ClusterSpec B` vertex and
ORIENTED SIGNED edge set.

The explicit hProper hypothesis is precisely the source's
non-full-B-coset alternative; it follows from the genuine
multi-constituent rank-drop lemma when applicable. -/
theorem allProperCoset_B_component_vertex_and_signed_edge_images_eq_lower_cluster
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
    {g : Γ |
      ∃ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) ∧
        K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret y = g} =
      ClusterSpec.LeftTranslateSet
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret core)
        ((K.activeTaggedLowerClusterSpec
          hadm hgen hret B anchor hProper).VertexSet gen) ∧
    {a : ActionEdge Γ ι |
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
          (allProperCosetFamily A) hadm hgen hret e = a} =
      ClusterSpec.LeftTranslateEdgeSet
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret core)
        ((K.activeTaggedLowerClusterSpec
          hadm hgen hret B anchor hProper).EdgeSet gen) := by
  constructor
  · rw [K.allProperCoset_B_component_ambient_image_eq_active_lower_cosets
      hadm hgen hret B anchor core hAll]
    ext g
    exact (K.activeTaggedLowerCluster_vertex_iff
      hadm hgen hret B anchor hProper
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret core) g).symm
  · rw [K.allProperCoset_B_component_ambient_signed_edge_image_eq_cluster
      hadm hgen hret hcard B anchor core hAll]
    ext a
    exact (K.activeTaggedLowerCluster_edge_iff
      hadm hgen hret B anchor hProper
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret core) a).symm

end CayleySubgraphSpec
end ABO
end PSTSEPPA
