import PSTSEPPA.ABO.Lemma43ClusterVertexImage
import PSTSEPPA.ABO.ClusterComponents
import PSTSEPPA.ABO.Lemma43NonContainedCoatomRankDrop

/-!
# ABO Lemma 4.3: the true component's ambient image is a translated B-cluster

The preceding source vertex-image theorem identifies one genuine
old+fresh component-tagged B-component Q's ambient vertex set
with the translated union of lower B∩C subalphabet cosets
around one common quotient core z.

The published Lemma 4.3/Corollary 3.12 describes that union as
a true B-cluster, not merely an arbitrary set of cosets.
For this, the source's non-full-B-coset branch requires each
active B∩C to be a PROPER subalphabet of B. The accepted
real-path rank drop of the multi-constituent case supplies
exactly that hypothesis, and no additional group condition.

This module packages the finite active ORIGINAL component-tagged
coatom family as an actual `ClusterSpec B` whose constituent
alphabets are the B∩C, and proves the exact set-theoretic
equality:

 ambient(Q) = LeftTranslateSet ambient(z) (ClusterSpec.VertexSet).

This is an equality of actual SOURCE vertex image with
the translated vertex universe of a genuine finite B-cluster
in the PUBLISHED sense, preserving the original component
tag bookkeeping through the previous vertex-image theorem.

We do not yet claim a full labelled-graph isomorphism:
injectivity of the ambient map restricted to Q is proved in
separate source #743, while the exact projected ORIGINAL signed
edge image is being formalized in #745.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Genuine finite lower-cluster specification associated with
the active ORIGINAL coatom constituent tags of ONE
signed B-component, whenever the source has established
the strict rank-drop B∩C⊊B for every active tag.

No two old tags are first collapsed by ambient coordinates:
the finite image into alphabet sets happens ONLY when
forming the resulting lower cluster specification. -/
noncomputable def activeLowerClusterSpec
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
  pieces := (K.activeTaggedCoatoms hadm hgen hret B anchor).image
    (fun t => B ∩ K.properCosetTagAlphabet t)
  proper := by
    classical
    intro D hD
    rcases Finset.mem_image.mp hD with ⟨t, ht, rfl⟩
    exact hProper t ht

/-- Exact VERTEX-SET B-cluster identity for the TRUE
original signed component Q, once a common core z and
the source strict rank-drop premise are available.

The right side is the translated vertex set of the
actual finite `ClusterSpec B`, NOT just a union of
unverified ambient coset coordinates. The proof
uses the already certified original signed path
and tagged-coatom vertex-cover image theorem. -/
theorem allProperCoset_B_component_ambient_image_eq_translated_lower_cluster
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor z : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        z ∈ K.properCosetTagSlice hadm hgen hret B anchor t)
    (hProper :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B) :
    { g : Γ |
      ∃ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) ∧
        K.multiCosetAmbientValue
          (allProperCosetFamily A) hadm hgen hret y = g } =
    ClusterSpec.LeftTranslateSet
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret z)
      ((K.activeLowerClusterSpec hadm hgen hret B anchor hProper).VertexSet gen) := by
  classical
  let P := allProperCosetFamily A
  let I := K.activeTaggedCoatoms hadm hgen hret B anchor
  let g0 := K.multiCosetAmbientValue P hadm hgen hret z
  let F := K.activeLowerClusterSpec hadm hgen hret B anchor hProper
  have hImage :=
    K.allProperCoset_B_component_ambient_image_eq_active_lower_cosets
      hadm hgen hret B anchor z hAll
  rw [hImage]
  ext g
  change
    (∃ t ∈ I, g ∈ generatedLeftCoset gen
        (B ∩ K.properCosetTagAlphabet t) g0) ↔
      g0⁻¹ * g ∈ F.VertexSet gen
  constructor
  · rintro ⟨t, ht, hg⟩
    change ∃ D ∈ F.pieces,
      g0⁻¹ * g ∈ generatedSubgroup gen D
    refine ⟨B ∩ K.properCosetTagAlphabet t, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    · exact hg
  · intro hg
    change ∃ D ∈ F.pieces,
      g0⁻¹ * g ∈ generatedSubgroup gen D at hg
    obtain ⟨D, hD, hgD⟩ := hg
    obtain ⟨t, ht, hDt⟩ := Finset.mem_image.mp hD
    subst D
    exact ⟨t, ht, hgD⟩

end CayleySubgraphSpec
end ABO
