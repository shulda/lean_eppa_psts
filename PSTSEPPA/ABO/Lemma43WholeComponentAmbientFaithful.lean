import PSTSEPPA.ABO.Lemma43CommonAnchorFaithfulCosetGluing
import PSTSEPPA.ABO.Lemma43CommonOriginalSkeletonAnchor
import PSTSEPPA.ABO.Lemma43FiniteActiveCoatomCover

/-!
# ABO Lemma 4.3: the ambient Cayley map is faithful on ONE common-anchor component

The original incomplete coset-extension's ambient group-coordinate
projection is NOT globally injective: distinct intrinsic old
component tags can share an ambient coset. The published Lemma 4.3
nevertheless identifies each individual B-cluster as a translated
union of full subalphabet Cayley cosets AFTER proving its
coatom constituents share ONE ORIGINAL skeleton anchor.

The independently checked common-old-skeleton-anchor theorem
supplies an original skeleton point x such that every ACTIVE
component-tagged coatom constituent of a chosen signed
B-component Q has C-component index componentClass C x.
The immediately preceding faithful-gluing lemma then
proves equal ambient values within the union of these
constituents identify the very SAME ORIGINAL glued
quotient point. We promote that fact to an injection on
the ENTIRE TRUE B-component Q.

This is NOT false global ambient injectivity, an untagged
coset argument, or yet a complete labelled-graph isomorphism
to the source B-cluster. It is the exact *vertex
faithfulness* part of the missing source Corollary-3.12
cluster representation, while retaining actual oriented
signed original edges and all original old-component tags.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- General original gluing criterion: on ANY set S of actual
old/fresh multi-coset quotient points which all admit selected
constituent presentations based at the SAME ORIGINAL skeleton
vertex x, the canonical ambient group-coordinate map is
injective.

Unlike global coset-cover embedding, different original
component tags are never collapsed: common x is explicit. -/
theorem multiCosetAmbientValue_injOn_of_common_old_anchor
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (x : K.Vertex)
    (S : Set (K.MultiCosetVertex P hadm hgen hret))
    (hPresent :
      ∀ z ∈ S,
        ∃ (C : Finset ι) (hCP : C ∈ P.alphabets)
          (p : K.AttachedCosetVertex C),
          p.1 = K.componentClass C x ∧
          K.multiCosetInclude P hadm hgen hret C hCP p = z) :
    Set.InjOn (K.multiCosetAmbientValue P hadm hgen hret) S := by
  intro u hu v hv huv
  obtain ⟨C, hCP, p, hpIdx, hpU⟩ := hPresent u hu
  obtain ⟨D, hDP, q, hqIdx, hqV⟩ := hPresent v hv
  have hUValue :
      K.multiCosetAmbientValue P hadm hgen hret u = p.2.1 := by
    rw [← hpU]
    rfl
  have hVValue :
      K.multiCosetAmbientValue P hadm hgen hret v = q.2.1 := by
    rw [← hqV]
    rfl
  have hpq : p.2.1 = q.2.1 := by
    calc
      p.2.1 = K.multiCosetAmbientValue P hadm hgen hret u :=
        hUValue.symm
      _ = K.multiCosetAmbientValue P hadm hgen hret v := huv
      _ = q.2.1 := hVValue
  calc
    u = K.multiCosetInclude P hadm hgen hret C hCP p := hpU.symm
    _ = K.multiCosetInclude P hadm hgen hret D hDP q :=
      K.multiCosetInclude_eq_of_same_old_anchor_and_ambient_value
        P hadm hgen hret C D hCP hDP x p q hpIdx hqIdx hpq
    _ = v := hqV

/-- SOURCE Lemma 4.3 whole-B-component VERTEX FAITHFULNESS.

For finite Γ let I be the actual finite original-component-tagged
coatom family meeting the true signed B-component Q based at
anchor. Suppose ONE original quotient vertex z lies in EVERY
selected coatom slice -- this is exactly the source's
finite connected common-core conclusion, already independently
formalized in Lemma43FiniteCoatomWholeComponentMinimum.

Then the AMBIENT GROUP COORDINATE map is injective on
the ENTIRE component Q, not just on one selected coset:
every Q vertex lies in an active constituent, all
active original C-component tags come from ONE original
skeleton anchor x, and the original gluing is faithful
among such common-anchor tagged representatives.

This is a crucial vertex half of the source's final
identification of Q with a translated B-cluster. -/
theorem allProperCoset_B_component_ambient_injOn_of_common_core
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor z : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        z ∈ K.properCosetTagSlice hadm hgen hret B anchor t) :
    Set.InjOn
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret)
      { y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows anchor w y } := by
  let P := allProperCosetFamily A
  let I := K.activeTaggedCoatoms hadm hgen hret B anchor
  obtain ⟨M, hMP, x, w, hwM, hPath, hTags⟩ :=
    K.allProperCoset_common_point_one_original_skeleton_anchor
      hadm hgen hret B anchor z I hAll
  apply K.multiCosetAmbientValue_injOn_of_common_old_anchor
    P hadm hgen hret x
  intro y hy
  obtain ⟨t, ht, htSlice⟩ :=
    K.activeTaggedCoatoms_vertex_cover
      hadm hgen hret B anchor y hy
  let C := K.properCosetTagAlphabet t
  let hCP := K.properCosetTagAlphabet_mem t
  obtain ⟨_hReach, p, hpTag, hpY⟩ := htSlice
  refine ⟨C, hCP, p, ?_, hpY.symm⟩
  calc
    p.1 = K.properCosetTagIndex t := hpTag
    _ = K.componentClass C x := (hTags t ht).2.symm

end CayleySubgraphSpec
end ABO
end PSTSEPPA
