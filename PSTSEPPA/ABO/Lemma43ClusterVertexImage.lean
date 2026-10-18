import PSTSEPPA.ABO.Lemma43CommonOriginalSkeletonAnchor
import PSTSEPPA.ABO.Lemma43FiniteActiveCoatomCover
import PSTSEPPA.ABO.ComponentSelectedSliceExact

/-!
# ABO Lemma 4.3 / Corollary 3.12: exact VERTEX IMAGE of one true B-component

A true original B-component Q of an incomplete component-tagged
coset extension is not automatically an ambient Cayley B-coset.
But once the source's finite connected coatom induction has
produced one actual common CORE vertex z belonging to every
selected tagged maximal constituent, the set of ambient
group-coordinate values attained by Q is an explicit
TRANSLATED UNION of FULL lower-alphabet cosets:

  ambient(Q) = ∪_{(C,c) active} ambient(z) G[B∩C].

This is the VERTEX-SET part of the published
ABO Lemma 4.3 cluster-shape identification, leading
to Corollary 3.12. It is proved using the exact source
subalphabet component equivalence and real signed
paths, NOT from guessed global ambient Cayley injectivity.

The companion same-OLD-anchor faithful-gluing lemma and
whole-Q coordinate injectivity are separately developed
in #740/#741. Combining these with the edge-image
correspondence will give the final labelled-cluster
isomorphism, but this module does not falsely claim that
full graph isomorphism has already been proved.

No new axioms, fictional old edges or untagged quotient
identifications occur. The common-core hypothesis is
explicit and is supplied by the existing certified
finite coatom common-core induction under the published
lower-rank cluster and bridge-free hypotheses.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact original component-tagged C-slice AMBIENT vertex
image. If z belongs to the genuine C-tagged slice of
one B-component Q, its ambient vertex set is exactly
the complete left (B∩C)-coset based at ambient(z).

This is a two-sided result: the backward implication
constructs an ACTUAL selected C-attachment with the
correct old-component tag and uses a REAL signed
B-labelled path in the original multiCE. -/
theorem allProperCoset_tagged_slice_ambient_range_iff
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (c : K.ComponentIndex C)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hz : z ∈ K.allProperCoset_taggedConstituentSlice
      hadm hgen hret B anchor C hCP c)
    (g : Γ) :
    (∃ y : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret,
      y ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c ∧
      K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret y = g) ↔
    g ∈ generatedLeftCoset gen (B ∩ C)
      (K.multiCosetAmbientValue
        (allProperCosetFamily A) hadm hgen hret z) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨⟨wz, hwz, hAz⟩, pZ, hpZtag, hzEq⟩ := hz
  have hMeet :
      ∃ u : LabelWord ι, LabelWord.Uses B u ∧
        G.Follows
          (K.multiCosetInclude P hadm hgen hret C hCP pZ)
          u anchor := by
    refine ⟨PSTS.SignedWord.inv wz, hwz.inv, ?_⟩
    rw [← hzEq]
    exact G.follows_inverse hAz
  have hZvalue :
      K.multiCosetAmbientValue P hadm hgen hret z = pZ.2.1 := by
    rw [hzEq]
    rfl
  constructor
  · rintro ⟨y, hy, hyValue⟩
    obtain ⟨⟨wy, hwy, hAy⟩, pY, hpYtag, hyEq⟩ := hy
    have hIndex : pZ.1 = pY.1 :=
      hpZtag.trans hpYtag.symm
    have hToY :
        ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          G.Follows anchor w
            (K.multiCosetInclude P hadm hgen hret C hCP pY) := by
      refine ⟨wy, hwy, ?_⟩
      rw [← hyEq]
      exact hAy
    have hSmall :=
      (K.multiCoset_B_component_selected_C_slice_exact
        P hadm hgen hret B C hCP pZ anchor hMeet pY hIndex).mp hToY
    have hPvalue : pY.2.1 = g := by
      have hVal :
          K.multiCosetAmbientValue P hadm hgen hret y = pY.2.1 := by
        rw [hyEq]
        rfl
      exact hVal.symm.trans hyValue
    rw [hZvalue]
    rw [← hPvalue]
    exact hSmall
  · intro hg
    have hSmall : g ∈ generatedLeftCoset gen (B ∩ C) pZ.2.1 := by
      simpa only [hZvalue] using hg
    have hBig : g ∈ generatedLeftCoset gen C pZ.2.1 :=
      generatedSubgroup_mono gen Finset.inter_subset_right hSmall
    have hCosetEq : K.componentAmbientCoset C pZ.1 =
        generatedLeftCoset gen C pZ.2.1 :=
      K.componentAmbientCoset_eq_generatedLeftCoset_of_member
        C pZ.1 pZ.2.1 pZ.2.2
    have hMember : g ∈ K.componentAmbientCoset C pZ.1 := by
      rw [hCosetEq]
      exact hBig
    let q : K.AttachedCosetVertex C := ⟨pZ.1, ⟨g, hMember⟩⟩
    have hQSmall : q.2.1 ∈ generatedLeftCoset gen (B ∩ C) pZ.2.1 :=
      hSmall
    obtain ⟨w, hw, hPath⟩ :=
      (K.multiCoset_B_component_selected_C_slice_exact
        P hadm hgen hret B C hCP pZ anchor hMeet q rfl).mpr hQSmall
    let y : K.MultiCosetVertex P hadm hgen hret :=
      K.multiCosetInclude P hadm hgen hret C hCP q
    refine ⟨y, ?_, ?_⟩
    · exact ⟨⟨w, hw, hPath⟩, q, hpZtag, rfl⟩
    · rfl

/-- SOURCE cluster-shape VERTEX IMAGE, for one true signed
B-component Q of the ORIGINAL full multiCE with finite Γ.

Given one actual common-core quotient vertex z in EVERY
original-component-tagged coatom slice meeting Q, the
ambient vertex values of the WHOLE Q are exactly the
translated union of complete lower subalphabet cosets
ambient(z) G[B∩C_t] over its finite active coatom family.

This is the source's set-theoretic cluster representation;
full faithful labelled graph geometry requires the
separately developed old-anchor coset gluing and
edge-level verification. -/
theorem allProperCoset_B_component_ambient_image_eq_active_lower_cosets
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        z ∈ K.properCosetTagSlice hadm hgen hret B anchor t) :
    { g : Γ |
      ∃ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) ∧
        K.multiCosetAmbientValue
          (allProperCosetFamily A) hadm hgen hret y = g } =
    { g : Γ |
      ∃ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        g ∈ generatedLeftCoset gen
          (B ∩ K.properCosetTagAlphabet t)
          (K.multiCosetAmbientValue
            (allProperCosetFamily A) hadm hgen hret z) } := by
  ext g
  constructor
  · rintro ⟨y, hy, hyValue⟩
    obtain ⟨t, ht, htSlice⟩ :=
      K.activeTaggedCoatoms_vertex_cover
        hadm hgen hret B anchor y hy
    have hCore : z ∈ K.properCosetTagSlice
        hadm hgen hret B anchor t := hAll t ht
    have hCoset :=
      (K.allProperCoset_tagged_slice_ambient_range_iff
        hadm hgen hret B anchor
        (K.properCosetTagAlphabet t)
        (K.properCosetTagAlphabet_mem t)
        (K.properCosetTagIndex t)
        z hCore g).mp ⟨y, htSlice, hyValue⟩
    exact ⟨t, ht, hCoset⟩
  · rintro ⟨t, ht, hCoset⟩
    have hCore : z ∈ K.properCosetTagSlice
        hadm hgen hret B anchor t := hAll t ht
    obtain ⟨y, hy, hyValue⟩ :=
      (K.allProperCoset_tagged_slice_ambient_range_iff
        hadm hgen hret B anchor
        (K.properCosetTagAlphabet t)
        (K.properCosetTagAlphabet_mem t)
        (K.properCosetTagIndex t)
        z hCore g).mpr hCoset
    exact ⟨y, hy.1, hyValue⟩

end CayleySubgraphSpec
end ABO
