import PSTSEPPA.ABO.OriginalTaggedActiveCoatomCanonicalCosets
import PSTSEPPA.ABO.CanonicalSignedTranslatedProperClusterNaturality

/-!
# Original H forward 4.5: TWO genuine active tagged C-coatoms produce the proper-cluster bridge geometry

The conditional source-upward proper B-cluster n≥2 bridge
requires a true signed canonical original H B-component
isomorphism f, two actual constituent pieces B∩C₁ and
B∩C₂, original old H endpoints s₁,s₂ in those two
constituent cosets, and ONE true original common old H
core belonging to both corresponding cosets.

None of those constituent properties should be freely
assumed when the original forward Theorem4.5 has already
selected exact active OLD component-tagged C-coatoms
and a genuine common original tagged core.

We use the strengthened canonical signed graph isomorphism
that PRESERVES the exact ORIGINAL H multiCE ambient group
value of every original component-tagged B-vertex and both
signed directed edge tokens. The genuine source signed
B∩C paths in each active coatom slice from the ORIGINAL
common core then prove precise canonical translated
H[B∩C_i] membership of the two selected old H endpoints
AND the same true core; the lower B-cluster pieces
B∩C_i are literally selected by the original finite
active coatom image.

This returns one ACTUAL signed canonical proper B-cluster
iso with vertex/edge bijectivity and the full TWO active
constituent geometry required by the constructed source
upward bridge. It does NOT rely on a global original H
coset extension ambient injection or identify unrelated
old component-tagged vertices by their group coordinates.

The remaining source inputs are matching these two
original H tagged coset endpoints with the corresponding
two source G tagged completed coset anchors and the finite
stage labelled transition quotient from G into the
constructed nonisolated H B-augmentation.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Actual TWO selected original active H coatom
constituents give the complete signed proper B-cluster
piece-membership and old signed anchor/common-core
B∩C-coset geometry.

The extracted graph map is EXACTLY the ORIGINAL signed
multiCE ambient projection restricted to the true
B-component, not an arbitrary signed graph isomorphism
with incompatible G→H anchor group coordinates. -/
theorem allProperCoset_originalTwoTaggedCoatoms_canonicalSignedGeometry
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
        B ∩ K.properCosetTagAlphabet t ⊂ B)
    (t₁ t₂ : K.ProperCosetTag)
    (ht₁ : t₁ ∈ K.activeTaggedCoatoms hadm hgen hret B anchor)
    (ht₂ : t₂ ∈ K.activeTaggedCoatoms hadm hgen hret B anchor)
    (s₁ s₂ : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hs₁ : s₁ ∈ K.properCosetTagSlice hadm hgen hret B anchor t₁)
    (hs₂ : s₂ ∈ K.properCosetTagSlice hadm hgen hret B anchor t₂) :
    ∃ f : LabelledGraphHom
      (((K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).BComponentEGraph B anchor).toLabelledGraph)
      (((K.activeTaggedLowerClusterSpec
        hadm hgen hret B anchor hProper).rootTranslatedCayleySubgraph
          gen (K.multiCosetAmbientValue
            (allProperCosetFamily A) hadm hgen hret core)).toEGraph.toLabelledGraph),
      Function.Bijective f.onVertex ∧
      Function.Bijective f.onEdge ∧
      B ∩ K.properCosetTagAlphabet t₁ ∈
        (K.activeTaggedLowerClusterSpec
          hadm hgen hret B anchor hProper).pieces ∧
      B ∩ K.properCosetTagAlphabet t₂ ∈
        (K.activeTaggedLowerClusterSpec
          hadm hgen hret B anchor hProper).pieces ∧
      (f.onVertex ⟨s₁, hs₁.1⟩).1 ∈
        generatedLeftCoset gen (B ∩ K.properCosetTagAlphabet t₁)
          (K.multiCosetAmbientValue
            (allProperCosetFamily A) hadm hgen hret core) ∧
      (f.onVertex ⟨s₂, hs₂.1⟩).1 ∈
        generatedLeftCoset gen (B ∩ K.properCosetTagAlphabet t₂)
          (K.multiCosetAmbientValue
            (allProperCosetFamily A) hadm hgen hret core) ∧
      (f.onVertex ⟨core, (hAll t₁ ht₁).1⟩).1 ∈
        generatedLeftCoset gen (B ∩ K.properCosetTagAlphabet t₁)
          (K.multiCosetAmbientValue
            (allProperCosetFamily A) hadm hgen hret core) ∧
      (f.onVertex ⟨core, (hAll t₂ ht₂).1⟩).1 ∈
        generatedLeftCoset gen (B ∩ K.properCosetTagAlphabet t₂)
          (K.multiCosetAmbientValue
            (allProperCosetFamily A) hadm hgen hret core) := by
  obtain ⟨f, hv, he, hNat, _hEdgeNat⟩ :=
    K.allProperCoset_B_component_canonicalTranslatedCluster_signedIso_with_exact_ambient_value
      hadm hgen hret hcard B anchor core hAll hProper
  refine ⟨f, hv, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact K.activeTaggedLowerCluster_actual_piece_of_active_tag
      hadm hgen hret B anchor hProper t₁ ht₁
  · exact K.activeTaggedLowerCluster_actual_piece_of_active_tag
      hadm hgen hret B anchor hProper t₂ ht₂
  · rw [hNat ⟨s₁, hs₁.1⟩]
    exact K.activeTaggedSlice_original_ambient_B_inter_C_coset
      hadm hgen hret B anchor core hAll t₁ ht₁ s₁ hs₁
  · rw [hNat ⟨s₂, hs₂.1⟩]
    exact K.activeTaggedSlice_original_ambient_B_inter_C_coset
      hadm hgen hret B anchor core hAll t₂ ht₂ s₂ hs₂
  · rw [hNat ⟨core, (hAll t₁ ht₁).1⟩]
    exact K.activeTaggedSlice_original_ambient_B_inter_C_coset
      hadm hgen hret B anchor core hAll t₁ ht₁ core (hAll t₁ ht₁)
  · rw [hNat ⟨core, (hAll t₂ ht₂).1⟩]
    exact K.activeTaggedSlice_original_ambient_B_inter_C_coset
      hadm hgen hret B anchor core hAll t₂ ht₂ core (hAll t₂ ht₂)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
