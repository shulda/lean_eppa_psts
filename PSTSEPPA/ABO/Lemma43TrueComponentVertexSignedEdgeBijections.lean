import PSTSEPPA.ABO.Lemma43WholeComponentSignedEdgeFaithful
import PSTSEPPA.ABO.Lemma43ClusterSignedEdgeImage

/-!
# ABO Lemma 4.3: bijections of true B-component VERTICES and SIGNED EDGES

This is the source's final component-faithfulness synthesis before
constructing a labelled-graph isomorphism and applying Corollary 3.12.

For ONE real intrinsic signed B-component Q of the ORIGINAL incomplete
old+fresh tagged coset extension over a finite generated/retractable group,
the earlier common-core proof supplies one genuine quotient vertex z
belonging to all active original old-component-tagged coatom constituents.
Four independently certified source-facing theorems then establish:

* the ambient group-coordinate map is INJECTIVE on Q's original
  signed-path-reachable VERTICES, even though it can fail to be
  injective globally because different original old component
  tags have equal Cayley values;
* its vertex image is EXACTLY the union of the translated
  lower B∩C subalphabet cosets;
* the true ORIENTED SIGNED edge-token projection is INJECTIVE
  on precisely the original B-labelled edges whose source lies
  in Q, with formal inverses and original geometric loops kept;
* its signed edge image is EXACTLY the union of the translated
  lower B∩C full Cayley signed edge sets.

We combine these as two actual `Set.BijOn` theorems. The original
signed graph morphism was separately certified by the original
multiCE ambient map and preserves source, inverse and signed label.
Thus these two bijections are the concrete vertex/edge payload of
the published labelled-cluster graph isomorphism.

No actual old vertex/edge has been created or removed here, and
the underlying image equalities were proved using genuine
old-component-tagged quotient presentations and realised signed
paths. This is not a proof of global multiCE embedding or
unconditional cluster property.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Source vertex-set bijection of a true ORIGINAL B-component
onto the union of translated lower B∩C cosets, retaining the
original component tags on the domain side. -/
theorem allProperCoset_B_component_ambient_vertex_bijOn
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor core : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        core ∈ K.properCosetTagSlice hadm hgen hret B anchor t) :
    Set.BijOn
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret)
      {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows anchor w y}
      {g : Γ |
        ∃ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
          g ∈ generatedLeftCoset gen
            (B ∩ K.properCosetTagAlphabet t)
            (K.multiCosetAmbientValue (allProperCosetFamily A)
              hadm hgen hret core)} := by
  let P := allProperCosetFamily A
  let F := K.multiCosetAmbientValue P hadm hgen hret
  have hImage :=
    K.allProperCoset_B_component_ambient_image_eq_active_lower_cosets
      hadm hgen hret B anchor core hAll
  have hInj :=
    K.allProperCoset_B_component_ambient_injOn_of_common_core
      hadm hgen hret B anchor core hAll
  constructor
  · intro x hx
    have hMember : F x ∈
        {g : Γ | ∃ y : K.MultiCosetVertex P hadm hgen hret,
          (∃ w : LabelWord ι, LabelWord.Uses B w ∧
            (K.multiCosetEGraph P hadm hgen hret).Follows anchor w y) ∧
            F y = g} := ⟨x, hx, rfl⟩
    rw [hImage] at hMember
    exact hMember
  constructor
  · exact hInj
  · intro g hg
    rw [← hImage] at hg
    obtain ⟨x, hx, hEq⟩ := hg
    exact ⟨x, hx, hEq⟩

/-- Source signed-edge-token bijection of a true ORIGINAL
B-component onto its exact translated lower-coatom cluster
oriented SIGNED edges, not just the corresponding undirected
edges and not the artificial later trivial completion loops. -/
theorem allProperCoset_B_component_ambient_signed_edge_bijOn
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι)
    (anchor core : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        core ∈ K.properCosetTagSlice hadm hgen hret B anchor t) :
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
      {a : ActionEdge Γ ι |
        ∃ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
          (cayleyGraph gen).source a ∈
            generatedLeftCoset gen
              (B ∩ K.properCosetTagAlphabet t)
              (K.multiCosetAmbientValue
                (allProperCosetFamily A) hadm hgen hret core) ∧
          signedBase ((cayleyGraph gen).label a) ∈
            B ∩ K.properCosetTagAlphabet t} := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let F := K.multiCosetEdgeQuotientAmbient P hadm hgen hret
  have hImage :=
    K.allProperCoset_B_component_ambient_signed_edge_image_eq_cluster
      hadm hgen hret hcard B anchor core hAll
  have hInj :=
    K.allProperCoset_B_component_ambient_signed_edge_injOn_of_common_core
      hadm hgen hret B anchor core hAll
  constructor
  · intro e he
    have hMember : F e ∈
        {a : ActionEdge Γ ι |
          ∃ d : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret,
            (signedBase (G.label d) ∈ B ∧
              ∃ w : LabelWord ι, LabelWord.Uses B w ∧
                G.Follows anchor w (G.source d)) ∧
            F d = a} := ⟨e, he, rfl⟩
    rw [hImage] at hMember
    exact hMember
  constructor
  · exact hInj
  · intro a ha
    rw [← hImage] at ha
    obtain ⟨e, he, hEq⟩ := ha
    exact ⟨e, he, hEq⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
