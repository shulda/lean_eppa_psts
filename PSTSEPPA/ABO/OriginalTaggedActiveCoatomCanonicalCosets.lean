import PSTSEPPA.ABO.CanonicalSignedTranslatedProperClusterNaturality
import PSTSEPPA.ABO.Lemma43TaggedSliceBInterCPaths

/-!
# Corrected ABO forward 4.5: ACTUAL original active tagged coatom slices lie in exact B∩C cosets

An ORIGINAL proper B-component of CE(H,L_H;P_A) is
covered by TRUE old-component-tagged maximal C-coset
constituents; for a selected active tag t the slice
Q ∩ (the actual tagged full H[C] copy) is a genuine
B∩C-connected subgraph, not just a set of equal
H ambient group coordinates.

The accepted signed-path theorem
`allProperCoset_taggedSlice_B_inter_C_connected`
constructs an actual chronological signed B∩C path
BETWEEN ANY TWO ORIGINAL vertices of this same
component-tagged slice. Source forward 4.5 gives a
genuine common core belonging to EVERY active slice.

Map these REAL ORIGINAL old/fresh signed paths
through the ORIGINAL source signed multiCE ambient
morphism to Cayley(H): each actual tagged slice
vertex has ambient H value inside the precise
left H[B∩C] coset based at the TRUE source common
core's H value. No globally injective H multiCE
ambient map or extra fictional old edge is assumed.

Independently, the concrete lower canonical B-cluster
family is the image of the TRUE active original coatom
tag set under t↦B∩C(t). Thus every actual selected
active original tag provides the exact corresponding
canonical cluster constituent piece; no free
piece-membership premise is needed.

This is a source-exact next step towards replacing
the abstract B∩C_i constituent coset-membership
hypotheses of the actual constructed H-stage→G
proper B-bridge by true ORIGINAL source tagged
coatom and common-core statements.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A chosen TRUE original component-tagged active
coatom t contributes B∩C(t) as an actual constituent
of the canonical translated proper B-cluster.
The source hProper is exactly the genuine strictness
hypothesis of the published proper branch. -/
theorem activeTaggedLowerCluster_actual_piece_of_active_tag
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hProper :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B)
    (t : K.ProperCosetTag)
    (ht : t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor) :
    B ∩ K.properCosetTagAlphabet t ∈
      (K.activeTaggedLowerClusterSpec
        hadm hgen hret B anchor hProper).pieces := by
  change
    B ∩ K.properCosetTagAlphabet t ∈
      (K.activeTaggedCoatoms hadm hgen hret B anchor).image
        (fun s => B ∩ K.properCosetTagAlphabet s)
  exact Finset.mem_image.mpr ⟨t, ht, rfl⟩

/-- Every TRUE original old B-component vertex x in
one selected active original component-tagged
C-constituent has its ORIGINAL group projection
in the exact gH[B∩C]-coset of the actual ORIGINAL
tagged common core. This follows from REAL old
positive/inverse signed B∩C paths in that slice,
not from abstract ambient H-coordinate equality
or an arbitrary (possibly non-natural) signed
cluster graph isomorphism. -/
theorem activeTaggedSlice_original_ambient_B_inter_C_coset
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor core : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        core ∈ K.properCosetTagSlice hadm hgen hret B anchor t)
    (t : K.ProperCosetTag)
    (ht : t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor)
    (x : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hx : x ∈ K.properCosetTagSlice hadm hgen hret B anchor t) :
    K.multiCosetAmbientValue (allProperCosetFamily A) hadm hgen hret x ∈
      generatedLeftCoset gen (B ∩ K.properCosetTagAlphabet t)
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret core) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let F := K.multiCosetAmbientHom P hadm hgen hret
  obtain ⟨w, hw, hRealPath⟩ :=
    K.allProperCoset_taggedSlice_B_inter_C_connected
      hadm hgen hret B
      (K.properCosetTagAlphabet t)
      (K.properCosetTagAlphabet_mem t)
      anchor (K.properCosetTagIndex t)
      core x (hAll t ht) hx
  have hMapped :
      (cayleyGraph gen).toEGraph.Follows
        (F.onVertex core) w (F.onVertex x) :=
    hRealPath.map F
  have hEnd :
      (cayleyGraph gen).followWord (F.onVertex core) w =
        F.onVertex x :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord (F.onVertex core) w)
      hMapped
  exact
    (mem_generatedLeftCoset_iff_subalphabetReachable
      gen (B ∩ K.properCosetTagAlphabet t)
      (F.onVertex core) (F.onVertex x)).mpr
        ⟨w, hw, hEnd⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
