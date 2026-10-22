import PSTSEPPA.ABO.ForwardInductionOriginalActiveCoatomTags
import PSTSEPPA.ABO.ForwardInductionLocalCompletedEGraphAgreement

/-!
# ABO 4.5: original Γ-rooted active coatom tags are intrinsically defined

The prior source Γ tagged common-core proof transported all active
coatom indices by a genuinely dependent local H[C]↔ORIGINAL Γ
component-index equivalence. We now independently define, *in the
original incomplete signed Γ-rooted quotient itself*, the coatom
slice of a true signed B-component:

  real B-reachability in the original source EGraph AND support in
  that precise ORIGINAL old D-component tag.

An ORIGINAL coatom is active iff its alphabet is a maximal proper
one and its original slice is nonempty. This definition mentions
no local active family. We prove that this SOURCE-intrinsic finite
active set is EXACTLY the transported local family, by reflecting
actual signed B-word paths and authentic tagged source supports.
Consequently the previously certified original common-core
statement quantifies over precisely the original coatom family.

No ambient Γ global generation/retractability or fake old signed
edges, and no equality-of-group-coordinates identification of old
component tags. No custom axiom/sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The intrinsically ORIGINAL Γ-rooted coatom-tagged slice of
a genuine signed B-component: actual ORIGINAL signed B-path
reachability AND an ORIGINAL intrinsic old-component D-tag,
not a local H[C] component or ambient group coordinate. -/
def arbitraryRankRootedOriginalTaggedCoatomSlice
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret)
    (t : (K.subalphabetComponentSubgraph C root).ProperCosetTag) :
    Set (Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root (allProperCosetFamily C) hadm hgen hret)) :=
  {y | (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root (allProperCosetFamily C) hadm hgen hret).Follows
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root (allProperCosetFamily C) hadm hgen hret u) w y) ∧
      K.ArbitraryRankRootedOriginalTaggedSupportAt
        C root (allProperCosetFamily C) hadm hgen hret
        ((K.subalphabetComponentSubgraph C root).properCosetTagAlphabet t)
        ((K.subalphabetComponentSubgraph C root).properCosetTagIndex t) y }

/-- For EACH intrinsic old tagged local coatom, its genuine signed
B-component slice corresponds exactly to the intrinsically
ORIGINAL Γ-rooted tagged coatom slice under the certified
source/local vertex quotient equivalence, in BOTH directions. -/
theorem originalRootedTaggedCoatomSlice_mem_iff
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret)
    (t : (K.intrinsicComponentLocalSlice C root).ProperCosetTag)
    (z : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret) :
    z ∈ (K.intrinsicComponentLocalSlice C root).properCosetTagSlice
      hadm hgen hret B u t ↔
    (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
      C root (allProperCosetFamily C) hadm hgen hret z) ∈
      K.arbitraryRankRootedOriginalTaggedCoatomSlice
        C root hadm hgen hret B u
        (K.originalRootedProperCosetTagEquiv C root t) := by
  let L := K.intrinsicComponentLocalSlice C root
  let P := allProperCosetFamily C
  let D := L.properCosetTagAlphabet t
  let d := L.properCosetTagIndex t
  let hDP := L.properCosetTagAlphabet_mem t
  constructor
  · rintro ⟨⟨w, hw, hPath⟩, q, hTag, hInclude⟩
    have hLocalPath :
        (K.arbitraryRankRootedLocalCompletedEGraph
          C root P hadm hgen hret).Follows u w z :=
      (K.arbitraryRankRootedLocalCompletedFollows_iff_standard
        C root P hadm hgen hret u z w).mpr hPath
    have hOriginalPath :=
      (K.arbitraryRankRootedCompletedEGraphHom_follows_iff
        C root P hadm hgen hret u z w).mp hLocalPath
    have hTagged :
        L.HasTaggedSupportAt P hadm hgen hret D d z :=
      ⟨hDP, q, hTag, hInclude.symm⟩
    have hOriginalTag :=
      (K.arbitraryRankRootedLocalTaggedSupport_iff_original
        C root P hadm hgen hret D d z).mp hTagged
    exact ⟨⟨w, hw, hOriginalPath⟩, hOriginalTag⟩
  · rintro ⟨⟨w, hw, hOriginalPath⟩, hOriginalTag⟩
    have hLocalPath :
        (L.multiCosetEGraph P hadm hgen hret).Follows u w z :=
      (K.arbitraryRankRootedLocalCompletedFollows_iff_standard
        C root P hadm hgen hret u z w).mp
        ((K.arbitraryRankRootedCompletedEGraphHom_follows_iff
          C root P hadm hgen hret u z w).mpr hOriginalPath)
    have hLocalTag :
        L.HasTaggedSupportAt P hadm hgen hret D d z :=
      (K.arbitraryRankRootedLocalTaggedSupport_iff_original
        C root P hadm hgen hret D d z).mpr hOriginalTag
    obtain ⟨_hDP, q, hTag, hInclude⟩ := hLocalTag
    exact ⟨⟨w, hw, hLocalPath⟩, q, hTag, hInclude.symm⟩

/-- SOURCE-intrinsic finite active coatom family: a tag of the
ORIGINAL rooted Γ skeleton is active precisely if its selected
alphabet is maximal proper in C and its ORIGINAL signed B-component
slice is NONEMPTY. This definition does not invoke local activity. -/
noncomputable def originalRootedIntrinsicActiveTaggedCoatoms
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret) :
    Finset (K.subalphabetComponentSubgraph C root).ProperCosetTag := by
  classical
  let M := K.subalphabetComponentSubgraph C root
  letI : Finite M.ProperCosetTag := M.finite_properCosetTag
  letI : Fintype M.ProperCosetTag := Fintype.ofFinite _
  exact Finset.univ.filter (fun t =>
    (M.properCosetTagAlphabet t).card + 1 = C.card ∧
      (K.arbitraryRankRootedOriginalTaggedCoatomSlice
        C root hadm hgen hret B u t).Nonempty)

/-- An ORIGINAL Γ-rooted coatom is intrinsically active iff
the corresponding genuine LOCAL signed H[C] coatom is active.
No direction assumes actual activity, and both are proved
using real signed paths and preserved original support tags. -/
theorem originalRootedIntrinsicActiveTaggedCoatoms_mem_iff
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret)
    (t : (K.intrinsicComponentLocalSlice C root).ProperCosetTag) :
    K.originalRootedProperCosetTagEquiv C root t ∈
      K.originalRootedIntrinsicActiveTaggedCoatoms
        C root hadm hgen hret B u ↔
    t ∈ (K.intrinsicComponentLocalSlice C root).activeTaggedCoatoms
      hadm hgen hret B u := by
  classical
  let L := K.intrinsicComponentLocalSlice C root
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root (allProperCosetFamily C) hadm hgen hret
  rw [show
    K.originalRootedProperCosetTagEquiv C root t ∈
      K.originalRootedIntrinsicActiveTaggedCoatoms
        C root hadm hgen hret B u ↔
      ((K.subalphabetComponentSubgraph C root).properCosetTagAlphabet
        (K.originalRootedProperCosetTagEquiv C root t)).card + 1 =
          C.card ∧
        (K.arbitraryRankRootedOriginalTaggedCoatomSlice
          C root hadm hgen hret B u
          (K.originalRootedProperCosetTagEquiv C root t)).Nonempty from by
            simp [originalRootedIntrinsicActiveTaggedCoatoms]]
  rw [L.mem_activeTaggedCoatoms_iff hadm hgen hret B u t]
  constructor
  · rintro ⟨hCard, ⟨y, hy⟩⟩
    let z := e.symm y
    have he : e z = y := e.apply_symm_apply y
    have hLocal : z ∈ L.properCosetTagSlice hadm hgen hret B u t :=
      (K.originalRootedTaggedCoatomSlice_mem_iff
        C root hadm hgen hret B u t z).mpr (by
          rw [he]
          exact hy)
    exact ⟨by simpa only [K.originalRootedProperCosetTagEquiv_alphabet]
                  using hCard, ⟨z, hLocal⟩⟩
  · rintro ⟨hCard, ⟨z, hLocal⟩⟩
    refine ⟨?_, ⟨e z, ?_⟩⟩
    · simpa only [K.originalRootedProperCosetTagEquiv_alphabet]
        using hCard
    · exact (K.originalRootedTaggedCoatomSlice_mem_iff
        C root hadm hgen hret B u t z).mp hLocal

/-- The previous transported finite active coatom family equals
the INTRINSICALLY SOURCE-DEFINED family of actual signed slices.
Thus the original common core quantifies over exactly the
original old-component-tagged coatom constituents of B. -/
theorem originalRootedIntrinsicActive_eq_transported
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret) :
    K.originalRootedIntrinsicActiveTaggedCoatoms
      C root hadm hgen hret B u =
    K.originalRootedActiveTaggedCoatoms
      C root hadm hgen hret B u := by
  classical
  ext tag
  obtain ⟨t, rfl⟩ :=
    (K.originalRootedProperCosetTagEquiv C root).surjective tag
  exact (K.originalRootedIntrinsicActiveTaggedCoatoms_mem_iff
    C root hadm hgen hret B u t).trans
      (K.originalRootedActiveTaggedCoatoms_mem_iff
        C root hadm hgen hret B u t).symm

end CayleySubgraphSpec
end ABO
end PSTSEPPA
