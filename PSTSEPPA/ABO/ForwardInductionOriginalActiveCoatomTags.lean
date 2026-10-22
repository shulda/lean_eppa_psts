import PSTSEPPA.ABO.ForwardInductionOriginalTaggedCommonCore

/-!
# ABO Theorem 4.5: fully ORIGINAL Γ-rooted active coatom tags

The accepted local H[C] induction proves a common-core property whose
coatom quantifier runs through local H[C] intrinsic component indices.
However the printed source Γ statement must quantify over the genuinely
ORIGINAL connected-component indices of the rooted Γ old skeleton.

Here we define a precise dependent equivalence of local and ORIGINAL
proper constituent tags. It preserves the selected alphabet exactly
and transports the quotient D-component index via the already certified
rooted local component-index equivalence; no two old D-components may
be identified merely because their ambient Γ coordinates agree.

The ORIGINAL active coatom family is the image of the actual local
finite active family under that dependent equivalence. Its membership
is EXACTLY reflected, not just preserved.

Finally we strengthen the previously certified source original tagged
common-core theorem: the same ORIGINAL B-word reachable core attains
the ORIGINAL minimum of the WHOLE signed B-component and has tagged
support at EVERY member of this ORIGINAL active coatom family.

No global Γ generation/retractability, false old edge, new axiom or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact dependent equivalence of LOCAL H[C] and genuine ORIGINAL
Γ-rooted old-component-tagged proper constituent indices. The
alphabet itself is unchanged; the intrinsic D-component index is
transported by an actual old signed D-path component equivalence. -/
noncomputable def originalRootedProperCosetTagEquiv
    (C : Finset ι) (root : K.Vertex) :
    (K.intrinsicComponentLocalSlice C root).ProperCosetTag ≃
    (K.subalphabetComponentSubgraph C root).ProperCosetTag :=
  Equiv.sigmaCongrRight (fun D =>
    K.rootedLocalComponentIndexEquiv C root D.1)

/-- No selected alphabet is changed by original-rooted tag transport. -/
theorem originalRootedProperCosetTagEquiv_alphabet
    (C : Finset ι) (root : K.Vertex)
    (t : (K.intrinsicComponentLocalSlice C root).ProperCosetTag) :
    (K.subalphabetComponentSubgraph C root).properCosetTagAlphabet
      (K.originalRootedProperCosetTagEquiv C root t) =
    (K.intrinsicComponentLocalSlice C root).properCosetTagAlphabet t := rfl

/-- The original D-component tag, separately from the group
coordinate, is the transported local intrinsic D-component index. -/
theorem originalRootedProperCosetTagEquiv_index
    (C : Finset ι) (root : K.Vertex)
    (t : (K.intrinsicComponentLocalSlice C root).ProperCosetTag) :
    (K.subalphabetComponentSubgraph C root).properCosetTagIndex
      (K.originalRootedProperCosetTagEquiv C root t) =
    K.rootedLocalComponentIndexEquiv C root
      ((K.intrinsicComponentLocalSlice C root).properCosetTagAlphabet t)
      ((K.intrinsicComponentLocalSlice C root).properCosetTagIndex t) := rfl

/-- Genuine finite ORIGINAL old-component-tagged active coatom family.
This is a finset of ORIGINAL Γ-rooted D-component indices, not
a finset of locally normalized H[C] tags. -/
noncomputable def originalRootedActiveTaggedCoatoms
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret) :
    Finset (K.subalphabetComponentSubgraph C root).ProperCosetTag := by
  classical
  exact ((K.intrinsicComponentLocalSlice C root).activeTaggedCoatoms
    hadm hgen hret B u).image (K.originalRootedProperCosetTagEquiv C root)

/-- Original Γ-rooted coatom ACTIVITY is equivalent to the
corresponding normalized H[C] source activity, retaining
the original exact D-component index and actual signed paths. -/
theorem originalRootedActiveTaggedCoatoms_mem_iff
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret)
    (t : (K.intrinsicComponentLocalSlice C root).ProperCosetTag) :
    K.originalRootedProperCosetTagEquiv C root t ∈
      K.originalRootedActiveTaggedCoatoms C root hadm hgen hret B u ↔
    t ∈ (K.intrinsicComponentLocalSlice C root).activeTaggedCoatoms
      hadm hgen hret B u := by
  classical
  change (K.originalRootedProperCosetTagEquiv C root t) ∈
    ((K.intrinsicComponentLocalSlice C root).activeTaggedCoatoms
      hadm hgen hret B u).image
        (K.originalRootedProperCosetTagEquiv C root) ↔ _
  constructor
  · intro ht
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp ht
    have hSame : s = t :=
      (K.originalRootedProperCosetTagEquiv C root).injective hst
    simpa only [hSame] using hs
  · intro ht
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩

/-- COMPLETE original Γ-facing common-core condition: one original
old-tagged minimum of the WHOLE real signed B-component, attained
at one actual original B-reachable core, which has support at each
ORIGINAL active coatom's intrinsic D-component tag. -/
def HasExactOriginalRootedSignedTaggedCommonCore
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret) : Prop :=
  ∃ (M : Finset ι)
    (m : (K.subalphabetComponentSubgraph C root).ComponentIndex M)
    (core : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root (allProperCosetFamily C) hadm hgen hret)),
    K.ArbitraryRankRootedOriginalMinimalTaggedSupportFor
      C root (allProperCosetFamily C) hadm hgen hret
      {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.arbitraryRankRootedOriginalCompletedEGraph
          C root (allProperCosetFamily C) hadm hgen hret).Follows
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root (allProperCosetFamily C) hadm hgen hret u) w y}
      M m ∧
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root (allProperCosetFamily C) hadm hgen hret).Follows
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root (allProperCosetFamily C) hadm hgen hret u) w core) ∧
    K.ArbitraryRankRootedOriginalTaggedSupportAt
      C root (allProperCosetFamily C) hadm hgen hret M m core ∧
    ∀ t ∈ K.originalRootedActiveTaggedCoatoms
        C root hadm hgen hret B u,
      K.ArbitraryRankRootedOriginalTaggedSupportAt
        C root (allProperCosetFamily C) hadm hgen hret
        ((K.subalphabetComponentSubgraph C root).properCosetTagAlphabet t)
        ((K.subalphabetComponentSubgraph C root).properCosetTagIndex t)
        core

/-- The previous genuine ORIGINAL root-normalized signed common core
theorem now quantifies over ORIGINAL active D-component tags,
not the local H[C] tag carrier. -/
theorem exactOriginalRootedSignedTaggedCommonCore_of_localTagged
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret)
    (h : K.HasOriginalRootedSignedTaggedCommonCore
      C root hadm hgen hret B u) :
    K.HasExactOriginalRootedSignedTaggedCommonCore
      C root hadm hgen hret B u := by
  classical
  obtain ⟨M, m, core, hMin, hReach, hTagged, hAll⟩ := h
  refine ⟨M, m, core, hMin, hReach, hTagged, ?_⟩
  intro t ht
  change t ∈ ((K.intrinsicComponentLocalSlice C root).activeTaggedCoatoms
    hadm hgen hret B u).image
      (K.originalRootedProperCosetTagEquiv C root) at ht
  obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp ht
  subst t
  change K.ArbitraryRankRootedOriginalTaggedSupportAt
    C root (allProperCosetFamily C) hadm hgen hret
    ((K.intrinsicComponentLocalSlice C root).properCosetTagAlphabet s)
    (K.rootedLocalComponentIndexEquiv C root
      ((K.intrinsicComponentLocalSlice C root).properCosetTagAlphabet s)
      ((K.intrinsicComponentLocalSlice C root).properCosetTagIndex s))
    core
  exact hAll s hs

end CayleySubgraphSpec
end ABO
end PSTSEPPA
