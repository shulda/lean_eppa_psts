import PSTSEPPA.ABO.Lemma43FiniteTaggedCoatomIndex
import PSTSEPPA.ABO.Lemma43LocalSliceEdgeCoverConnectivity
import PSTSEPPA.ABO.Lemma43FiniteConnectedTaggedCommonCore

/-!
# ABO Lemma 4.3: construct a FINITE coatom cover of ONE genuine B-component

The source's finite-stage assumption means the original labelled group
Γ is finite. In that case the type of genuine original old-component-tagged
proper-alphabet constituents is finite (previous module).

For a fixed REAL signed B-component Q of the original uncompleted
full proper-coset EGraph, we select exactly those original tagged
COATOM constituents whose intersection with Q is NONEMPTY.
This is a finite family, independent of arbitrary choices of
ambient group representatives.

We verify the three concrete facts the PUBLISHED proof needs:

1. The fixed Q anchor belongs to a selected coatom slice.
2. EVERY genuine vertex of Q belongs to a selected coatom slice,
   by exact source coatom vertex support.
3. EVERY actual signed B-edge whose source is in Q has BOTH
   endpoints in a SINGLE selected coatom slice, by exact source
   CoatomEdgeCover. The target is reachable from Q's anchor
   by appending the TRUE signed edge, with no fictitious loops.

The previously checked Q-LOCAL signed-edge-cover connectivity
then shows that the intersection graph of all these finite
selected slices is connected. The accepted finite common-core
theorem concludes that if lower-rank induction supplies a minimum
original component-tagged support of each selected coatom slice,
then Q itself has ONE attained minimum support and there is a
GENUINE quotient vertex lying in EVERY selected slice.

This is precisely the coverage + finite common-core portion of
ABO Lemma 4.3 under its lower-rank minima hypotheses. It does
NOT prove those lower-rank hypotheses, localized H[A]
retractability, the already-full-B-coset alternative, or
the final cluster-shape identification via Corollary 3.12.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Finite original old-component-tagged COATOM constituents
which genuinely MEET the one selected intrinsic B-component
of the uncompleted old/fresh coset extension. Finite Γ makes
this an ACTUAL finite set of constituent tags. -/
noncomputable def activeTaggedCoatoms
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) : Finset K.ProperCosetTag := by
  classical
  letI : Finite K.ProperCosetTag := K.finite_properCosetTag
  letI : Fintype K.ProperCosetTag := Fintype.ofFinite _
  exact Finset.univ.filter fun t =>
    (K.properCosetTagAlphabet t).card + 1 = A.card ∧
      (K.properCosetTagSlice hadm hgen hret B anchor t).Nonempty

theorem mem_activeTaggedCoatoms_iff
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (t : K.ProperCosetTag) :
    t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor ↔
      (K.properCosetTagAlphabet t).card + 1 = A.card ∧
      (K.properCosetTagSlice hadm hgen hret B anchor t).Nonempty := by
  classical
  simp [activeTaggedCoatoms]

/-- The root of Q has a TRUE old-component-tagged
coatom presentation; consequently the finite active
family is never empty even for a singleton B-component. -/
theorem activeTaggedCoatoms_root
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    ∃ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
      anchor ∈ K.properCosetTagSlice hadm hgen hret B anchor t := by
  obtain ⟨t, htCard, p, hpIndex, hpAnchor⟩ :=
    K.allProperCoset_vertex_exists_tagged_coatom
      hadm hgen hret anchor
  have hMem : anchor ∈ K.properCosetTagSlice
      hadm hgen hret B anchor t := by
    refine ⟨⟨[], LabelWord.uses_nil B,
        EGraph.Follows.nil anchor⟩, p, hpIndex, ?_⟩
    exact hpAnchor.symm
  refine ⟨t, ?_, hMem⟩
  exact (K.mem_activeTaggedCoatoms_iff
    hadm hgen hret B anchor t).mpr
      ⟨htCard, ⟨anchor, hMem⟩⟩

/-- LITERAL finite coatom vertex coverage of the whole
chosen B-component Q. This never enumerates the vertices
of unrelated B-components. -/
theorem activeTaggedCoatoms_vertex_cover
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hReach :
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows anchor w y) :
    ∃ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
      y ∈ K.properCosetTagSlice hadm hgen hret B anchor t := by
  obtain ⟨t, htCard, p, hpIndex, hpY⟩ :=
    K.allProperCoset_vertex_exists_tagged_coatom
      hadm hgen hret y
  have hySlice : y ∈ K.properCosetTagSlice
      hadm hgen hret B anchor t :=
    ⟨hReach, p, hpIndex, hpY.symm⟩
  refine ⟨t, ?_, hySlice⟩
  exact (K.mem_activeTaggedCoatoms_iff
    hadm hgen hret B anchor t).mpr
      ⟨htCard, ⟨y, hySlice⟩⟩

/-- The finite active coatom family covers BOTH endpoints
of EVERY ACTUAL signed B-edge whose source lies in Q,
inside one SAME old-component-tagged complete coatom
constituent. The signed target B-reachability from
anchor is built by APPENDING the genuine oriented edge.

This is the source-exact local edge cover assumption
used by the already checked intersection-graph theorem. -/
theorem activeTaggedCoatoms_local_signed_edge_cover
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (hReach :
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows anchor w
          ((K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).source e))
    (hLabel :
      signedBase ((K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).label e) ∈ B) :
    ∃ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source e ∈
        K.properCosetTagSlice hadm hgen hret B anchor t ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).target e ∈
        K.properCosetTagSlice hadm hgen hret B anchor t := by
  let G := K.multiCosetEGraph (allProperCosetFamily A)
    hadm hgen hret
  obtain ⟨t, htCard, p, q, hpTag, hqTag, hSource, hTarget⟩ :=
    K.allProperCoset_edge_exists_tagged_coatom
      hadm hgen hret hcard e
  have hStep : G.Follows (G.source e)
      [G.label e] (G.target e) :=
    EGraph.Follows.cons e rfl rfl
      (EGraph.Follows.nil (G.target e))
  have hTargetReach :
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        G.Follows anchor w (G.target e) := by
    obtain ⟨w, hwB, hwPath⟩ := hReach
    refine ⟨w ++ [G.label e], ?_, ?_⟩
    · exact (LabelWord.uses_append B w _).mpr
        ⟨hwB, ⟨hLabel, trivial⟩⟩
    · exact G.follows_append hwPath hStep
  have hs :
      G.source e ∈
        K.properCosetTagSlice hadm hgen hret B anchor t :=
    ⟨hReach, p, hpTag, hSource⟩
  have ht :
      G.target e ∈
        K.properCosetTagSlice hadm hgen hret B anchor t :=
    ⟨hTargetReach, q, hqTag, hTarget⟩
  refine ⟨t, ?_, hs, ht⟩
  exact (K.mem_activeTaggedCoatoms_iff
    hadm hgen hret B anchor t).mpr
      ⟨htCard, ⟨G.source e, hs⟩⟩

/-- The actual slice-intersection graph of the explicitly
selected FINITE coatom family is CONNECTED, with a true
selected anchor slice. The edge cover needed in this proof
is LOCAL to the one B-component Q. -/
theorem activeTaggedCoatoms_intersection_graph_connected
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    ∃ root ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        Relation.ReflTransGen
          (fun s u : K.ProperCosetTag =>
            s ∈ K.activeTaggedCoatoms hadm hgen hret B anchor ∧
            u ∈ K.activeTaggedCoatoms hadm hgen hret B anchor ∧
            ((K.properCosetTagSlice hadm hgen hret B anchor s) ∩
             (K.properCosetTagSlice hadm hgen hret B anchor u)).Nonempty)
          root t := by
  classical
  let I := K.activeTaggedCoatoms hadm hgen hret B anchor
  let S := K.properCosetTagSlice hadm hgen hret B anchor
  obtain ⟨root, hroot, _hAnchorRoot⟩ :=
    K.activeTaggedCoatoms_root hadm hgen hret B anchor
  have hNonempty : ∀ t ∈ I, (S t).Nonempty := by
    intro t ht
    exact ((K.mem_activeTaggedCoatoms_iff
      hadm hgen hret B anchor t).mp ht).2
  have hEdgeCover :
      ∀ e : K.MultiCosetEdgeVertexIncidenceQuotient
          (allProperCosetFamily A) hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w
            ((K.multiCosetEGraph (allProperCosetFamily A)
              hadm hgen hret).source e)) →
        signedBase ((K.multiCosetEGraph
          (allProperCosetFamily A) hadm hgen hret).label e) ∈ B →
        ∃ t ∈ I,
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).source e ∈ S t ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).target e ∈ S t := by
    intro e hr hl
    exact K.activeTaggedCoatoms_local_signed_edge_cover
      hadm hgen hret hcard B anchor e hr hl
  have hConnected :=
    K.allProperCoset_local_tagged_slice_overlap_connected
      hadm hgen hret B anchor
      K.properCosetTagAlphabet
      (fun t => K.properCosetTagAlphabet_mem t)
      K.properCosetTagIndex
      I root hroot hNonempty hEdgeCover
  exact ⟨root, hroot, hConnected⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
