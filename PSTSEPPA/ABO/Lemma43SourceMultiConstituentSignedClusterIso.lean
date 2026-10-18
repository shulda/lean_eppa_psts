import PSTSEPPA.ABO.Lemma43MultiConstituentMinimumFromLowerInduction
import PSTSEPPA.ABO.Lemma43NonContainedCoatomRankDrop
import PSTSEPPA.ABO.Lemma43ActualTranslatedLowerClusterSignedGraphIso

/-!
# ABO Lemma 4.3: source multi-constituent case gives actual signed B-cluster

The published Lemma 4.3 does not merely exhibit a common-core
support in the higher-rank induction. In the multi-constituent
case it identifies the entire ORIGINAL signed B-component
with an actual translated proper B-cluster, including both
formal orientations of every signed edge.

This file combines independently Lean-certified source stages:

(1) for a genuine B-component Q that is NOT contained in any
    one of its active original tagged maximal constituent copies,
    every active coatom C has B∩C properly contained in B;
    this follows from a real B-path escaping C, without the
    stronger no-superset-support hypothesis;
(2) under the precise lower-rank bridge-free and
    cluster-minimum hypotheses of the published induction,
    one actual old-component-tagged quotient vertex u
    belongs to ALL active coatom slices and attains a
    minimum tagged support of the ENTIRE B-component;
(3) the certified true signed graph isomorphism theorem
    identifies Q with the translated proper B-cluster
    formed from the lower pieces B∩C, on BOTH actual
    vertices and oriented signed edge tokens.

Unlike earlier intermediate lemmas, the NEW theorem below
does NOT require the common core nor the proper lower-cluster
pieces as additional hypotheses: both are DERIVED from
the genuine source multi-constituent case and the explicit
lower-rank induction premises.

The alternative that Q is contained in ONE completed
constituent, application of the complete Theorem 4.5
forward induction, and the source-local H[A]-retractability
transport remain separate. This is not a proof of
unconditional PSTS EPPA. No sorry/new axiom, untagged
global Cayley injection or fake old edges.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- In a TRUE multi-constituent B-component, every
original component-tagged active coatom C has a
STRICT lower piece B∩C⊊B. This is source Lemma 4.3
without an extra no-large-support assumption. -/
theorem allProperCoset_active_coatoms_proper_lower_pieces_of_multi
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hMulti :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        ∃ (y : K.MultiCosetVertex
            (allProperCosetFamily A) hadm hgen hret),
          (∃ w : LabelWord ι, LabelWord.Uses B w ∧
            (K.multiCosetEGraph (allProperCosetFamily A)
              hadm hgen hret).Follows anchor w y) ∧
          ¬ ∃ q : K.AttachedCosetVertex
              (K.properCosetTagAlphabet t),
            q.1 = K.properCosetTagIndex t ∧
            y = K.multiCosetInclude (allProperCosetFamily A)
              hadm hgen hret
              (K.properCosetTagAlphabet t)
              (K.properCosetTagAlphabet_mem t) q) :
    ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
      B ∩ K.properCosetTagAlphabet t ⊂ B := by
  intro t ht
  obtain ⟨hCard, hMeet⟩ :=
    (K.mem_activeTaggedCoatoms_iff
      hadm hgen hret B anchor t).mp ht
  exact
    (K.allProperCoset_nonContained_coatom_slice_both_inter_strict
      hadm hgen hret
      B (K.properCosetTagAlphabet t)
      hBP (K.properCosetTagAlphabet_mem t)
      hCard anchor (K.properCosetTagIndex t)
      hMeet (hMulti t ht)).1

/-- Exact multi-constituent CASE of published ABO I Lemma 4.3.

Assuming the original finite generated/retractable group,
the genuine old+fresh incomplete signed coset extension,
and the paper's lower-rank bridge-free and whole-component
minimum-support induction hypotheses, an intrinsic
B-component which is NOT contained in any single active
coatom constituent is a genuine translated PROPER B-cluster.

This conclusion constructs the minimum ORIGINAL tagged
support (M,m), a real minimum-attaining quotient core,
an actual EGraph on precisely the translated lower-cluster
vertex and oriented signed edge sets, and a true labelled
morphism of the original signed B-component onto that graph
which is BIJECTIVE on both carriers. -/
theorem allProperCoset_multiConstituent_B_component_signedClusterIso
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (hMulti :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        ∃ (y : K.MultiCosetVertex
            (allProperCosetFamily A) hadm hgen hret),
          (∃ w : LabelWord ι, LabelWord.Uses B w ∧
            (K.multiCosetEGraph (allProperCosetFamily A)
              hadm hgen hret).Follows anchor w y) ∧
          ¬ ∃ q : K.AttachedCosetVertex
              (K.properCosetTagAlphabet t),
            q.1 = K.properCosetTagIndex t ∧
            y = K.multiCosetInclude (allProperCosetFamily A)
              hadm hgen hret
              (K.properCosetTagAlphabet t)
              (K.properCosetTagAlphabet_mem t) q)
    (hBridge :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets)
        (root : K.Vertex),
        (K.subalphabetComponentSubgraph C root).MultiCosetBridgeFree
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
          hgen hret)
    (hLowerMinimum :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets)
        (root : K.Vertex),
        ∀ x₀ : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
          hgen hret,
        ∃ (M : Finset ι) (hMC : M ⊂ C)
          (m : (K.subalphabetComponentSubgraph C root).ComponentIndex M),
          (K.subalphabetComponentSubgraph C root).IsMinimalTaggedSupportFor
            (allProperCosetFamily C)
            (K.subalphabetComponentSubgraph_admissible
              hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
            hgen hret
            {x | ∃ w : LabelWord ι, LabelWord.Uses (B ∩ C) w ∧
              ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
                (allProperCosetFamily C)
                (K.subalphabetComponentSubgraph_admissible
                  hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
                hgen hret).Follows x₀ w x}
            M m) :
    ∃ (hProper :
        ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
          B ∩ K.properCosetTagAlphabet t ⊂ B)
      (M : Finset ι) (m : K.ComponentIndex M)
      (core : K.MultiCosetVertex
        (allProperCosetFamily A) hadm hgen hret),
      K.HasTaggedSupportAt (allProperCosetFamily A)
        hadm hgen hret M m core ∧
      K.IsMinimalTaggedSupportFor (allProperCosetFamily A)
        hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
        M m ∧
      ∃ (T : EGraph
          {g : Γ // g ∈
            ClusterSpec.LeftTranslateSet
              (K.multiCosetAmbientValue
                (allProperCosetFamily A) hadm hgen hret core)
              ((K.activeTaggedLowerClusterSpec
                hadm hgen hret B anchor hProper).VertexSet gen)}
          {a : ActionEdge Γ ι // a ∈
            ClusterSpec.LeftTranslateEdgeSet
              (K.multiCosetAmbientValue
                (allProperCosetFamily A) hadm hgen hret core)
              ((K.activeTaggedLowerClusterSpec
                hadm hgen hret B anchor hProper).EdgeSet gen)} ι)
        (f : LabelledGraphHom
          ((K.multiCosetEGraph
            (allProperCosetFamily A) hadm hgen hret).BComponentEGraph
              B anchor).toLabelledGraph
          T.toLabelledGraph),
        Function.Bijective f.onVertex ∧
        Function.Bijective f.onEdge := by
  have hProper :=
    K.allProperCoset_active_coatoms_proper_lower_pieces_of_multi
      hadm hgen hret B hBP anchor hMulti
  obtain ⟨M, m, core, hSupport, hAll, hMinimum⟩ :=
    K.allProperCoset_multiConstituent_B_component_minimum
      hadm hgen hret hAcard B hBP anchor hMulti
      hBridge hLowerMinimum
  obtain ⟨T, f, hBijV, hBijE⟩ :=
    K.allProperCoset_B_component_translatedLowerCluster_signedGraphIso
      hadm hgen hret (by omega) B anchor core hAll hProper
  exact ⟨hProper, M, m, core, hSupport, hMinimum,
    T, f, hBijV, hBijE⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
