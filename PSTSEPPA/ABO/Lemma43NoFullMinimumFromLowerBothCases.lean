import PSTSEPPA.ABO.Lemma43MultiConstituentMinimumFromLowerInduction
import PSTSEPPA.ABO.Lemma43OneCoatomMinimumFromLowerInduction
import PSTSEPPA.ABO.Lemma43NoLargeCoatomLowerRank
import PSTSEPPA.ABO.Lemma43FiniteActiveCoatomCover

/-!
# ABO Lemma 4.3: the non-full-B component gets its minimum from LOWER ranks

This module combines TWO already published and separately certified
parts of Auinger--Bitterlich--Otto I Lemma 4.3 (pp.35--38), without
assuming a fictitious universal minimum for arbitrary incomplete graphs.

Fix a TRUE signed B-component Q of the actual old+fresh full proper
coset extension over a FINITE generated/retractable labelled group.
Work in the source non-full-B-coset branch: the component anchor has
NO genuine original component-tagged support E with B ⊆ E.

The explicit inductive hypotheses are exactly:
 * every original rooted lower C-stage full P_C coset extension is
   bridge-free;
 * its relevant actual (B∩C)-components have an attained minimum
   ORIGINAL tagged support with alphabet properly below C.

The source splits Q into TWO exhaustive constituent possibilities:

SINGLE constituent: Q is wholly inside some one ACTUAL old-component-
tagged selected coatom C. The non-full-B support obstruction forces
B∩C ⊊ C, by the certified old-tagged invariant. Apply the already
checked one-C-case lower-rank minimum construction (#766).

MULTIPLE constituents: Q is not wholly contained in ANY selected
old-component-tagged coatom meeting Q. Apply the already checked
multi-constituent lower-induction whole-component minimum theorem
(#739), which invokes true original boundary exit, finite edge-covered
family, and same original common-core witness.

Therefore, under just those explicit printed LOWER-RANK hypotheses,
the ENTIRE original component Q has an attained original-tagged
minimum support (M,m). There is NO additional hMulti/hContained
hypothesis for the user to supply, and no assertion that the
whole ambient group H is globally retractable when the paper
requires only local H[A] retractability: the current generic
CayleySubgraphSpec theorem assumes Retractable gen on the chosen Γ.

This is the missing precise induction input for the already
separately checked source original SIGNED full-B-coset versus
translated proper-cluster dichotomy (#774).
The original signed cluster/coset shape itself is not reproved here.

No sorry, new axiom, fake old signed edge, or identification
of distinct original component tags by ambient Cayley coordinates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Precisely the no-full-B-constituent LOWER-RANK induction
minimum-support input of the source Lemma 4.3.

It handles both the actual ONE-coatom and the genuine
MULTI-coatom original signed B-component branches without
requiring a separate component-cover case choice.

The minimum is a full Definition-3.22 ORIGINAL OLD component
pair (M,m), ATTAINED inside the entire B-component. -/
theorem allProperCoset_noFull_B_component_minimum_from_lower_induction
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (hNoFull :
      ∀ (E : Finset ι)
        (hEP : E ∈ (allProperCosetFamily A).alphabets),
          B ⊆ E →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret E anchor)
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
    ∃ (M : Finset ι) (m : K.ComponentIndex M),
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
        M m := by
  classical
  let P := allProperCosetFamily A
  let I := K.activeTaggedCoatoms hadm hgen hret B anchor
  let S := K.properCosetTagSlice hadm hgen hret B anchor
  let G := K.multiCosetEGraph P hadm hgen hret
  by_cases hSingle :
      ∃ t ∈ I, ∀ y : K.MultiCosetVertex P hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          G.Follows anchor w y) → y ∈ S t
  · obtain ⟨t, ht, hContained⟩ := hSingle
    let C := K.properCosetTagAlphabet t
    let hCP : C ∈ P.alphabets :=
      K.properCosetTagAlphabet_mem t
    let c : K.ComponentIndex C := K.properCosetTagIndex t
    obtain ⟨hCcard, ⟨y, hySlice⟩⟩ :=
      (K.mem_activeTaggedCoatoms_iff
        hadm hgen hret B anchor t).mp ht
    have hDlocal : B ∩ C ⊂ C :=
      (K.allProperCoset_noLarge_coatom_slice_both_inter_strict
        hadm hgen hret B hBP anchor hNoFull
        C hCP hCcard c y hySlice).2
    have hContainedC :
        ∀ z : K.MultiCosetVertex P hadm hgen hret,
          (∃ w : LabelWord ι, LabelWord.Uses B w ∧
            G.Follows anchor w z) →
          ∃ pC : K.AttachedCosetVertex C,
            pC.1 = c ∧
            z = K.multiCosetInclude P hadm hgen hret C hCP pC := by
      intro z hz
      exact (hContained z hz).2
    exact K.allProperCoset_one_coatom_component_minimum_of_lower_induction
      hadm hgen hret B C hCP hCcard hDlocal
      anchor c hContainedC (hBridge C hCP) (hLowerMinimum C hCP)
  · have hMulti :
        ∀ t ∈ I,
          ∃ (y : K.MultiCosetVertex P hadm hgen hret),
            (∃ w : LabelWord ι, LabelWord.Uses B w ∧
              G.Follows anchor w y) ∧
            ¬ ∃ q : K.AttachedCosetVertex
                (K.properCosetTagAlphabet t),
                q.1 = K.properCosetTagIndex t ∧
                y = K.multiCosetInclude P hadm hgen hret
                  (K.properCosetTagAlphabet t)
                  (K.properCosetTagAlphabet_mem t) q := by
      intro t ht
      have hWitness :
          ∃ y : K.MultiCosetVertex P hadm hgen hret,
            (∃ w : LabelWord ι, LabelWord.Uses B w ∧
              G.Follows anchor w y) ∧ y ∉ S t := by
        by_contra hNone
        apply hSingle
        refine ⟨t, ht, ?_⟩
        intro y hy
        by_contra hNot
        exact hNone ⟨y, hy, hNot⟩
      obtain ⟨y, hyReach, hyNotSlice⟩ := hWitness
      refine ⟨y, hyReach, ?_⟩
      intro hSupported
      obtain ⟨q, hqIndex, hqY⟩ := hSupported
      exact hyNotSlice ⟨hyReach, q, hqIndex, hqY⟩
    obtain ⟨M, m, _u, _hSupport, _hAll, hMinimum⟩ :=
      K.allProperCoset_multiConstituent_B_component_minimum
        hadm hgen hret hAcard B hBP anchor
        hMulti hBridge hLowerMinimum
    exact ⟨M, m, hMinimum⟩

end CayleySubgraphSpec
end ABO
