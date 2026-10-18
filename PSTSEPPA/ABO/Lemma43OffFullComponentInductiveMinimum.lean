import PSTSEPPA.ABO.Lemma43EveryNonSingleCoatomSliceLowerSupport
import PSTSEPPA.ABO.Lemma43FiniteCoatomWholeComponentMinimum
import PSTSEPPA.ABO.Lemma43LowerInductionToTaggedSliceMinimum
import PSTSEPPA.ABO.Lemma43NoLargeCoatomLowerRank

/-!
# ABO Lemma 4.3: from lower-rank cluster minima to one whole off-full B-component minimum

This is a source-aligned composition of ALREADY proved portions of the
published ABO I Lemma 4.3 (pp. 35–38), conditional on the exact remaining
lower-rank inductive hypotheses and source's explicit branch distinction.

Work with the actual incomplete old/fresh signed full proper-coset extension
over a FINITE generated and retractable group. For an intrinsic signed
B-component Q fix its real quotient anchor. Assume:

* B is a proper selected alphabet and NO completed selected E⊇B supports
  the anchor. This is the published non-full-B-coset branch.
* Q is not contained in ANY single coatom constituent that meets Q.
  This is the published multi-constituent branch.
* All lower proper C-component extensions have the specified bridge-free
  property, and all their relevant (B∩C)-components have one attained
  minimum support of proper C-rank (the LOWER-RANK cluster induction).

Then every selected coatom C-slice of Q has a minimum tagged support:
(1) the first-exit theorem finds a genuine vertex of the SAME tagged C-slice
    with an original proper D₀⊊C support, using its actual B-paths;
(2) the no-full-B obstruction and maximality imply B∩C⊊C;
(3) the source lower-rooted embedding and bridge-freeness transport the
    lower (B∩C)-component minimum to the ENTIRE upper C-slice.

The accepted finite tagged coatom-cover and finite connected common-core
theorems finally construct ONE ACTUAL quotient vertex present in ALL these
coatom slices and attaining a minimum ORIGINAL component-tagged support
(M,m) for the WHOLE true B-component Q.

The source's separate case when Q is already one completed constituent /
full B-coset, the final B-cluster identification via Corollary 3.12,
and the passage from local H[A]-retractability to the relevant actual
local signed skeleton are NOT silently claimed.

No new axioms, sorry, fictional old edges, or untagged Cayley injection.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Published Lemma-4.3 off-full-coset/multi-constituent induction
conclusion, with all LOWER-RANK bridge-free and cluster-minimum
assumptions explicitly preserved.

Unlike the intermediate finite-cover theorem, this does NOT assume
that each upper coatom slice already has its minimum: those are
DERIVED from the source's true boundary exit, support rank drop,
and lower-rank minimum transport lemmas.

One original quotient point simultaneously lies in every maximal
coatom slice of Q, attains its minimum (M,m), and the same original
component-tagged support is minimum for the ENTIRE signed B-component.
-/
theorem allProperCoset_offFull_multiConstituent_B_component_minimum
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
    ∃ (M : Finset ι) (m : K.ComponentIndex M)
      (u : K.MultiCosetVertex
        (allProperCosetFamily A) hadm hgen hret),
      K.HasTaggedSupportAt (allProperCosetFamily A)
        hadm hgen hret M m u ∧
      (∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        u ∈ K.properCosetTagSlice hadm hgen hret B anchor t) ∧
      K.IsMinimalTaggedSupportFor (allProperCosetFamily A)
        hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
        M m := by
  classical
  let P := allProperCosetFamily A
  let I := K.activeTaggedCoatoms hadm hgen hret B anchor
  have hEach :
      ∀ t ∈ I,
        ∃ (M : Finset ι) (m : K.ComponentIndex M),
          K.IsMinimalTaggedSupportFor P hadm hgen hret
            (K.properCosetTagSlice hadm hgen hret B anchor t) M m := by
    intro t ht
    let C := K.properCosetTagAlphabet t
    let hCP : C ∈ P.alphabets :=
      K.properCosetTagAlphabet_mem t
    let c : K.ComponentIndex C :=
      K.properCosetTagIndex t
    obtain ⟨hCard, hMeet⟩ :=
      (K.mem_activeTaggedCoatoms_iff
        hadm hgen hret B anchor t).mp ht
    obtain ⟨y, hy, D₀, hD₀C, hD₀Support⟩ :=
      K.allProperCoset_coatom_slice_exists_lower_support_of_not_contained
        hadm hgen hret hAcard B C hCP hCard
        anchor c hMeet (hMulti t ht)
    have hDC : B ∩ C ⊂ C :=
      (K.allProperCoset_noLarge_coatom_slice_both_inter_strict
        hadm hgen hret B hBP anchor hNoFull
        C hCP hCard c y hy).2
    exact K.allProperCoset_tagged_slice_minimum_from_lower_induction
      hadm hgen hret B C hCP hDC
      anchor c y hy ⟨D₀, hD₀C, hD₀Support⟩
      (hBridge C hCP) (hLowerMinimum C hCP)
  exact K.allProperCoset_B_component_minimum_from_finite_coatoms
    hadm hgen hret (by omega) B anchor hEach

end CayleySubgraphSpec
end ABO
end PSTSEPPA
