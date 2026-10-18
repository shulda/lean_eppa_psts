import PSTSEPPA.ABO.Lemma43OffFullComponentInductiveMinimum
import PSTSEPPA.ABO.Lemma43NonContainedCoatomRankDrop

/-!
# ABO Lemma 4.3: source-exact multi-constituent whole-component minimum

Strengthens the previously accepted conditional induction to EXACTLY
the source's genuine multi-constituent hypothesis. There is NO longer
any requirement that the B-component root lack a selected
superset-of-B support. What matters in the published proof is:

* B is a selected proper subalphabet;
* the true signed B-component Q is NOT contained in ANY SINGLE selected
  component-tagged coatom constituent which meets Q;
* the proper lower rooted C-extensions are bridge-free and satisfy
  the lower-rank cluster minimum-support induction hypotheses.

The accepted source geometric result
`allProperCoset_nonContained_coatom_slice_both_inter_strict`
proves B∩C⊊C DIRECTLY from the witnessed exit of Q from
each coatom C constituent, without the old stronger hypothesis.

The rest follows the verified actual source first-exit support,
lower rooted component minimum transport, finite signed coatom cover
and common-core induction. A genuine quotient vertex in ALL selected
coatom slices attains the original component-tagged minimum for Q.

This is the exact MINIMUM SUPPORT part of the published
multi-constituent branch in ABO I Lemma 4.3, not the full cluster
representation or the one-constituent/full-B-coset alternative.
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
theorem allProperCoset_multiConstituent_B_component_minimum
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
      (K.allProperCoset_nonContained_coatom_slice_both_inter_strict
        hadm hgen hret B C hBP hCP hCard
        anchor c hMeet (hMulti t ht)).2
    exact K.allProperCoset_tagged_slice_minimum_from_lower_induction
      hadm hgen hret B C hCP hDC
      anchor c y hy ⟨D₀, hD₀C, hD₀Support⟩
      (hBridge C hCP) (hLowerMinimum C hCP)
  exact K.allProperCoset_B_component_minimum_from_finite_coatoms
    hadm hgen hret (by omega) B anchor hEach

end CayleySubgraphSpec
end ABO
end PSTSEPPA
