import PSTSEPPA.ABO.Lemma43SingleCoatomNoLowerMinimum
import PSTSEPPA.ABO.Lemma43LowerInductionToTaggedSliceMinimumOffSkeleton
import PSTSEPPA.ABO.Lemma43TaggedSliceOverlapByDeletion

/-!
# ABO Lemma 4.3: a component contained in one maximal C-copy has a minimum

The PUBLISHED source proof treats a true B-component Q wholly
contained in one original component-tagged completed maximal
C-constituent separately from the multi-constituent case.

The source distinguishes whether Q admits ANY original tagged
support over D₀⊊C; we now require Q to avoid the upper old skeleton,
so the relevant lower component is OFF its own lower old skeleton:

* If no such support exists, the accepted single-coatom
  minimum lemma proves (C,c) is the attained minimum for
  all Q, including its ORIGINAL intrinsic old C-component tag.
* If such a vertex y exists and B∩C⊊C, use the already
  certified lower-rooted C-stage support-contact,
  bridge-free intersection and lower-rank component
  cluster-minimum induction to construct the attained
  minimum for the ENTIRE upper tagged C-slice.

Since the assumed one-constituent copy actually contains
the WHOLE B-component, its tagged slice is EXACTLY Q,
not merely a connected subset or a set of equal ambient
Cayley coordinates.

This gives the full MINIMUM-SUPPORT conclusion of the
one-constituent case under explicit source lower-rank
premises and the proper-local-rank B∩C⊊C condition.

If B=C, the component meets the original skeleton
and Definition 3.22's OFF-skeleton clause is not
needed; the separate full-B-coset case is already
described by the certified exact selected-C component
theorem. No extra axioms/sorry/global ambient
embedding or fake signed edges are used.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Whole-component minimum for the source's one-coatom
alternative, allowing EITHER the existence or the absence
of an actual support strictly below C.

Lower bridge freeness and lower B∩C-component minimum
remain the exact explicit assumptions from the
published induction; no support existence is presumed.

The ambient extension's entire signed B-component
is assumed to be contained in the SAME original
component-tagged C-copy, not just to have coordinates
in one untagged subgroup coset. -/
theorem allProperCoset_one_coatom_component_minimum_of_off_skeleton_lower_induction
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hCcard : C.card + 1 = A.card)
    (hDlocal : B ∩ C ⊂ C)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (hContained :
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) →
        ∃ pC : K.AttachedCosetVertex C,
          pC.1 = c ∧
          y = K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP pC)
    (hUpperOff :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            B hBP).onVertex x)
          w anchor)
    (hBridge :
      ∀ root : K.Vertex,
        (K.subalphabetComponentSubgraph C root).MultiCosetBridgeFree
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
          hgen hret)
    (hLowerMin :
      ∀ root : K.Vertex,
        ∀ x₀ : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
          hgen hret,
        (¬ ∃ (v : (K.subalphabetComponentSubgraph C root).Vertex)
          (w : LabelWord ι),
          LabelWord.Uses (B ∩ C) w ∧
          ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
            (allProperCosetFamily C)
            (K.subalphabetComponentSubgraph_admissible
              hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
            hgen hret).Follows
              (((K.subalphabetComponentSubgraph C root).skeletonToMultiCosetHom
                (allProperCosetFamily C)
                (K.subalphabetComponentSubgraph_admissible
                  hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
                hgen hret (B ∩ C)
                ((mem_allProperCosetFamily C (B ∩ C)).mpr hDC)).onVertex v)
              w x₀) →
        ∃ (M : Finset ι) (hMC : M ⊂ C)
          (m : (K.subalphabetComponentSubgraph C root).ComponentIndex M),
          (K.subalphabetComponentSubgraph C root).IsMinimalTaggedSupportFor
            (allProperCosetFamily C)
            (K.subalphabetComponentSubgraph_admissible
              hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
            hgen hret
            { x | ∃ w : LabelWord ι,
              LabelWord.Uses (B ∩ C) w ∧
              ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
                (allProperCosetFamily C)
                (K.subalphabetComponentSubgraph_admissible
                  hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
                hgen hret).Follows x₀ w x }
            M m) :
    ∃ (M : Finset ι) (m : K.ComponentIndex M),
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        { y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y }
        M m := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let S : Set (K.MultiCosetVertex P hadm hgen hret) :=
    { y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      G.Follows anchor w y }
  let T : Set (K.MultiCosetVertex P hadm hgen hret) :=
    K.allProperCoset_taggedConstituentSlice
      hadm hgen hret B anchor C hCP c
  have hST : S = T := by
    ext y
    constructor
    · intro hy
      obtain ⟨pC, hpIndex, hpY⟩ := hContained y hy
      exact ⟨hy, pC, hpIndex, hpY⟩
    · intro hy
      exact hy.1
  by_cases hSmall :
      ∃ y : K.MultiCosetVertex P hadm hgen hret,
        y ∈ S ∧
        ∃ D₀ : Finset ι, D₀ ⊂ C ∧
          K.MultiCosetVertexSupported P hadm hgen hret D₀ y
  · obtain ⟨y, hyS, D₀, hD₀C, hD₀Supported⟩ := hSmall
    have hyT : y ∈ T := hST ▸ hyS
    obtain ⟨M, m, hMinT⟩ :=
      K.allProperCoset_tagged_slice_minimum_from_off_skeleton_lower_induction
        hadm hgen hret B C hCP hBP hDlocal
        anchor c y hyT ⟨D₀, hD₀C, hD₀Supported⟩
        hUpperOff hBridge hLowerMin
    refine ⟨M, m, ?_⟩
    change K.IsMinimalTaggedSupportFor P hadm hgen hret S M m
    rw [hST]
    exact hMinT
  · have hNoLower :
        ∀ y : K.MultiCosetVertex P hadm hgen hret,
          y ∈ S →
          ∀ D₀ : Finset ι, D₀ ⊂ C →
            ¬ K.MultiCosetVertexSupported
              P hadm hgen hret D₀ y := by
      intro y hy D₀ hD₀C hSupp
      exact hSmall ⟨y, hy, D₀, hD₀C, hSupp⟩
    exact ⟨C, c,
      K.allProperCoset_single_coatom_no_lower_minimal_support
        hadm hgen hret B C hCP hCcard
        anchor c hContained hNoLower⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
