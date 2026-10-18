import PSTSEPPA.ABO.Lemma43TaggedSliceOverlapByDeletion
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.MaximalProperAlphabets

/-!
# ABO Lemma 4.3: genuine multi-constituent case forces rank drop B∩C⊊C

The source's multi-constituent branch of published Lemma 4.3
does NOT need the stronger hypothesis that no selected E⊇B
supports the component anchor.

Fix a TRUE signed B-component Q and a nonempty intersection
with one specific ORIGINAL component-tagged completed coatom
constituent C (codimension one in A). Suppose Q has an ACTUAL
vertex outside that SAME tagged C-copy. Then necessarily
B⊄C: otherwise all true B-paths starting at the C-supported
vertex stay in precisely that tagged completed C-copy,
contrary to the witnessed outside-Q point.

Because B itself is a selected proper subalphabet, maximality
of the coatom C then also gives C⊄B: otherwise C⊆B⊊A
forces C=B, contradicting B⊄C.

Consequently D=B∩C is a proper subalphabet of BOTH B and C,
and in particular belongs to the proper C-family used in
the LOWER-rank ABO Lemma 4.3 induction.

This is the exact published source alternative for a
multi-constituent B-component. All inclusions and the
contradiction are established from ACTUAL signed paths
in the ORIGINAL incomplete EGraph and exact old
component-tagged constituent membership, not from
ambient group-coordinate coset equality.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The rank drop D=B∩C⊊C for a nonempty coatom
slice of a real B-component Q NOT contained in
that one exact old-C-component-tagged constituent.

No all-large-support exclusion is assumed. This
aligns with the multi-constituent branch in
the proof of published ABO Lemma 4.3. -/
theorem allProperCoset_nonContained_coatom_slice_both_inter_strict
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCcard : C.card + 1 = A.card)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (hMeet :
      (K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c).Nonempty)
    (hExit :
      ∃ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) ∧
        ¬ ∃ q : K.AttachedCosetVertex C,
          q.1 = c ∧
          y = K.multiCosetInclude
            (allProperCosetFamily A) hadm hgen hret C hCP q) :
    (B ∩ C) ⊂ B ∧ (B ∩ C) ⊂ C := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨x, hx⟩ := hMeet
  obtain ⟨⟨p, hpB, hAx⟩, pC, hIndexC, hxC⟩ := hx
  obtain ⟨y, ⟨q, hqB, hAy⟩, hNotC⟩ := hExit
  have hBnotC : ¬ B ⊆ C := by
    intro hBC
    have hXY : G.Follows x (PSTS.SignedWord.inv p ++ q) y :=
      G.follows_append (G.follows_inverse hAx) hAy
    have hwC : LabelWord.Uses C (PSTS.SignedWord.inv p ++ q) :=
      ((LabelWord.uses_append B (PSTS.SignedWord.inv p) q).mpr
        ⟨hpB.inv, hqB⟩).mono hBC
    have hFromC : G.Follows
        (K.multiCosetInclude P hadm hgen hret C hCP pC)
        (PSTS.SignedWord.inv p ++ q) y := by
      rw [← hxC]
      exact hXY
    obtain ⟨v, hvIndex, hvVertex⟩ :=
      K.multiCoset_selected_B_path_stays_in_coset
        P hadm hgen hret C hCP
        (PSTS.SignedWord.inv p ++ q)
        hwC pC y hFromC
    exact hNotC ⟨v, hvIndex.trans hIndexC, hvVertex.symm⟩
  have hCnotB : ¬ C ⊆ B := by
    intro hCB
    have hBCeq : B = C :=
      allProperCoset_coatom_maximal A C hCcard B hBP hCB
    exact hBnotC hBCeq.le
  constructor
  · refine ⟨Finset.inter_subset_left, ?_⟩
    intro hBad
    apply hBnotC
    intro i hi
    exact (Finset.mem_inter.mp (hBad hi)).2
  · refine ⟨Finset.inter_subset_right, ?_⟩
    intro hBad
    apply hCnotB
    intro i hi
    exact (Finset.mem_inter.mp (hBad hi)).1

/-- Source's proper-local-rank conclusion as a selected lower alphabet. -/
theorem allProperCoset_nonContained_coatom_slice_lower_alphabet
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCcard : C.card + 1 = A.card)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (hMeet :
      (K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c).Nonempty)
    (hExit :
      ∃ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) ∧
        ¬ ∃ q : K.AttachedCosetVertex C,
          q.1 = c ∧
          y = K.multiCosetInclude
            (allProperCosetFamily A) hadm hgen hret C hCP q) :
    B ∩ C ∈ (allProperCosetFamily C).alphabets := by
  exact (mem_allProperCosetFamily C (B ∩ C)).mpr
    (K.allProperCoset_nonContained_coatom_slice_both_inter_strict
      hadm hgen hret B C hBP hCP hCcard
      anchor c hMeet hExit).2

end CayleySubgraphSpec
end ABO
