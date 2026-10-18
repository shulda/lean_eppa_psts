import PSTSEPPA.ABO.MultiCosetWholeComponentBoundarySupport
import PSTSEPPA.ABO.Lemma43TaggedSliceOverlapByDeletion
import PSTSEPPA.ABO.MaximalProperAlphabets

/-!
# ABO Lemma 4.3: every proper coatom slice in the multi-constituent case meets lower support

The PUBLISHED ABO I Lemma 4.3 (PDF pp.35–36) begins by
distinguishing an intrinsic signed B-component Q which is
already contained in one maximal constituent coset
from the genuinely multi-constituent case.

In the latter case, every maximal C-constituent slice
B_i = Q ∩ vH[C] is either empty or contains one actual
vertex supported by an alphabet D strictly BELOW C.

The hard first-exit signed-path theorem and its
whole-B-component corollary are ALREADY formalized
in MultiCosetMaximalConstituentPathExit.lean and
MultiCosetWholeComponentBoundarySupport.lean.

This module specializes that published geometric
argument to the exact TRUE old-component-tagged
B-component slices used by the finite coatom
cover and lower-rank minimum-support induction.

The only extra assumptions are the paper's rank
|A|>=3, the chosen C is a coatom, the selected
slice is genuinely nonempty, and Q is NOT entirely
contained in that SAME original old-C-component-tagged
constituent copy. No cluster property or bridge
freeness is assumed for the conclusion.

Unlike a mere ambient coset argument, the output
is a TRUE quotient vertex x in that SAME exact
tagged slice, carrying an actual smaller original
component-tagged support over D⊊C. The root's
true signed B-paths are part of the proof and
missing original old edges are never completed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Source Lemma 4.3's exact smaller-support boundary
point for a nonempty chosen coatom slice that does NOT
contain all of the selected TRUE signed B-component.

The resulting x is an actual original multi-coset
quotient point B-reachable from the same anchor, in
the SAME intrinsic original old C-component tag c,
with a genuine support over some D⊊C. -/
theorem allProperCoset_coatom_slice_exists_lower_support_of_not_contained
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (B C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCcard : C.card + 1 = A.card)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (hMeet :
      (K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c).Nonempty)
    (hNotContained :
      ∃ (y : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret),
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) ∧
        ¬ ∃ q : K.AttachedCosetVertex C,
          q.1 = c ∧
          y = K.multiCosetInclude
            (allProperCosetFamily A)
            hadm hgen hret C hCP q) :
    ∃ x : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret,
      x ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c ∧
      ∃ D : Finset ι,
        D ⊂ C ∧
        K.MultiCosetVertexSupported
          (allProperCosetFamily A) hadm hgen hret D x := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨z, hz⟩ := hMeet
  obtain ⟨hzReach, p, hpCtag, hpZ⟩ := hz
  obtain ⟨y, hyReach, hyOut⟩ := hNotContained
  have hCpos : 0 < C.card := by omega
  have hCne : C.Nonempty := Finset.card_pos.mp hCpos
  have hMax :
      ∀ (E : Finset ι)
        (hEP : E ∈ P.alphabets),
        C ⊆ E → E = C :=
    allProperCoset_coatom_maximal A C hCcard
  have hMeetC :
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        G.Follows
          (K.multiCosetInclude P hadm hgen hret C hCP p)
          w anchor := by
    obtain ⟨w, hw, hPath⟩ := hzReach
    refine ⟨PSTS.SignedWord.inv w, hw.inv, ?_⟩
    rw [← hpZ]
    exact G.follows_inverse hPath
  have hNotC :
      ∃ (y : K.MultiCosetVertex P hadm hgen hret)
        (w : LabelWord ι),
          LabelWord.Uses B w ∧
          G.Follows anchor w y ∧
          ¬ ∃ q : K.AttachedCosetVertex C,
            q.1 = p.1 ∧
            y = K.multiCosetInclude P hadm hgen hret C hCP q := by
    obtain ⟨w, hw, hPath⟩ := hyReach
    refine ⟨y, w, hw, hPath, ?_⟩
    intro hBad
    obtain ⟨q, hqp, hqy⟩ := hBad
    exact hyOut ⟨q, hqp.trans hpCtag, hqy⟩
  obtain ⟨x, ⟨q, hqp, hxC⟩, hxReach,
      D, hDC, hSupport⟩ :=
    K.allProperCoset_B_component_maximal_C_boundary_support
      hadm hgen hret B C hCP hCne hMax
      p anchor hMeetC hNotC
  refine ⟨x, ?_, D, hDC, hSupport⟩
  exact ⟨hxReach, q, hqp.trans hpCtag, hxC⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
