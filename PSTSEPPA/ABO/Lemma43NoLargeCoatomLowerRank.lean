import PSTSEPPA.ABO.MultiCosetComponentSupportDichotomy
import PSTSEPPA.ABO.Lemma43TaggedSliceOverlapByDeletion
import PSTSEPPA.ABO.MaximalProperAlphabets

/-!
# ABO Lemma 4.3: coatom pieces in the true cluster case have strictly lower B∩C rank

The published Lemma 4.3 distinguishes two cases.
If an original B-component Q meets a genuinely completed
C-constituent with B ⊆ C, it is already a full B-coset,
the separate type-(1) alternative. Otherwise every
selected maximal proper constituent C meeting Q has
B NOT SUBSET C.

For the latter case, every selected coatom C
(|C|+1=|A|) meeting Q also satisfies C NOT SUBSET B,
since B is itself a proper subalphabet of A and
C is maximal proper. Therefore the intersection
D=B∩C is properly contained in BOTH B and C.

The strict D⊊C condition is precisely what is needed
to apply the LOWER C-rank embedded/bridge-free coset
extension and lower-rank cluster-minimum induction
in the source's Lemma 4.3.

This proof uses the ACTUAL old-component-tagged support
of a vertex and its GENUINE signed B-path from Q's root.
It does not infer component membership from equality
of ambient group coordinates.

No global cluster-property theorem or source-local
retractability is assumed; the absence of all
large supports is an EXPLICIT off-skeleton branch
hypothesis, as in the published case distinction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- In the source's *non-full-B-coset* branch, any true
component-tagged maximal C-constituent slice of the
chosen B-component has an overlap alphabet D=B∩C
strictly below BOTH B and C.

The proper-subalphabet hypotheses are literal, and
the original support obstruction is tested only at
the fixed B-component anchor, then transported along
a true signed B-path via the accepted invariant. -/
theorem allProperCoset_noLarge_coatom_slice_both_inter_strict
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoLarge :
      ∀ (E : Finset ι)
        (hEP : E ∈ (allProperCosetFamily A).alphabets),
        B ⊆ E →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret E anchor)
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCcard : C.card + 1 = A.card)
    (c : K.ComponentIndex C)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hy :
      y ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c) :
    (B ∩ C) ⊂ B ∧ (B ∩ C) ⊂ C := by
  let P := allProperCosetFamily A
  obtain ⟨hReach, p, _hTag, hp⟩ := hy
  have hCY :
      K.MultiCosetVertexSupported P hadm hgen hret C y :=
    ⟨hCP, p, hp.symm⟩
  have hBNotC : ¬ B ⊆ C := by
    intro hBC
    have hCAnchor :
        K.MultiCosetVertexSupported P hadm hgen hret C anchor :=
      (K.multiCoset_selected_superset_support_invariant
        P hadm hgen hret B C hBC anchor y hReach).mpr hCY
    exact hNoLarge C hCP hBC hCAnchor
  have hCNotB : ¬ C ⊆ B := by
    intro hCB
    have hBCeq : B = C :=
      allProperCoset_coatom_maximal A C hCcard B hBP hCB
    exact hBNotC hBCeq.le
  constructor
  · refine ⟨Finset.inter_subset_left, ?_⟩
    intro hBInter
    apply hBNotC
    intro x hx
    exact (Finset.mem_inter.mp (hBInter hx)).2
  · refine ⟨Finset.inter_subset_right, ?_⟩
    intro hCInter
    apply hCNotB
    intro x hx
    exact (Finset.mem_inter.mp (hCInter hx)).1

/-- Under the same genuine off-skeleton cluster-branch
hypotheses, the overlap alphabet D=B∩C is an ACTUAL
selected proper alphabet of the lower C-extension.

This is the exact rank-drop precondition of source
Lemma 4.3's lower induction, not an additional
mathematical assumption. -/
theorem allProperCoset_noLarge_coatom_lower_alphabet
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoLarge :
      ∀ (E : Finset ι)
        (hEP : E ∈ (allProperCosetFamily A).alphabets),
        B ⊆ E →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret E anchor)
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCcard : C.card + 1 = A.card)
    (c : K.ComponentIndex C)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hy :
      y ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c) :
    B ∩ C ∈ (allProperCosetFamily C).alphabets := by
  have hDC :=
    (K.allProperCoset_noLarge_coatom_slice_both_inter_strict
      hadm hgen hret B hBP anchor hNoLarge
      C hCP hCcard c y hy).2
  exact (mem_allProperCosetFamily C (B ∩ C)).mpr hDC

end CayleySubgraphSpec
end ABO
end PSTSEPPA
