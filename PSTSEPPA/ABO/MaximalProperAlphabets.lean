import PSTSEPPA.ABO.MultiCosetMaximalConstituentExit
import PSTSEPPA.ABO.StandardCosetFamily

/-!
# Coatom alphabets are maximal proper selected constituents

The source's higher-rank induction uses maximal proper subalphabets
C of A. In the finite full proper-subalphabet family, the
combinatorial test |C|+1=|A| suffices to establish maximality:
any strict C⊊E⊊A would force an impossible intervening cardinal.

This provides a source-friendly way of discharging the explicit
maximality assumption in the certified exact boundary-exit lemma.
The only remaining size restriction for the exit result is C≠∅,
corresponding to the intended |A|≥2 range.

The statement is valid at any rank and does not assume
retractability in its combinatorial part.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- If C has codimension one in the finite alphabet A,
it is maximal among the selected proper subalphabets of A. -/
theorem allProperCoset_coatom_maximal
    (A C : Finset ι) (hcard : C.card + 1 = A.card) :
    ∀ (E : Finset ι)
      (_hEP : E ∈ (allProperCosetFamily A).alphabets),
      C ⊆ E → E = C := by
  intro E hEP hCE
  by_contra hneq
  have hStrict : C ⊂ E := by
    refine ⟨hCE, ?_⟩
    intro hEC
    exact hneq (Finset.Subset.antisymm hEC hCE)
  have hCltE : C.card < E.card := Finset.card_lt_card hStrict
  have hEltA : E.card < A.card :=
    Finset.card_lt_card ((mem_allProperCosetFamily A E).mp hEP)
  have hAleE : A.card ≤ E.card := by
    calc
      A.card = C.card + 1 := hcard.symm
      _ ≤ E.card := Nat.succ_le_iff.mpr hCltE
  exact (not_lt_of_ge hAleE) hEltA

variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- For a nonempty codimension-one C⊊A, any edge exiting the
set of C-supported quotient vertices already starts at a
point with real component-tagged support D⊊C.

The coatom cardinality hypothesis automatically discharges
the maximality condition required by the lower-rank boundary
lemma; no global cluster property is needed. -/
theorem allProperCoset_coatom_exit_step_lower
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCnonempty : C.Nonempty)
    (hcard : C.card + 1 = A.card)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (hSourceC :
      K.MultiCosetVertexSupported (allProperCosetFamily A)
        hadm hgen hret C
        ((K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).source e))
    (hTargetOff :
      ¬ K.MultiCosetVertexSupported (allProperCosetFamily A)
        hadm hgen hret C
        ((K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).target e)) :
    ∃ D : Finset ι,
      D ⊂ C ∧
      K.MultiCosetVertexSupported (allProperCosetFamily A)
        hadm hgen hret D
        ((K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).source e) := by
  exact K.allProperCoset_maximal_support_exit_step_lower
    hadm hgen hret C hCP hCnonempty
    (allProperCoset_coatom_maximal A C hcard)
    e hSourceC hTargetOff

end CayleySubgraphSpec
end ABO
end PSTSEPPA
