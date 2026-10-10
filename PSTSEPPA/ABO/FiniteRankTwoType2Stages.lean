import PSTSEPPA.ABO.RankTwoOffComponentCompletedStage
import PSTSEPPA.ABO.FiniteActionStages
import Mathlib.Data.Fintype.Quotient

/-!
# The genuine augmented full-coset stages are finite over a finite ambient group

Corrected ABO Section 5 builds finite transition groups out of a finite
family Z₁ of completed rank-two stages. It is not enough to show that
an arbitrary COMPLETE EGraph has a finite transition group when its
carrier is finite: the actual geometrically constructed quotient and
its augmented full-coset carrier must also be finite.

Here the ambient group Γ is assumed finite, precisely as in the finite
step of the source construction. Then:
* each original skeleton vertex belongs to the finite type Γ;
* each intrinsic C-component index is a quotient of a finite type;
* each component-tagged C-coset consists of a finite quotient tag
  and a finite Γ-point;
* the genuine glued all-proper multi-coset quotient is finite;
* the new singleton type-(2) full B-coset adds only finitely many
  fresh tagged Γ-points;
* hence the real completed type-(2) action has a finite carrier
  and its transition group is finite as a subgroup of Perm(V).

No choice of representatives, injection of the multi-CE into Γ,
stability, or reflecting-group existence is assumed. The result
only gives actual finiteness certificates needed to construct Z₁.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every intrinsic C-component of a skeleton over a finite group
is among finitely many components, despite being a genuine
signed-path equivalence class. -/
theorem finite_componentIndex (C : Finset ι) :
    Finite (K.ComponentIndex C) := by
  classical
  letI : Finite K.Vertex :=
    Finite.of_injective (fun x : K.Vertex => x.1)
      (fun _ _ h => Subtype.ext h)
  apply Finite.of_surjective (K.componentClass C)
  intro q
  induction q using Quotient.inductionOn with
  | h x => exact ⟨x, rfl⟩

/-- Component-tagged copies of ambient cosets are finite when
their ambient group Γ is finite. No global coset-map injectivity
is required. -/
theorem finite_attachedCosetVertex (C : Finset ι) :
    Finite (K.AttachedCosetVertex C) := by
  classical
  letI : Finite (K.ComponentIndex C) := K.finite_componentIndex C
  change Finite
    (Σ c : K.ComponentIndex C,
      {x : Γ // x ∈ K.componentAmbientCoset C c})
  infer_instance

/-- The genuine all-proper multi-coset vertex QUOTIENT is finite,
even though different tagged coset copies may overlap. -/
theorem finite_allProperMultiCosetVertex
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Finite (K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) := by
  classical
  let P := allProperCosetFamily A
  letI : Finite (K.MultiCosetRawVertex P) := by
    change Finite
      (Σ b : {B : Finset ι // B ∈ P.alphabets},
        K.AttachedCosetVertex b.1)
    exact @Finite.instSigma
      _ _ (inferInstance : Finite {B : Finset ι // B ∈ P.alphabets})
      (fun b => K.finite_attachedCosetVertex b.1)
  apply Finite.of_surjective
    (fun p : K.MultiCosetRawVertex P =>
      (Quotient.mk (K.multiCosetSetoid P hadm hgen hret) p :
        K.MultiCosetVertex P hadm hgen hret))
  intro q
  induction q using Quotient.inductionOn with
  | h p => exact ⟨p, rfl⟩

/-- The actual singleton-augmented full B-coset carrier is finite,
including the original multi-coset quotient and every fresh point. -/
theorem finite_rankTwoOffComponentCarrier
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret) :
    Finite (IsolatedCosetGluing.Vertex
      (K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret)
      gen B
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le)
        hgen hret z)) := by
  classical
  letI : Finite
      (K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret) :=
    K.finite_allProperMultiCosetVertex
      (K.admissible_of_card_le_two hcard.le) hgen hret
  change Finite
    ((K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret) ⊕
      {x : Γ //
        x ∈ generatedLeftCoset gen B
          (K.multiCosetAmbientValue (allProperCosetFamily A)
            (K.admissible_of_card_le_two hcard.le)
            hgen hret z) ∧
          x ≠ K.multiCosetAmbientValue (allProperCosetFamily A)
            (K.admissible_of_card_le_two hcard.le)
            hgen hret z})
  infer_instance

/-- Consequently, every actual legal type-(2) rank-two complete
stage has a FINITE labelled transition group. The proof applies
to the genuine stage object with all its component tags. -/
theorem finite_rankTwoOffComponent_transitionGroup
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret)
    (hOff : ¬ ∃ q : K.AttachedCosetVertex B,
      K.multiCosetInclude (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le)
        hgen hret B hBP q = z) :
    Finite (K.rankTwoOffComponentCompletedStage
      hcard hgen hret B hBP z hOff).transitionGroup := by
  classical
  letI : Finite
      (IsolatedCosetGluing.Vertex
        (K.MultiCosetVertex (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard.le) hgen hret)
        gen B
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard.le)
          hgen hret z)) :=
    K.finite_rankTwoOffComponentCarrier hcard hgen hret B z
  letI : Fintype
      (IsolatedCosetGluing.Vertex
        (K.MultiCosetVertex (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard.le) hgen hret)
        gen B
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard.le)
          hgen hret z)) := Fintype.ofFinite _
  exact (K.rankTwoOffComponentCompletedStage
    hcard hgen hret B hBP z hOff).finite_transitionGroup

end CayleySubgraphSpec
end ABO
end PSTSEPPA
