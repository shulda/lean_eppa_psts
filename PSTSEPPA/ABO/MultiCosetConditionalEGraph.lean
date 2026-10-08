import PSTSEPPA.ABO.MultiCosetEdgeQuotient
import PSTSEPPA.ABO.MultiCosetRawEdgeInversion

/-!
# The final multi-coset E-graph conditional on target congruence

We isolate precisely the last missing geometric gluing lemma:

  if two raw directed edges have the same *glued* source and signed
  label, their targets must be equal in the glued vertex quotient.

Assuming this, formal reversal descends to the source-label edge
quotient, remains a fixed-point-free involution, and produces a fully
deterministic E-graph. No completeness hypothesis or injectivity of
the canonical ambient-group projection is required.

This module does not assume the target-congruence lemma as an axiom:
it takes an explicit Prop parameter that will later be discharged by
the three inside/old edge case splits. The resulting E-graph is a
conditional theorem, not yet an unconditional coset-extension
construction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The exact missing edge gluing condition. This is stronger than
ambient target equality, which follows automatically from
source-and-label equality but is insufficient to glue component tags. -/
def MultiCosetTargetCongruent
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) : Prop :=
  ∀ e f : K.MultiCosetRawEdge P,
    K.MultiCosetRawEdgeRelated P hadm hgen hret e f →
    K.multiCosetRawEdgeTarget P hadm hgen hret e =
      K.multiCosetRawEdgeTarget P hadm hgen hret f

/-- Once target congruence is given, formal reversal descends to the
edge quotient. -/
noncomputable def multiCosetEdgeQuotientInv
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcongr : K.MultiCosetTargetCongruent P hadm hgen hret)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret :=
  Quotient.liftOn e
    (fun raw => Quotient.mk (K.multiCosetRawEdgeSetoid P hadm hgen hret)
      (K.multiCosetRawEdgeInv P raw))
    (by
      intro e f hef
      apply Quotient.sound
      change K.MultiCosetRawEdgeRelated P hadm hgen hret
        (K.multiCosetRawEdgeInv P e) (K.multiCosetRawEdgeInv P f)
      constructor
      · rw [K.multiCosetRawEdgeSource_inv P hadm hgen hret e,
          K.multiCosetRawEdgeSource_inv P hadm hgen hret f]
        exact hcongr e f hef
      · rw [K.multiCosetRawEdgeLabel_inv P e,
          K.multiCosetRawEdgeLabel_inv P f]
        exact congrArg PSTS.SignedLetter.inv hef.2)

@[simp]
theorem multiCosetEdgeQuotientInv_mk
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcongr : K.MultiCosetTargetCongruent P hadm hgen hret)
    (e : K.MultiCosetRawEdge P) :
    K.multiCosetEdgeQuotientInv P hadm hgen hret hcongr
      (Quotient.mk (K.multiCosetRawEdgeSetoid P hadm hgen hret) e) =
    Quotient.mk (K.multiCosetRawEdgeSetoid P hadm hgen hret)
      (K.multiCosetRawEdgeInv P e) :=
  rfl

/-- Formal reversal on edge classes is involutive. -/
theorem multiCosetEdgeQuotientInv_inv
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcongr : K.MultiCosetTargetCongruent P hadm hgen hret)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    K.multiCosetEdgeQuotientInv P hadm hgen hret hcongr
      (K.multiCosetEdgeQuotientInv P hadm hgen hret hcongr e) = e := by
  induction e using Quotient.inductionOn with
  | h e =>
    simp only [K.multiCosetEdgeQuotientInv_mk,
      K.multiCosetRawEdgeInv_inv]
    rfl

/-- Formal reversal on edge classes has no fixed points. -/
theorem multiCosetEdgeQuotientInv_ne
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcongr : K.MultiCosetTargetCongruent P hadm hgen hret)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    K.multiCosetEdgeQuotientInv P hadm hgen hret hcongr e ≠ e := by
  induction e using Quotient.inductionOn with
  | h e =>
    intro heq
    have hlabel := congrArg
      (K.multiCosetEdgeQuotientLabel P hadm hgen hret) heq
    change
      K.multiCosetRawEdgeLabel P (K.multiCosetRawEdgeInv P e) =
        K.multiCosetRawEdgeLabel P e at hlabel
    rw [K.multiCosetRawEdgeLabel_inv P e] at hlabel
    cases hs : K.multiCosetRawEdgeLabel P e with
    | pos i =>
        rw [hs] at hlabel
        cases hlabel
    | neg i =>
        rw [hs] at hlabel
        cases hlabel

/-- The signed label of formal reversal is its signed inverse. -/
theorem multiCosetEdgeQuotientLabel_inv
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcongr : K.MultiCosetTargetCongruent P hadm hgen hret)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    K.multiCosetEdgeQuotientLabel P hadm hgen hret
        (K.multiCosetEdgeQuotientInv P hadm hgen hret hcongr e) =
      PSTS.SignedLetter.inv
        (K.multiCosetEdgeQuotientLabel P hadm hgen hret e) := by
  induction e using Quotient.inductionOn with
  | h e =>
    exact K.multiCosetRawEdgeLabel_inv P e

/-- Conditional multi-alphabet labelled graph, including two distinct
directed tokens for each geometric loop. -/
noncomputable def multiCosetQuotientLabelledGraph
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcongr : K.MultiCosetTargetCongruent P hadm hgen hret) :
    LabelledGraph
      (K.MultiCosetVertex P hadm hgen hret)
      (K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) ι where
  source := K.multiCosetEdgeQuotientSource P hadm hgen hret
  inv := K.multiCosetEdgeQuotientInv P hadm hgen hret hcongr
  inv_inv := K.multiCosetEdgeQuotientInv_inv P hadm hgen hret hcongr
  inv_ne := K.multiCosetEdgeQuotientInv_ne P hadm hgen hret hcongr
  label := K.multiCosetEdgeQuotientLabel P hadm hgen hret
  label_inv := K.multiCosetEdgeQuotientLabel_inv P hadm hgen hret hcongr

/-- The source-and-label quotient is deterministic as soon as the
edge reversal is well-defined. Distinct raw presentations of one
outgoing labelled edge automatically collapse. -/
noncomputable def multiCosetQuotientEGraph
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcongr : K.MultiCosetTargetCongruent P hadm hgen hret) :
    EGraph
      (K.MultiCosetVertex P hadm hgen hret)
      (K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) ι where
  toLabelledGraph :=
    K.multiCosetQuotientLabelledGraph P hadm hgen hret hcongr
  deterministic := by
    intro e f hsource hlabel
    induction e using Quotient.inductionOn with
    | h e =>
      induction f using Quotient.inductionOn with
      | h f =>
        apply Quotient.sound
        exact ⟨hsource, hlabel⟩

/-- The target of the edge class represented by a raw edge equals
that raw edge's source-formally-inverted target in the vertex quotient. -/
theorem multiCosetQuotient_target_mk
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcongr : K.MultiCosetTargetCongruent P hadm hgen hret)
    (e : K.MultiCosetRawEdge P) :
    (K.multiCosetQuotientEGraph P hadm hgen hret hcongr).target
      (Quotient.mk (K.multiCosetRawEdgeSetoid P hadm hgen hret) e) =
    K.multiCosetRawEdgeTarget P hadm hgen hret e := by
  change
    K.multiCosetRawEdgeSource P hadm hgen hret
      (K.multiCosetRawEdgeInv P e) =
    K.multiCosetRawEdgeTarget P hadm hgen hret e
  exact K.multiCosetRawEdgeSource_inv P hadm hgen hret e

end CayleySubgraphSpec
end ABO
end PSTSEPPA
