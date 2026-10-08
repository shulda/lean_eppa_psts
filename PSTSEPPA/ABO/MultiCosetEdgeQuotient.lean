import PSTSEPPA.ABO.MultiCosetRawEdgeInversion

/-!
# Source-and-label quotient of raw multi-coset edge tokens

Every single-alphabet E-graph is deterministic. For the multi-alphabet
extension, two raw directed edge tokens are candidates for identification
exactly when their sources agree *in the checked vertex quotient* and
their signed labels agree.

This is an equivalence relation before any assertion about targets.
We construct the resulting edge-token quotient, show its source,
signed label and ambient Cayley projection are well-defined, and prove
that each individual single-alphabet edge set injects into it.

Crucial scope: we have NOT YET shown that target or formal reversal
descends to this quotient. Doing so requires the target-congruence lemma:
equal glued sources and signed labels imply equal glued targets.
Until that lemma is proved, the quotient below is intentionally not
called a LabelledGraph or EGraph.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Candidate identification of raw directed edge tokens in the
multi-alphabet extension: equal glued source and equal signed label. -/
def MultiCosetRawEdgeRelated
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e f : K.MultiCosetRawEdge P) : Prop :=
  K.multiCosetRawEdgeSource P hadm hgen hret e =
    K.multiCosetRawEdgeSource P hadm hgen hret f ∧
  K.multiCosetRawEdgeLabel P e =
    K.multiCosetRawEdgeLabel P f

/-- The source-and-label relation is an equivalence relation.
Transitivity here is elementary because the gluing of vertices
has already been formalized; it does not yet prove edge inversion
is compatible with this relation. -/
def multiCosetRawEdgeSetoid
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Setoid (K.MultiCosetRawEdge P) where
  r := K.MultiCosetRawEdgeRelated P hadm hgen hret
  iseqv := {
    refl := fun _ => ⟨rfl, rfl⟩
    symm := fun h => ⟨h.1.symm, h.2.symm⟩
    trans := fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  }

/-- Edge-token quotient by the proposed incidence-and-label relation.
This is a type, not yet a labelled graph. -/
def MultiCosetEdgeVertexIncidenceQuotient
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  Quotient (K.multiCosetRawEdgeSetoid P hadm hgen hret)

/-- Source descends to the quotient by construction. -/
noncomputable def multiCosetEdgeQuotientSource
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    K.MultiCosetVertex P hadm hgen hret :=
  Quotient.liftOn e
    (K.multiCosetRawEdgeSource P hadm hgen hret)
    (by
      intro e f hef
      exact hef.1)

/-- The signed label descends to the quotient by construction. -/
noncomputable def multiCosetEdgeQuotientLabel
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    SignedLabel ι :=
  Quotient.liftOn e
    (K.multiCosetRawEdgeLabel P)
    (by
      intro e f hef
      exact hef.2)

/-- The ambient Cayley edge also descends; no injectivity of this
projection is asserted or required. -/
noncomputable def multiCosetEdgeQuotientAmbient
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    ActionEdge Γ ι :=
  Quotient.liftOn e
    (K.multiCosetRawEdgeAmbient P)
    (by
      intro e f hef
      exact K.multiCosetRawEdgeAmbient_eq_of_source_label
        P hadm hgen hret e f hef.1 hef.2)

/-- Include the single-B extension's directed edges in the
source-and-label quotient. -/
def multiCosetEdgeInclude
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (e : K.SingleCosetEdge B) :
    K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret :=
  Quotient.mk (K.multiCosetRawEdgeSetoid P hadm hgen hret)
    (⟨⟨B, hBP⟩, e⟩ : K.MultiCosetRawEdge P)

/-- Each individual constituent E-graph embeds on its directed edges
in this quotient; no two of its edges with distinct source or signed
label become identified. -/
theorem multiCosetEdgeInclude_injective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    Function.Injective
      (K.multiCosetEdgeInclude P hadm hgen hret B hBP) := by
  intro e f hef
  have hrel := Quotient.exact hef
  change
    K.MultiCosetRawEdgeRelated P hadm hgen hret
      (⟨⟨B, hBP⟩, e⟩ : K.MultiCosetRawEdge P)
      (⟨⟨B, hBP⟩, f⟩ : K.MultiCosetRawEdge P) at hrel
  apply (K.singleCosetEGraph B).deterministic
  · exact K.multiCosetInclude_injective P hadm hgen hret B hBP hrel.1
  · exact hrel.2

end CayleySubgraphSpec
end ABO
end PSTSEPPA
