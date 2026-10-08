import PSTSEPPA.ABO.MultiCosetVertexQuotient
import PSTSEPPA.ABO.SingleCosetEGraph

/-!
# Raw directed edges for the multi-alphabet coset extension

Before quotienting directed edge tokens, form a disjoint union of the
single-B coset-extension edges for the chosen family of alphabets.
Every raw edge has a canonical source and target in the *already glued*
multi-coset vertex quotient, a signed label, and an ambient Cayley edge.

This representation is deliberately not an E-graph yet: different
alphabet summands may describe the same outgoing edge, and these tokens
must be identified only after checking compatibility of formal reversal.
In particular, using only the ambient group edge as its identity would
prematurely collapse distinct component-tagged copies.

The definitions below are the source-level interface for the remaining
directed-edge gluing and Proposition 3.18. The separately tagged edge
universe is intentionally retained until congruence under reversal and
source/target identification has been established.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Disjoint union of directed edge tokens of all selected
single-alphabet coset extensions. -/
abbrev MultiCosetRawEdge (P : CosetFamilySpec A) :=
  Σ B : {B : Finset ι // B ∈ P.alphabets},
    K.SingleCosetEdge B.1

/-- Canonical source of a raw edge in the glued vertex quotient. -/
noncomputable def multiCosetRawEdgeSource
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetRawEdge P) :
    K.MultiCosetVertex P hadm hgen hret :=
  K.multiCosetInclude P hadm hgen hret e.1.1 e.1.2
    ((K.singleCosetEGraph e.1.1).source e.2)

/-- Canonical target in the glued vertex quotient. -/
noncomputable def multiCosetRawEdgeTarget
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetRawEdge P) :
    K.MultiCosetVertex P hadm hgen hret :=
  K.multiCosetInclude P hadm hgen hret e.1.1 e.1.2
    ((K.singleCosetEGraph e.1.1).target e.2)

/-- Its signed label is the label from the constituent E-graph. -/
noncomputable def multiCosetRawEdgeLabel
    (P : CosetFamilySpec A)
    (e : K.MultiCosetRawEdge P) : SignedLabel ι :=
  (K.singleCosetEGraph e.1.1).label e.2

/-- The ambient Cayley edge is a *projection* only; this coordinate
is not globally injective on the raw edge universe. -/
noncomputable def multiCosetRawEdgeAmbient
    (P : CosetFamilySpec A)
    (e : K.MultiCosetRawEdge P) : ActionEdge Γ ι :=
  (K.singleCosetAmbientHom e.1.1).onEdge e.2

/-- Raw edge reversal stays inside its alphabet summand. -/
noncomputable def multiCosetRawEdgeInv
    (P : CosetFamilySpec A)
    (e : K.MultiCosetRawEdge P) : K.MultiCosetRawEdge P :=
  ⟨e.1, K.singleCosetInv e.1.1 e.2⟩

/-- The ambient edge of a raw token has the same source as its
multi-coset source after applying the canonical ambient projection. -/
theorem multiCosetRawEdgeAmbient_source
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetRawEdge P) :
    (cayleyGraph gen).source (K.multiCosetRawEdgeAmbient P e) =
      K.multiCosetAmbientValue P hadm hgen hret
        (K.multiCosetRawEdgeSource P hadm hgen hret e) := by
  rcases e with ⟨B, e⟩
  exact (K.singleCosetAmbientHom B.1).map_source e

/-- The signed label likewise survives projection into the ambient
Cayley graph, including labels for geometric loops. -/
theorem multiCosetRawEdgeAmbient_label
    (P : CosetFamilySpec A)
    (e : K.MultiCosetRawEdge P) :
    (cayleyGraph gen).label (K.multiCosetRawEdgeAmbient P e) =
      K.multiCosetRawEdgeLabel P e := by
  rcases e with ⟨B, e⟩
  exact (K.singleCosetAmbientHom B.1).map_label e

/-- The target of the projected ambient edge equals the projected
multi-coset target. -/
theorem multiCosetRawEdgeAmbient_target
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetRawEdge P) :
    (cayleyGraph gen).target (K.multiCosetRawEdgeAmbient P e) =
      K.multiCosetAmbientValue P hadm hgen hret
        (K.multiCosetRawEdgeTarget P hadm hgen hret e) := by
  rcases e with ⟨B, e⟩
  exact (K.singleCosetAmbientHom B.1).map_target e

end CayleySubgraphSpec
end ABO
end PSTSEPPA
