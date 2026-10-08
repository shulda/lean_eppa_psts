import PSTSEPPA.ABO.MultiCosetRawEdges

/-!
# Inversion and ambient rigidity of raw multi-coset edge tokens

Before identifying directed edges in CE(G,K;P), we check the exact
formal-inversion calculus on the alphabet-tagged disjoint union of
single-coset edge sets. Every raw edge has an inverse token in its own
alphabet summand; inversion is fixed-point-free, has order two, reverses
the signed label, and interchanges the glued source and target.

The ambient Cayley edge is a projection, not an identification map.
However, equality of *glued sources* and signed labels forces equality
of ambient Cayley edges by determinism. This does not yet imply equality
of glued targets. The latter is the substantive congruence obligation
needed before quotienting edge tokens (ABO 3.10/Proposition 3.18).
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Formal inversion of raw multi-coset edge tokens is involutive. -/
theorem multiCosetRawEdgeInv_inv
    (P : CosetFamilySpec A) (e : K.MultiCosetRawEdge P) :
    K.multiCosetRawEdgeInv P (K.multiCosetRawEdgeInv P e) = e := by
  rcases e with ⟨B, e⟩
  change
    (⟨B, K.singleCosetInv B.1 (K.singleCosetInv B.1 e)⟩ :
      K.MultiCosetRawEdge P) = ⟨B, e⟩
  rw [K.singleCosetInv_inv]

/-- Raw inversion reverses the signed label, not just the underlying
unsigned generator. -/
theorem multiCosetRawEdgeLabel_inv
    (P : CosetFamilySpec A) (e : K.MultiCosetRawEdge P) :
    K.multiCosetRawEdgeLabel P (K.multiCosetRawEdgeInv P e) =
      PSTS.SignedLetter.inv (K.multiCosetRawEdgeLabel P e) := by
  rcases e with ⟨B, e⟩
  exact K.singleCosetLabel_inv B.1 e

/-- Formal reversal is fixed-point-free even when the Cayley edge is
a geometric loop or the corresponding group generator is trivial. -/
theorem multiCosetRawEdgeInv_ne
    (P : CosetFamilySpec A) (e : K.MultiCosetRawEdge P) :
    K.multiCosetRawEdgeInv P e ≠ e := by
  intro heq
  have hs := congrArg (K.multiCosetRawEdgeLabel P) heq
  rw [K.multiCosetRawEdgeLabel_inv P e] at hs
  cases hletter : K.multiCosetRawEdgeLabel P e with
  | pos i =>
      rw [hletter] at hs
      cases hs
  | neg i =>
      rw [hletter] at hs
      cases hs

/-- Source of the reversed raw edge is the original target in the
already-glued vertex quotient. -/
theorem multiCosetRawEdgeSource_inv
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetRawEdge P) :
    K.multiCosetRawEdgeSource P hadm hgen hret
        (K.multiCosetRawEdgeInv P e) =
      K.multiCosetRawEdgeTarget P hadm hgen hret e := by
  rcases e with ⟨B, e⟩
  rfl

/-- Target of the reversed raw edge is the original source. -/
theorem multiCosetRawEdgeTarget_inv
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetRawEdge P) :
    K.multiCosetRawEdgeTarget P hadm hgen hret
        (K.multiCosetRawEdgeInv P e) =
      K.multiCosetRawEdgeSource P hadm hgen hret e := by
  rw [← K.multiCosetRawEdgeSource_inv P hadm hgen hret
    (K.multiCosetRawEdgeInv P e)]
  rw [K.multiCosetRawEdgeInv_inv P e]

/-- Ambient Cayley projection respects *formal* edge reversal. -/
theorem multiCosetRawEdgeAmbient_inv
    (P : CosetFamilySpec A) (e : K.MultiCosetRawEdge P) :
    K.multiCosetRawEdgeAmbient P (K.multiCosetRawEdgeInv P e) =
      (cayleyGraph gen).inv (K.multiCosetRawEdgeAmbient P e) := by
  rcases e with ⟨B, e⟩
  exact (K.singleCosetAmbientHom B.1).map_inv e

/-- Equal glued source and signed label force the raw edges to have
the same ambient Cayley projection, although they may still be distinct
raw tokens or have as-yet-unidentified tagged targets. -/
theorem multiCosetRawEdgeAmbient_eq_of_source_label
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e f : K.MultiCosetRawEdge P)
    (hsource :
      K.multiCosetRawEdgeSource P hadm hgen hret e =
        K.multiCosetRawEdgeSource P hadm hgen hret f)
    (hlabel :
      K.multiCosetRawEdgeLabel P e =
        K.multiCosetRawEdgeLabel P f) :
    K.multiCosetRawEdgeAmbient P e =
      K.multiCosetRawEdgeAmbient P f := by
  apply (cayleyGraph gen).toEGraph.deterministic
  · rw [K.multiCosetRawEdgeAmbient_source P hadm hgen hret e,
      K.multiCosetRawEdgeAmbient_source P hadm hgen hret f]
    exact congrArg (K.multiCosetAmbientValue P hadm hgen hret) hsource
  · rw [K.multiCosetRawEdgeAmbient_label P e,
      K.multiCosetRawEdgeAmbient_label P f]
    exact hlabel

/-- Necessary ambient-target equality for any putative multi-coset
edge identification by glued source and signed label. The remaining
gate is equality *inside the vertex quotient*, not the ambient group. -/
theorem multiCosetRawEdgeTarget_ambient_eq_of_source_label
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e f : K.MultiCosetRawEdge P)
    (hsource :
      K.multiCosetRawEdgeSource P hadm hgen hret e =
        K.multiCosetRawEdgeSource P hadm hgen hret f)
    (hlabel :
      K.multiCosetRawEdgeLabel P e =
        K.multiCosetRawEdgeLabel P f) :
    K.multiCosetAmbientValue P hadm hgen hret
        (K.multiCosetRawEdgeTarget P hadm hgen hret e) =
      K.multiCosetAmbientValue P hadm hgen hret
        (K.multiCosetRawEdgeTarget P hadm hgen hret f) := by
  have h := congrArg (cayleyGraph gen).target
    (K.multiCosetRawEdgeAmbient_eq_of_source_label
      P hadm hgen hret e f hsource hlabel)
  rw [K.multiCosetRawEdgeAmbient_target P hadm hgen hret e,
      K.multiCosetRawEdgeAmbient_target P hadm hgen hret f] at h
  exact h

end CayleySubgraphSpec
end ABO
end PSTSEPPA
