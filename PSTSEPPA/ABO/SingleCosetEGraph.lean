import PSTSEPPA.ABO.SingleCosetExtension

/-!
# Determinism of the single-B coset extension

The tagged-copy representation of CE(G,K;B) is an ABO E-graph:
at each source there is at most one outgoing edge with any fixed signed
label. For labels in B the unique edge is from the attached full coset;
for other labels any edge must come from the original deterministic
skeleton.

In particular, the outside-B and inside-B edges cannot collide, even when
a generator acts trivially or distinct labels induce the same permutation.
The graph need not be complete outside B.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The tagged single-B coset extension is deterministic as an E-graph. -/
noncomputable def singleCosetEGraph (B : Finset ι) :
    EGraph (K.AttachedCosetVertex B) (K.SingleCosetEdge B) ι where
  toLabelledGraph := K.singleCosetLabelledGraph B
  deterministic := by
    intro e f hs hl
    cases e with
    | inl e =>
      cases f with
      | inl f =>
        have hsrc : e.1.1.1 = f.1.1.1 := by
          have h := congrArg (K.attachedValue B) hs
          exact h
        have hlabel : e.1.1.2 = f.1.1.2 := hl
        have hraw : e.1.1 = f.1.1 :=
          Prod.ext hsrc hlabel
        apply congrArg Sum.inl
        apply Subtype.ext
        apply Subtype.ext
        exact hraw
      | inr f =>
        have heq : e.1.1.2 = f.2.1 := hl
        have hmem : signedBase e.1.1.2 ∈ B := by
          rw [heq]
          exact f.2.2
        exact (e.2 hmem).elim
    | inr e =>
      cases f with
      | inl f =>
        have heq : e.2.1 = f.1.1.2 := hl
        have hmem : signedBase f.1.1.2 ∈ B := by
          rw [← heq]
          exact e.2.2
        exact (f.2 hmem).elim
      | inr f =>
        have hsrc : e.1 = f.1 := hs
        have hlabel : e.2.1 = f.2.1 := hl
        apply congrArg Sum.inr
        exact Prod.ext hsrc (Subtype.ext hlabel)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
