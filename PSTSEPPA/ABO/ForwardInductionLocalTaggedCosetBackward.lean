import PSTSEPPA.ABO.ForwardInductionLocalTaggedCosetMembership

/-!
# ABO Theorem 4.5: backward lift of the *new* tagged coset points

The accepted original/local signed skeleton map is bijective on OLD
vertices and REAL oriented signed OLD edges. But Theorem 4.5
needs to compare the newly attached full D-coset vertices, too.

The forward tagged-coset membership theorem checks that a local
D-attached point (D ⊆ C) left-translates into the corresponding
ORIGINAL rooted C-stage D-coset with its genuine old component tag.
We now prove the converse without pretending the whole ambient
group Γ is isomorphic to Γ[C].

If y is an ambient point in the full original D-coset of the
translated local group element u, then the signed displacement
(g·u)^(-1) y belongs to Γ[D] ⊆ Γ[C]. Consequently g^(-1)y
is a GENUINE element of Γ[C]; this is the UNIQUE local
coordinate v such that g·v=y. The source-local full D-coset
membership equivalence then gives v's true D-support.

Inducting on the ACTUAL original intrinsic D-component quotient
tag produces full backward attached-coset compatibility for
EVERY selected D ⊆ C, including empty D and inverse/trivial
generators, with no new axiom or fake old edge.

This is one of the two necessary halves of an eventual
COMPONENT-TAGGED attached-coset bijection on the proper C-family.
It does not assert compatibility on alphabets D not contained
in C; those are NOT the selected constituents of the proper
C-stage and such a blanket assertion is generally invalid
because generators outside C act as the identity locally.
The complete signed coset-extension gluing and edge transport
remain separate source Theorem-4.5 obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Root-normalized surjectivity on ONE actual translated D-left-coset.
No ambient group coordinate is picked by a quotient trick: the local
preimage is concretely g⁻¹*y and lies in Γ[C] because D⊆C.

The result does NOT claim that all elements of ambient Γ belong to
the translated local subgroup, only those in the specified D-coset. -/
theorem exists_localPoint_of_mem_rootTranslated_leftCoset
    (gen : ι → Γ)
    (D C : Finset ι) (hDC : D ⊆ C)
    (g : Γ)
    (u : generatedSubgroup gen C)
    (y : Γ)
    (hy : y ∈ generatedLeftCoset gen D (g * (u : Γ))) :
    ∃ v : generatedSubgroup gen C,
      v ∈ generatedLeftCoset
        (trivialCompletionGenerator gen C) D u ∧
      g * (v : Γ) = y := by
  have hD :
      (g * (u : Γ))⁻¹ * y ∈ generatedSubgroup gen D := hy
  obtain ⟨w, hwD, hEval⟩ :=
    exists_word_uses_eq_of_mem_generatedSubgroup gen D hD
  have hC :
      (g * (u : Γ))⁻¹ * y ∈ generatedSubgroup gen C := by
    rw [← hEval]
    exact evalGroup_mem_generatedSubgroup_of_uses
      gen C (hwD.mono hDC)
  have hFactor :
      g⁻¹ * y = (u : Γ) * ((g * (u : Γ))⁻¹ * y) := by
    group
  have hNorm : g⁻¹ * y ∈ generatedSubgroup gen C := by
    rw [hFactor]
    exact (generatedSubgroup gen C).mul_mem u.2 hC
  let v : generatedSubgroup gen C := ⟨g⁻¹ * y, hNorm⟩
  have hv : g * (v : Γ) = y := by
    dsimp [v]
    group
  refine ⟨v, ?_, hv⟩
  apply (mem_rootTranslated_localGeneratedLeftCoset_iff
    gen D C hDC g u v).mpr
  simpa only [hv] using hy

variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact BACKWARD compatibility of every true original rooted
C-stage attached D-coset, for D⊆C, with the normalized local
group's component-tagged D-attachment.

The old component-tag index is transported via the genuine
signed graph quotient isomorphism, and all newly attached
ambient points receive honest local preimages.

The BOTTOM and full-C alphabets are included for convenience;
no statement about D outside C is made. -/
theorem intrinsicComponentLocal_attachedCosetBackward
    (C D : Finset ι) (hDC : D ⊆ C)
    (root : K.Vertex)
    (c : (K.intrinsicComponentLocalSlice C root).ComponentIndex D)
    (y : Γ)
    (hy :
      y ∈ (K.subalphabetComponentSubgraph C root).componentAmbientCoset
        D (K.intrinsicComponentLocalIndexEquiv C D root c)) :
    ∃ v : generatedSubgroup gen C,
      v ∈ (K.intrinsicComponentLocalSlice C root).componentAmbientCoset D c ∧
      root.1 * (v : Γ) = y := by
  induction c using Quotient.inductionOn with
  | h x =>
      have hFull :
          y ∈ generatedLeftCoset gen D (root.1 * (x.1 : Γ)) := by
        change
          y ∈ generatedLeftCoset gen D
            ((K.intrinsicComponentLocalHom C root).onVertex x).1 at hy
        change y ∈ generatedLeftCoset gen D (root.1 * (x.1 : Γ)) at hy
        exact hy
      obtain ⟨v, hv, hval⟩ :=
        exists_localPoint_of_mem_rootTranslated_leftCoset
          gen D C hDC root.1 x.1 y hFull
      refine ⟨v, ?_, hval⟩
      change v ∈ generatedLeftCoset
        (trivialCompletionGenerator gen C) D x.1
      exact hv

end CayleySubgraphSpec
end ABO
end PSTSEPPA
