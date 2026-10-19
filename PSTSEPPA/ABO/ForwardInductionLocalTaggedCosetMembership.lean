import PSTSEPPA.ABO.ForwardInductionLocalSignedPathReflection
import PSTSEPPA.ABO.BijectiveTaggedCosetTransport
import PSTSEPPA.ABO.LocalSubgroupCosetNaturality

/-!
# ABO Theorem 4.5: exact local-to-original tagged coset membership

The paper's forward induction works with the *actual* subgroup H[C] for
an original rooted intrinsic C-component of an incomplete signed
Cayley skeleton. The already accepted source-local graph isomorphism
and signed D-path/component-index equivalences do NOT by themselves
transport the attached full D-cosets: those include new points not
present in the old skeleton.

We provide the first precise constituent-level transport gate.

For each D ⊆ C, membership of two honest local group coordinates
in the same left D-coset is equivalent to membership of their
left translates by the original rooted old coordinate in the
corresponding ambient left D-coset. This follows from the accepted
subgroup coset-naturalness theorem by cancellation of the fixed root.

Crucially, the comparison is also valid for EVERY original
component-index-tagged D-coset, rather than merely untagged
group cosets: use the exact signed original/local D-component
index equivalence, then quotient induction on the component tag.

As a consequence the genuine old-component-tagged attachment map
from the local normalized skeleton to the old rooted C-skeleton
has the precise forward-compatible coset-membership predicate
required by the separately certified generic
`BijectiveTaggedCosetTransport` API.

We do NOT yet claim the backward attached-coset surjectivity
or the full signed multi-coset quotient equivalence, which must
be proved separately using ambient left-translation and original
component tags. No global Cayley injectivity, artificial old
edge completion, global ambient retractability or extra axiom is used.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Translating both endpoints by the SAME original old root g
preserves and reflects membership in a left D-coset of the
actual generated local subgroup Γ[C], provided D ⊆ C.

This includes empty alphabets and inverse/trivial generators,
without any generation or retractability assumption on Γ. -/
theorem mem_rootTranslated_localGeneratedLeftCoset_iff
    (gen : ι → Γ)
    (D C : Finset ι) (hDC : D ⊆ C)
    (g : Γ)
    (u v : generatedSubgroup gen C) :
    v ∈ generatedLeftCoset
          (trivialCompletionGenerator gen C) D u ↔
      g * (v : Γ) ∈ generatedLeftCoset gen D (g * (u : Γ)) := by
  have hLocal :=
    mem_localGeneratedLeftCoset_iff_ambient gen D C hDC u v
  have hCancel :
      (g * (u : Γ))⁻¹ * (g * (v : Γ)) =
        (u : Γ)⁻¹ * (v : Γ) := by
    group
  change
    v ∈ generatedLeftCoset
      (trivialCompletionGenerator gen C) D u ↔
      (g * (u : Γ))⁻¹ * (g * (v : Γ)) ∈
        generatedSubgroup gen D
  rw [hCancel]
  exact hLocal

variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An arbitrary TRUE original/local D-component tag c,
not only a selected representative, determines exactly
corresponding full left D-cosets under the root-normalized
coordinate change.

The right-hand component tag is transported by the actual
bijection on intrinsic signed D-reachability quotients.
The left-hand value is a genuine local point of Γ[C].
The conclusion compares full coset *membership* including
attached new points, rather than paths in the old skeleton. -/
theorem intrinsicComponentLocalIndex_ambientCoset_mem_iff
    (C D : Finset ι) (hDC : D ⊆ C)
    (root : K.Vertex)
    (c : (K.intrinsicComponentLocalSlice C root).ComponentIndex D)
    (v : generatedSubgroup gen C) :
    v ∈ (K.intrinsicComponentLocalSlice C root).componentAmbientCoset
      D c ↔
    root.1 * (v : Γ) ∈
      (K.subalphabetComponentSubgraph C root).componentAmbientCoset
        D (K.intrinsicComponentLocalIndexEquiv C D root c) := by
  induction c using Quotient.inductionOn with
  | h x =>
      change v ∈
          generatedLeftCoset (trivialCompletionGenerator gen C) D x.1 ↔
        root.1 * (v : Γ) ∈
          generatedLeftCoset gen D
            ((K.intrinsicComponentLocalHom C root).onVertex x).1
      change v ∈
          generatedLeftCoset (trivialCompletionGenerator gen C) D x.1 ↔
        root.1 * (v : Γ) ∈
          generatedLeftCoset gen D (root.1 * (x.1 : Γ))
      exact mem_rootTranslated_localGeneratedLeftCoset_iff
        gen D C hDC root.1 x.1 v

/-- Source Theorem 4.5 forward attached-coset membership.

The true root-normalized local signed skeleton's D-tagged
coset transports into the corresponding original rooted
C-component's D-tagged full coset by the genuine ambient
coordinate change x ↦ root·x.

The signed-graph vertex/edge bijections and intrinsic
component-index equivalences are already certified, and
the condition here holds for EVERY D ⊆ C, including D=∅.
No fake global ambient group isomorphism is assumed. -/
theorem intrinsicComponentLocal_attachedCosetForward
    (C : Finset ι) (root : K.Vertex)
    (D : Finset ι) (hDC : D ⊆ C)
    (c : (K.intrinsicComponentLocalSlice C root).ComponentIndex D)
    (v : generatedSubgroup gen C)
    (hv :
      v ∈ (K.intrinsicComponentLocalSlice C root).componentAmbientCoset
        D c) :
    root.1 * (v : Γ) ∈
      (K.subalphabetComponentSubgraph C root).componentAmbientCoset
        D (K.intrinsicComponentLocalIndexEquiv C D root c) :=
  (K.intrinsicComponentLocalIndex_ambientCoset_mem_iff
    C D hDC root c v).mp hv

end CayleySubgraphSpec
end ABO
end PSTSEPPA
