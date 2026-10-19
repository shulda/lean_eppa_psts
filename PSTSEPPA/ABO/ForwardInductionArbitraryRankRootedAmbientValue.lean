import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedVertexQuotient

/-!
# ABO Theorem 4.5: exact ambient coordinates in arbitrary-rank rooted multiCE

The published forward induction passes from an ORIGINAL incomplete
signed Γ-Cayley C-component to its locally normalized Γ[C] counterpart.
Even when Γ is only k-retractable, rather than globally retractable,
the new original component-tagged multi-coset quotient has an
unambiguous ambient Γ-coordinate.

We construct that coordinate by descending the ACTUAL component-tagged
attached-coset value through the literal ABO (3.10) intersection-support
gluing setoid.  This is NOT a quotient by ambient coordinate equality:
distinct original tagged points may have the SAME ambient value.

The source and local quotient coordinates are related by EXACTLY left
multiplication by the original signed skeleton root, at every rank.
This supplies the ambient-coordinate compatibility required in the
bridge-freeness and full-coset augmentation stages of ABO 4.5 and 4.7.
It proves no false global injectivity or completion admissibility.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Ambient Γ-value of the entire ORIGINAL rooted C-component's
multi-coset quotient, well-defined for arbitrary parent rank even
when Γ is not globally retractable.  Original component tags are
not collapsed by equality of these values. -/
noncomputable def arbitraryRankRootedOriginalMultiCosetValue
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (z : Quotient
      (K.arbitraryRankRootedOriginalMultiCosetSetoid
        C root P hadm hgen hret)) : Γ := by
  let M := K.subalphabetComponentSubgraph C root
  exact Quotient.liftOn z
    (fun p => M.attachedValue p.1.1 p.2)
    (by
      intro p q hpq
      change M.ShareIntersectionSupport p.1.1 q.1.1 p.2 q.2 at hpq
      exact M.shareIntersectionSupport_value_eq p.1.1 q.1.1 hpq)

/-- Every original component-tagged D-coset point retains its own
ambient value after the literal exact gluing, for D in P. -/
@[simp] theorem arbitraryRankRootedOriginalMultiCosetValue_include
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι) (hDP : D ∈ P.alphabets)
    (p : (K.subalphabetComponentSubgraph C root).AttachedCosetVertex D) :
    K.arbitraryRankRootedOriginalMultiCosetValue
      C root P hadm hgen hret
      (Quotient.mk (K.arbitraryRankRootedOriginalMultiCosetSetoid
        C root P hadm hgen hret)
        (⟨⟨D, hDP⟩, p⟩ :
          (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P)) =
      (K.subalphabetComponentSubgraph C root).attachedValue D p :=
  rfl

/-- The COMPLETE arbitrary-rank local/original tagged quotient
equivalence translates actual ambient coordinates by left
multiplication with the ORIGINAL old signed component root.

This is a coordinate-compatibility result, not an unjustified
claim that either quotient-to-Γ coordinate map is injective. -/
theorem arbitraryRankRootedOriginalMultiCosetValue_natural
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (z : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    K.arbitraryRankRootedOriginalMultiCosetValue
      C root P hadm hgen hret
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret z) =
    root.1 * ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
      P hadm hgen hret z : Γ) := by
  induction z using Quotient.inductionOn with
  | h p =>
      rcases p with ⟨b, p⟩
      change
        (K.subalphabetComponentSubgraph C root).attachedValue b.1
          (K.rootedLocalAttachedCosetMap C b.1
            (P.proper b.1 b.2).subset root p) =
        root.1 * ((K.intrinsicComponentLocalSlice C root).attachedValue b.1 p : Γ)
      exact K.rootedLocalAttachedCosetMap_value
        C b.1 (P.proper b.1 b.2).subset root p

end CayleySubgraphSpec
end ABO
end PSTSEPPA
