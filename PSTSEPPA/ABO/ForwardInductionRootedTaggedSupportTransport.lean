import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedVertexQuotient
import PSTSEPPA.ABO.MultiCosetVertexSupport

/-!
# ABO Theorem 4.5: exact COMPONENT-TAGGED support is reflected by localization

The already certified rank-independent rooted local/original
multi-coset equivalence is NOT just an untagged graph isomorphism.
For each D in the selected proper family it maps the WHOLE
component-tagged attached D-coset fibre bijectively onto the
corresponding ORIGINAL rooted D-coset fibre, even though
the original ambient group Γ need not be globally retractable.

A basic source condition for the cluster property is that a
vertex has a literal original D-support, in the sense of the
exact (3.10) gluing quotient. We prove that this condition is
preserved AND REFLECTED along the genuine rooted local/original
vertex equivalence, for every D and ALL quotient vertices.

The backward direction requires surjectivity of the genuine
dependent tagged attached-D-coset equivalence; equality of
ambient Γ-coordinates alone would be incorrect and is not used.

This is the first essential source-specific transfer gate
towards transporting attained MINIMUM support and entire
signed B-clusters from normalized Γ[C] stages back to
actual original Γ-components under k-retractability.

No fake old edges, no quotient by ambient group coordinates,
no global retractability of Γ, no new axioms or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- ORIGINAL rooted C-component D-support means a literal
component-tagged D-coset representative in the true original
intersection-support gluing quotient, not just an ambient
D-coset membership statement.

The original Γ need not be globally retractable. -/
def ArbitraryRankRootedOriginalSupported
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι)
    (z : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)) : Prop :=
  ∃ (hDP : D ∈ P.alphabets)
    (p : (K.subalphabetComponentSubgraph C root).AttachedCosetVertex D),
    Quotient.mk
        (K.arbitraryRankRootedOriginalMultiCosetSetoid
          C root P hadm hgen hret)
        (⟨⟨D, hDP⟩, p⟩ :
          (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) = z

/-- The exact original component-tagged D-support predicate is
invariant under the true local/original QUOTIENT equivalence at
ARBITRARY parent rank, including D=empty and equal/trivial
generators. No assumption about global retractability of Γ.

This is stronger than preserving the ambient Γ coordinate
and will be needed to transfer entire-component attained
support minima from Γ[C] back into the source Γ stage. -/
theorem arbitraryRankRootedLocalSupported_iff_original
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι)
    (z : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    (K.intrinsicComponentLocalSlice C root).MultiCosetVertexSupported
      P hadm hgen hret D z ↔
    K.ArbitraryRankRootedOriginalSupported
      C root P hadm hgen hret D
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret z) := by
  let L := K.intrinsicComponentLocalSlice C root
  let M := K.subalphabetComponentSubgraph C root
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm hgen hret
  constructor
  · rintro ⟨hDP, p, hp⟩
    refine ⟨hDP,
      K.rootedLocalAttachedCosetMap C D
        (P.proper D hDP).subset root p, ?_⟩
    calc
      Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D, hDP⟩,
            K.rootedLocalAttachedCosetMap C D
              (P.proper D hDP).subset root p⟩ :
            M.MultiCosetRawVertex P) =
        e (L.multiCosetInclude P hadm hgen hret D hDP p) :=
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv_include
            C root P hadm hgen hret D hDP p).symm
      _ = e z := congrArg e hp
  · rintro ⟨hDP, p, hp⟩
    let E := K.rootedLocalAttachedCosetEquiv C D
      (P.proper D hDP).subset root
    let q : L.AttachedCosetVertex D := E.symm p
    refine ⟨hDP, q, ?_⟩
    apply e.injective
    calc
      e (L.multiCosetInclude P hadm hgen hret D hDP q) =
        Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D, hDP⟩,
            K.rootedLocalAttachedCosetMap C D
              (P.proper D hDP).subset root q⟩ :
            M.MultiCosetRawVertex P) :=
          K.arbitraryRankRootedLocalMultiCosetVertexEquiv_include
            C root P hadm hgen hret D hDP q
      _ = Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D, hDP⟩, p⟩ : M.MultiCosetRawVertex P) := by
            have hEq :
                K.rootedLocalAttachedCosetMap C D
                  (P.proper D hDP).subset root q = p :=
              E.apply_symm_apply p
            rw [hEq]
      _ = e z := hp

end CayleySubgraphSpec
end ABO
end PSTSEPPA
