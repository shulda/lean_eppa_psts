import PSTSEPPA.ABO.ForwardInductionArbitraryRankBridgePaths

/-!
# ABO Theorem 4.5: both genuine signed bridge-freeness clauses commute with localization

Bridge-freeness (Definition 4.1) has TWO independent clauses:
  (1) ambient embedding of the full component-tagged coset extension;
  (2) reflection of ambient proper-D coset connections by REAL signed
      D-paths in the extension.

We have already proved at every parent rank that the original rooted
signed coset extension and its local Γ[C] counterpart are isomorphic
on actual old/fresh signed edge classes, that their ambient Γ-values
differ by left multiplication by the original root, and that exact
proper-D bridge paths correspond.

We now prove that the ENTIRE two-clause property -- injectivity
of the genuine ambient-coordinate map AND actual bridge paths --
is equivalent between the original rooted completed extension
and its normalized local H[C] stage.  No appeal to ambient
coordinate equality to merge tagged quotient points is made.

The statement is a LOCALIZATION TRANSPORT theorem, NOT a proof
that the local stage IS bridge-free: the printed forward induction
must derive that property from its lower-rank cluster hypotheses.
Global Γ-retractability is never assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Injectivity of the exact ambient-coordinate map on ALL local
tagged glued original/new quotient vertices is equivalent to
injectivity on the ORIGINAL source-rooted tagged quotient.

This is a statement about ambient EMBEDDING, not a false assumption
that all such coset quotients automatically embed. -/
theorem arbitraryRankRootedOriginalMultiCosetValue_injective_iff
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    Function.Injective
      (fun u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
          P hadm hgen hret =>
        ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
          P hadm hgen hret u : Γ)) ↔
    Function.Injective
      (K.arbitraryRankRootedOriginalMultiCosetValue
        C root P hadm hgen hret) := by
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm hgen hret
  constructor
  · intro hLocal x y hxy
    obtain ⟨u, rfl⟩ := e.surjective x
    obtain ⟨v, rfl⟩ := e.surjective y
    have hh :
        root.1 *
          ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
            P hadm hgen hret u : Γ) =
        root.1 *
          ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
            P hadm hgen hret v : Γ) := by
      calc
        root.1 *
            ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
              P hadm hgen hret u : Γ) =
          K.arbitraryRankRootedOriginalMultiCosetValue
            C root P hadm hgen hret (e u) :=
          (K.arbitraryRankRootedOriginalMultiCosetValue_natural
            C root P hadm hgen hret u).symm
        _ = K.arbitraryRankRootedOriginalMultiCosetValue
            C root P hadm hgen hret (e v) := hxy
        _ = root.1 *
            ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
              P hadm hgen hret v : Γ) :=
          K.arbitraryRankRootedOriginalMultiCosetValue_natural
            C root P hadm hgen hret v
    exact congrArg e (hLocal (mul_left_cancel hh))
  · intro hOriginal u v huv
    apply e.injective
    apply hOriginal
    calc
      K.arbitraryRankRootedOriginalMultiCosetValue
          C root P hadm hgen hret (e u) =
        root.1 *
          ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
            P hadm hgen hret u : Γ) :=
        K.arbitraryRankRootedOriginalMultiCosetValue_natural
          C root P hadm hgen hret u
      _ = root.1 *
          ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
            P hadm hgen hret v : Γ) :=
        congrArg (fun x : Γ => root.1 * x) huv
      _ = K.arbitraryRankRootedOriginalMultiCosetValue
          C root P hadm hgen hret (e v) :=
        (K.arbitraryRankRootedOriginalMultiCosetValue_natural
          C root P hadm hgen hret v).symm

/-- FULL two-clause signed bridge-freeness for the true local
normalized C-stage: literal ambient Γ-coordinate INJECTION,
and genuine proper-D signed PATH reflection for every pair of
newly glued component-tagged coset quotient vertices.

We use the actual EGraph from the exact source-and-label quotient,
rather than silently identifying it with a different graph API. -/
def ArbitraryRankRootedLocalBridgeProperty
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) : Prop :=
    Function.Injective
      (fun u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
          P hadm hgen hret =>
        ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
          P hadm hgen hret u : Γ)) ∧
    ∀ (D : Finset ι), D ⊂ C →
      ∀ (u v : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
        P hadm hgen hret),
        ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
          P hadm hgen hret v : Γ) ∈
            generatedLeftCoset gen D
              ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
                P hadm hgen hret u : Γ) →
        ∃ w : LabelWord ι, LabelWord.Uses D w ∧
          (K.arbitraryRankRootedLocalCompletedEGraph
            C root P hadm hgen hret).Follows u w v

/-- The corresponding exact two-clause signed bridge property
for the ORIGINAL rooted incomplete source C-component,
including every attached tagged coset point and REAL signed
edge class; it does NOT assume global Γ-retractability. -/
def ArbitraryRankRootedOriginalBridgeProperty
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) : Prop :=
    Function.Injective
      (K.arbitraryRankRootedOriginalMultiCosetValue
        C root P hadm hgen hret) ∧
    ∀ (D : Finset ι), D ⊂ C →
      ∀ (x y : Quotient
        (K.arbitraryRankRootedOriginalMultiCosetSetoid
          C root P hadm hgen hret)),
        K.arbitraryRankRootedOriginalMultiCosetValue
          C root P hadm hgen hret y ∈
          generatedLeftCoset gen D
            (K.arbitraryRankRootedOriginalMultiCosetValue
              C root P hadm hgen hret x) →
        ∃ w : LabelWord ι, LabelWord.Uses D w ∧
          (K.arbitraryRankRootedOriginalCompletedEGraph
            C root P hadm hgen hret).Follows x w y

/-- Source Theorem 4.5 arbitrary-rank GENUINE localization:
the whole embedding-and-bridge-path property transfers in BOTH
directions across the exact original/local signed multiCE
isomorphism.  This theorem transfers a property, rather than
assuming or proving its existence out of thin air. -/
theorem arbitraryRankRootedCompletedBridgeProperty_iff
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    K.ArbitraryRankRootedLocalBridgeProperty
      C root P hadm hgen hret ↔
    K.ArbitraryRankRootedOriginalBridgeProperty
      C root P hadm hgen hret := by
  constructor
  · rintro ⟨hinj, hpaths⟩
    exact ⟨(K.arbitraryRankRootedOriginalMultiCosetValue_injective_iff
      C root P hadm hgen hret).mp hinj,
      (K.arbitraryRankRootedCompletedBridgePaths_iff
        C root P hadm hgen hret).mp hpaths⟩
  · rintro ⟨hinj, hpaths⟩
    exact ⟨(K.arbitraryRankRootedOriginalMultiCosetValue_injective_iff
      C root P hadm hgen hret).mpr hinj,
      (K.arbitraryRankRootedCompletedBridgePaths_iff
        C root P hadm hgen hret).mpr hpaths⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
