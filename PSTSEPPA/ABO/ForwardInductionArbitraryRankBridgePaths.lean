import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedAmbientValue
import PSTSEPPA.ABO.ForwardInductionArbitraryRankSignedComponentTransport

/-!
# ABO Theorem 4.5: transport actual bridge paths at arbitrary rank

For the TRUE rooted original C-component of an incomplete signed Cayley
skeleton, the full component-tagged coset extension has both exact
original ambient Γ-coordinates and EXACT actual signed D-paths, through
the normalization to the locally generated Γ[C].

We show both components of the SOURCE bridge-path comparison:
* ambient D-left-coset membership is preserved and reflected by the
  genuine quotient isomorphism, using root-left multiplication;
* the actual proper-D bridge-PATH-LIFTING assertion (the second
  clause of Definition 4.1 bridge-freeness) holds for the local
  completed signed stage if and only if it holds for the original
  rooted completed signed stage.

These assertions concern REAL signed paths in the completed
source-and-full-label quotient graph, including ALL fresh coset
vertices; equal ambient group values never identify distinct
old-component-tagged quotient points.

Full original global embedding/injectivity and the actual forward
induction supplying local bridge-freeness remain separate obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

/-- Left multiplying BOTH the coset representative and the tested
point by a common root does not change D-left-coset membership. -/
theorem generatedLeftCoset_rootLeftTranslation_iff
    (gen : ι → Γ) (D : Finset ι) (root x y : Γ) :
    root * y ∈ generatedLeftCoset gen D (root * x) ↔
      y ∈ generatedLeftCoset gen D x := by
  change (root * x)⁻¹ * (root * y) ∈ generatedSubgroup gen D ↔
    x⁻¹ * y ∈ generatedSubgroup gen D
  simp [mul_inv_rev, mul_assoc]

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- True ORIGINAL versus normalized local attached-point ambient
D-coset membership, transported with the EXACT rooted quotient.
No assumption about globally retractable original Γ. -/
theorem arbitraryRankRootedOriginalMultiCosetValue_coset_iff
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι)
    (u v : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    K.arbitraryRankRootedOriginalMultiCosetValue
      C root P hadm hgen hret
        (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
          C root P hadm hgen hret v) ∈
      generatedLeftCoset gen D
        (K.arbitraryRankRootedOriginalMultiCosetValue
          C root P hadm hgen hret
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root P hadm hgen hret u)) ↔
    ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
      P hadm hgen hret v : Γ) ∈
      generatedLeftCoset gen D
        ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
          P hadm hgen hret u : Γ) := by
  rw [K.arbitraryRankRootedOriginalMultiCosetValue_natural
        C root P hadm hgen hret u,
      K.arbitraryRankRootedOriginalMultiCosetValue_natural
        C root P hadm hgen hret v]
  exact generatedLeftCoset_rootLeftTranslation_iff gen D root.1
    ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
      P hadm hgen hret u : Γ)
    ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
      P hadm hgen hret v : Γ)

/-- Genuine original/local bridge-path lifting equivalence.
For EACH proper D⊊C, EVERY ambient D-coset collision between
points of the FULL tagged coset quotient can be joined by an
ACTUAL signed D-path if and only if the normalized local stage
satisfies the corresponding statement.

This is the source's bridge-PATH half of Definition 4.1, not
the independent global embedding/injectivity half. -/
theorem arbitraryRankRootedCompletedBridgePaths_iff
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    (∀ (D : Finset ι), D ⊂ C →
      ∀ (u v : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
        P hadm hgen hret),
        ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
          P hadm hgen hret v : Γ) ∈
            generatedLeftCoset gen D
              ((K.intrinsicComponentLocalSlice C root).multiCosetAmbientValue
                P hadm hgen hret u : Γ) →
        ∃ w : LabelWord ι, LabelWord.Uses D w ∧
          (K.arbitraryRankRootedLocalCompletedEGraph
            C root P hadm hgen hret).Follows u w v) ↔
    (∀ (D : Finset ι), D ⊂ C →
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
            C root P hadm hgen hret).Follows x w y) := by
  constructor
  · intro hLocal D hDC x y hCoset
    let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
      C root P hadm hgen hret
    obtain ⟨u, rfl⟩ := e.surjective x
    obtain ⟨v, rfl⟩ := e.surjective y
    have hCosetLocal :=
      (K.arbitraryRankRootedOriginalMultiCosetValue_coset_iff
        C root P hadm hgen hret D u v).mp hCoset
    have hp := hLocal D hDC u v hCosetLocal
    exact (K.arbitraryRankRootedCompletedEGraph_supportedFollows_iff
      C root P hadm hgen hret D u v).mp hp
  · intro hOriginal D hDC u v hCoset
    have hCosetOriginal :=
      (K.arbitraryRankRootedOriginalMultiCosetValue_coset_iff
        C root P hadm hgen hret D u v).mpr hCoset
    have hp := hOriginal D hDC
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret u)
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret v)
      hCosetOriginal
    exact (K.arbitraryRankRootedCompletedEGraph_supportedFollows_iff
      C root P hadm hgen hret D u v).mpr hp

end CayleySubgraphSpec
end ABO
end PSTSEPPA
