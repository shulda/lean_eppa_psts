import PSTSEPPA.ABO.ForwardInductionSourceReadySignedLocalStage
import PSTSEPPA.ABO.ForwardInductionLocalCompletedEGraphAgreement
import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents
import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedVertexQuotient

/-!
# Exact ORIGINAL Γ-rooted full B-coset vertices, with old D-component tags

The actual signed B-path component of a point in a selected D-copy,
B⊆D, is a literal intrinsic OLD-COMPONENT-TAGGED B-coset even if the
original ambient group Γ is not globally retractable or generated.

The theorem is not a mere local normalized H[C] statement: its
left-hand side consists of genuine ORIGINAL Γ-rooted signed quotient
vertices and word paths, and the right side represents EXACTLY those
original quotient vertices by actual original attached D-coset points,
with the original intrinsic D-component index and the original signed
coset inclusion. The local q witnessing this original representation
also carries the precise B-coset membership.

Both implications are formalized, using the signed original/local
EGraph homomorphism, the proven single-selected-D full B-component
classification and exact original source quotient inclusion.

No ambient-coordinate identification, imaginary old edge, new
axiom or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- COMPLETE ORIGINAL Γ-ROOTED B-component VERTEX CLASSIFICATION
for a selected attached D-constituent (B⊆D). The local coset
witness q maps to a LITERAL original D-copy point with its full
intrinsic old D-component tag, and every such point is reached
by an ACTUAL original signed B-word path.

The original Γ may be only k-retractable or not globally
retractable at all; only the actually used local generated
H[C] group is assumed retractable. -/
theorem arbitraryRankRootedOriginalFullBComponent_exactTaggedVertices
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι) (hDP : D ∈ P.alphabets)
    (B : Finset ι) (hBD : B ⊆ D)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D)
    (y : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).Follows
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root P hadm hgen hret
            ((K.intrinsicComponentLocalSlice C root).multiCosetInclude
              P hadm hgen hret D hDP p)) w y) ↔
    ∃ q : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D,
      q.1 = p.1 ∧
      q.2.1 ∈ generatedLeftCoset
        (trivialCompletionGenerator gen C) B p.2.1 ∧
      y = Quotient.mk
        (K.arbitraryRankRootedOriginalMultiCosetSetoid
          C root P hadm hgen hret)
        (⟨⟨D,hDP⟩,
          K.rootedLocalAttachedCosetMap
            C D (P.proper D hDP).subset root q⟩ :
          (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) := by
  let L := K.intrinsicComponentLocalSlice C root
  let H := K.arbitraryRankRootedOriginalCompletedEGraph
    C root P hadm hgen hret
  let G := K.arbitraryRankRootedLocalCompletedEGraph
    C root P hadm hgen hret
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm hgen hret
  let a := L.multiCosetInclude P hadm hgen hret D hDP p
  constructor
  · rintro ⟨w, hw, hp⟩
    let v := e.symm y
    have hLocal : G.Follows a w v :=
      (K.arbitraryRankRootedCompletedEGraphHom_follows_iff
        C root P hadm hgen hret a v w).mpr (by
        change H.Follows (e a) w (e v)
        simpa [v] using hp)
    have hStd : (L.multiCosetEGraph P hadm hgen hret).Follows a w v :=
      (K.arbitraryRankRootedLocalCompletedFollows_iff_standard
        C root P hadm hgen hret a v w).mp hLocal
    obtain ⟨q, hIndex, hCoset, hVertex⟩ :=
      (L.multiCoset_selected_C_subalphabet_B_component_exact
        P hadm hgen hret D hDP B hBD p v).mp
          ⟨w, hw, hStd⟩
    refine ⟨q, hIndex, hCoset, ?_⟩
    calc
      y = e v := (e.apply_symm_apply y).symm
      _ = e (L.multiCosetInclude P hadm hgen hret D hDP q) := by
        rw [hVertex]
      _ = Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D,hDP⟩,
            K.rootedLocalAttachedCosetMap
              C D (P.proper D hDP).subset root q⟩ :
            (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) :=
        K.arbitraryRankRootedLocalMultiCosetVertexEquiv_include
          C root P hadm hgen hret D hDP q
  · rintro ⟨q, hIndex, hCoset, hVertex⟩
    obtain ⟨w, hw, hLocal⟩ :=
      (L.multiCoset_selected_C_subalphabet_B_component_exact
        P hadm hgen hret D hDP B hBD p
        (L.multiCosetInclude P hadm hgen hret D hDP q)).mpr
          ⟨q, hIndex, hCoset, rfl⟩
    have hSource : G.Follows a w
        (L.multiCosetInclude P hadm hgen hret D hDP q) :=
      (K.arbitraryRankRootedLocalCompletedFollows_iff_standard
        C root P hadm hgen hret a
        (L.multiCosetInclude P hadm hgen hret D hDP q) w).mpr hLocal
    have hOriginal :=
      (K.arbitraryRankRootedCompletedEGraphHom_follows_iff
        C root P hadm hgen hret a
        (L.multiCosetInclude P hadm hgen hret D hDP q) w).mp hSource
    refine ⟨w, hw, ?_⟩
    change H.Follows (e a) w
      (e (L.multiCosetInclude P hadm hgen hret D hDP q)) at hOriginal
    rw [K.arbitraryRankRootedLocalMultiCosetVertexEquiv_include
      C root P hadm hgen hret D hDP q] at hOriginal
    rw [hVertex]
    exact hOriginal

end CayleySubgraphSpec
end ABO
end PSTSEPPA
