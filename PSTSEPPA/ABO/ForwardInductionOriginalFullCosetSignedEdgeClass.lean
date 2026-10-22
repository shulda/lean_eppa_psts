import PSTSEPPA.ABO.ForwardInductionOriginalFreshEdgeClass
import PSTSEPPA.ABO.Lemma43FullBCosetSignedEdgeCompleteness
import PSTSEPPA.ABO.RootedSignedBComponentGraphIso

/-!
# ABO 4.5: source Γ full B-component edges belong to ONE ORIGINAL D-copy

Let B⊆D be a selected constituent of the genuinely incomplete
ORIGINAL Γ-rooted signed multi-coset quotient. The local H[C]
lemma already proves that every ACTUAL oriented B-edge of the
B-component containing a D-point is represented by a freshly
completed D-edge of the SAME old D-component tag.

Transport this statement back across the certified vertex/edge
bijective rooted local/source quotient graph map, then use the
exact freshly completed D-edge quotient class calculation from
ForwardInductionOriginalFreshEdgeClass. We obtain a literal
ORIGINAL Γ raw-D edge representation, with the original old
D-component tag and both signed positive/inverse edge tokens.
No merely ambient group-coordinate edge equality is accepted.

This is the actual source-full-coset signed edge-presentation
clause needed alongside old D-tag support and signed completeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every REAL oriented signed B-edge token of an original rooted
Γ quotient B-component supported by a selected D-summand has an
ORIGINAL fresh D-edge quotient presentation from the SAME intrinsic
old D-component tag. This is a literal original raw-edge class,
not a local-only edge, not an ambient Cayley edge, and not a
fictitious missing original skeleton edge. -/
theorem arbitraryRankRootedOriginal_fullBComponent_edges_originalD
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι) (hDP : D ∈ P.alphabets)
    (B : Finset ι) (hBD : B ⊆ D)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D)
    (a : Quotient (sourceLabelEdgeSetoid
      (K.arbitraryRankRootedOriginalRawGraph
        C root P hadm hgen hret).source
      (K.arbitraryRankRootedOriginalRawGraph
        C root P hadm hgen hret).label))
    (ha : a ∈ (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).BComponentEdgeSet B
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret
        ((K.intrinsicComponentLocalSlice C root).multiCosetInclude
          P hadm hgen hret D hDP p))) :
    ∃ (q : (K.subalphabetComponentSubgraph C root).AttachedCosetVertex D)
      (s : {s : SignedLabel ι // signedBase s ∈ D}),
      q.1 = (K.rootedLocalAttachedCosetMap
          C D (P.proper D hDP).subset root p).1 ∧
      a = Quotient.mk
        (sourceLabelEdgeSetoid
          (K.arbitraryRankRootedOriginalRawGraph
            C root P hadm hgen hret).source
          (K.arbitraryRankRootedOriginalRawGraph
            C root P hadm hgen hret).label)
        (⟨⟨D,hDP⟩, Sum.inr (q,s)⟩ :
          (K.subalphabetComponentSubgraph C root).MultiCosetRawEdge P) := by
  let L := K.intrinsicComponentLocalSlice C root
  let G := K.arbitraryRankRootedLocalCompletedEGraph
    C root P hadm hgen hret
  let H := K.arbitraryRankRootedOriginalCompletedEGraph
    C root P hadm hgen hret
  let f := K.arbitraryRankRootedCompletedEGraphHom
    C root P hadm hgen hret
  have hbij := K.arbitraryRankRootedCompletedEGraphHom_bijective
    C root P hadm hgen hret
  obtain ⟨e, he⟩ := hbij.2.2 a
  have heB : e ∈ G.BComponentEdgeSet B
      (L.multiCosetInclude P hadm hgen hret D hDP p) := by
    apply (G.BComponentEdge_mem_iff_bijective
      H f hbij.1 hbij.2 B
        (L.multiCosetInclude P hadm hgen hret D hDP p) e).mpr
    change f.onEdge e ∈ H.BComponentEdgeSet B
      (f.onVertex (L.multiCosetInclude
        P hadm hgen hret D hDP p))
    rw [he]
    exact ha
  obtain ⟨q, s, hSameTag, hRep⟩ :=
    L.multiCoset_full_B_component_all_signed_edges_in_C
      P hadm hgen hret D hDP B hBD p e heB
  let qOrig := K.rootedLocalAttachedCosetMap C D
    (P.proper D hDP).subset root q
  refine ⟨qOrig, s, ?_, ?_⟩
  · exact congrArg (K.rootedLocalComponentIndexEquiv C root D) hSameTag
  · calc
      a = f.onEdge e := he.symm
      _ = f.onEdge
          (L.multiCosetEdgeInclude P hadm hgen hret
            D hDP (Sum.inr (q,s))) := congrArg f.onEdge hRep
      _ = Quotient.mk
          (sourceLabelEdgeSetoid
            (K.arbitraryRankRootedOriginalRawGraph
              C root P hadm hgen hret).source
            (K.arbitraryRankRootedOriginalRawGraph
              C root P hadm hgen hret).label)
          (⟨⟨D,hDP⟩, Sum.inr (qOrig,s)⟩ :
            (K.subalphabetComponentSubgraph C root).MultiCosetRawEdge P) :=
          K.arbitraryRankRootedCompletedSignedHom_freshEdge_eq_originalClass
            C root P hadm hgen hret D hDP q s

end CayleySubgraphSpec
end ABO
end PSTSEPPA
