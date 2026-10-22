import PSTSEPPA.ABO.Lemma43SignedDichotomyFromMinimum
import PSTSEPPA.ABO.ForwardInductionOriginalFullCosetGammaExact
import PSTSEPPA.ABO.ForwardInductionOriginalFullCosetSignedSteps
import PSTSEPPA.ABO.ForwardInductionOriginalFullCosetSignedEdgeClass

/-!
# ABO Theorem 4.5: LITERAL original Γ full-B-coset SIGNED alternative

The locally generated and retractable H[C] proof has a real
full-B-coset case. Its original Γ-rooted counterpart is stronger
than a local coset support fact. It explicitly specifies:

1. the entire ORIGINAL signed B-connected component of the anchor,
   in BOTH directions, as exactly ONE original old-component-tagged
   selected D-copy whose original Γ-coordinate lies in the same
   generated left B-coset as the anchor;
2. EVERY actual oriented signed edge token of that whole B-component
   is a fresh D-edge in that SAME original D-component-tagged copy,
   not just an edge with equal ambient Cayley coordinates;
3. EVERY positive/negative signed B-step is genuinely present at
   EVERY vertex in the ORIGINAL quotient signed EGraph.

The proofs use the independently certified true signed original/local
graph isomorphism, exact Γ-coset component classification, actual
old-component tag transport, original fresh-edge quotient
naturality, and original directed signed-edge completeness.
They do NOT assume Γ is globally generated or retractable, invent
original old edges or identify distinct original component tags.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- ACTUAL original Γ-rooted full signed B-coset alternative, with
literal ORIGINAL Γ coordinates, genuine original old D-component
indices, WHOLE-component vertex iff, original actual signed
D-edge quotient-class presentations, and full positive/inverse
B-edge completeness at each original signed component vertex. -/
def HasOriginalRootedFullSignedBCosetAlternative
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret) : Prop :=
  ∃ (D : Finset ι)
    (hDP : D ∈ (allProperCosetFamily C).alphabets)
    (hBD : B ⊆ D)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D),
      (K.intrinsicComponentLocalSlice C root).multiCosetInclude
        (allProperCosetFamily C) hadm hgen hret D hDP p = u ∧
      (∀ y : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
          C root (allProperCosetFamily C) hadm hgen hret),
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.arbitraryRankRootedOriginalCompletedEGraph
            C root (allProperCosetFamily C) hadm hgen hret).Follows
              (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
                C root (allProperCosetFamily C) hadm hgen hret u) w y) ↔
        ∃ q : (K.subalphabetComponentSubgraph C root).AttachedCosetVertex D,
          q.1 = (K.rootedLocalAttachedCosetMap
            C D ((mem_allProperCosetFamily C D).mp hDP).subset root p).1 ∧
          q.2.1 ∈ generatedLeftCoset gen B
            (K.rootedLocalAttachedCosetMap
              C D ((mem_allProperCosetFamily C D).mp hDP).subset root p).2.1 ∧
          y = Quotient.mk
            (K.arbitraryRankRootedOriginalMultiCosetSetoid
              C root (allProperCosetFamily C) hadm hgen hret)
            (⟨⟨D, hDP⟩,q⟩ :
              (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex
                (allProperCosetFamily C))) ∧
      (∀ a : Quotient (sourceLabelEdgeSetoid
          (K.arbitraryRankRootedOriginalRawGraph
            C root (allProperCosetFamily C) hadm hgen hret).source
          (K.arbitraryRankRootedOriginalRawGraph
            C root (allProperCosetFamily C) hadm hgen hret).label),
        a ∈ (K.arbitraryRankRootedOriginalCompletedEGraph
          C root (allProperCosetFamily C) hadm hgen hret).BComponentEdgeSet
          B (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root (allProperCosetFamily C) hadm hgen hret u) →
        ∃ (q : (K.subalphabetComponentSubgraph C root).AttachedCosetVertex D)
          (s : {s : SignedLabel ι // signedBase s ∈ D}),
            q.1 = (K.rootedLocalAttachedCosetMap
              C D ((mem_allProperCosetFamily C D).mp hDP).subset root p).1 ∧
            a = Quotient.mk
              (sourceLabelEdgeSetoid
                (K.arbitraryRankRootedOriginalRawGraph
                  C root (allProperCosetFamily C) hadm hgen hret).source
                (K.arbitraryRankRootedOriginalRawGraph
                  C root (allProperCosetFamily C) hadm hgen hret).label)
              (⟨⟨D, hDP⟩, Sum.inr (q,s)⟩ :
                (K.subalphabetComponentSubgraph C root).MultiCosetRawEdge
                  (allProperCosetFamily C))) ∧
      (∀ y : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
          C root (allProperCosetFamily C) hadm hgen hret),
        y ∈ (K.arbitraryRankRootedOriginalCompletedEGraph
          C root (allProperCosetFamily C) hadm hgen hret).BComponentVertexSet
          B (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root (allProperCosetFamily C) hadm hgen hret u) →
        ∀ s : SignedLabel ι, signedBase s ∈ B →
          ∃ a : Quotient (sourceLabelEdgeSetoid
            (K.arbitraryRankRootedOriginalRawGraph
              C root (allProperCosetFamily C) hadm hgen hret).source
            (K.arbitraryRankRootedOriginalRawGraph
              C root (allProperCosetFamily C) hadm hgen hret).label),
            a ∈ (K.arbitraryRankRootedOriginalCompletedEGraph
              C root (allProperCosetFamily C) hadm hgen hret).BComponentEdgeSet
              B (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
                C root (allProperCosetFamily C) hadm hgen hret u) ∧
            (K.arbitraryRankRootedOriginalCompletedEGraph
              C root (allProperCosetFamily C) hadm hgen hret).source a = y ∧
            (K.arbitraryRankRootedOriginalCompletedEGraph
              C root (allProperCosetFamily C) hadm hgen hret).label a = s)

/-- The local FULL B-coset alternative, when Γ need only be locally
retractable on H[C], implies the ENTIRE literal source-original
Γ-tagged FULL signed B-coset alternative. No lower bridge-free
premise or globally retractable ambient Γ is needed for this
geometric implication. Both edge orientations are genuine. -/
theorem originalRootedFullSignedBCoset_of_localFull
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret)
    (hFull : (K.intrinsicComponentLocalSlice C root).HasFullSignedBCosetAlternative
      hadm hgen hret B u) :
    K.HasOriginalRootedFullSignedBCosetAlternative
      C root hadm hgen hret B u := by
  let L := K.intrinsicComponentLocalSlice C root
  let P := allProperCosetFamily C
  rcases hFull with ⟨D, hDP, hBD, p, hAnchor, _hEdges, _hSteps⟩
  subst u
  refine ⟨D, hDP, hBD, p, rfl, ?_, ?_, ?_⟩
  · intro y
    exact K.arbitraryRankRootedOriginalFullBComponent_exactGammaTaggedCoset
      C root P hadm hgen hret D hDP B hBD p y
  · intro a ha
    exact K.arbitraryRankRootedOriginal_fullBComponent_edges_originalD
      C root P hadm hgen hret D hDP B hBD p a ha
  · intro y hy s hs
    exact K.arbitraryRankRootedOriginal_fullBComponent_allSignedSteps
      C root P hadm hgen hret D hDP B hBD p y hy s hs

end CayleySubgraphSpec
end ABO
end PSTSEPPA
