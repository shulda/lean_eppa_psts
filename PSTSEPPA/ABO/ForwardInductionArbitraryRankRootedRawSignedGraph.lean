import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedVertexQuotient
import PSTSEPPA.ABO.RootedMultiCosetRawGraphNaturality

/-!
# ABO Theorem 4.5: arbitrary-rank ORIGINAL/LOCAL oriented signed RAW graph

The existing source-rooted raw signed graph theorem works only in the
two-letter first-rank setting. Its geometric ingredients were independently
formalized WITHOUT a rank restriction: the genuine incomplete rooted
C-component, the local H[C] skeleton, exact tagged (D∩E)-gluing,
the entire attached D-coset graph isomorphisms, and the equivalence
of the original/local disjoint unions of ACTUAL signed edge tokens.

The preceding arbitrary-rank theorem constructs the true LOCAL vertex
quotient from the locally admissible, generated and retractable H[C] group
and transports the original source vertex setoid without assuming global
retractability of Γ.

Here we upgrade this to a RAW signed graph isomorphism for every selected
proper-alphabet family P of C, with arbitrary |C|. Its vertices are the
ACTUAL component-tagged glued vertex quotients, and its edges are the
still unquotiented old/outside-D and completed/inside-D signed tokens.

The edge bijection fixes the outer D alphabet and uses the already
verified single-D signed graph equivalence. We prove exact preservation
of the glued SOURCE, FULL signed label, and FORMAL inverse token.
No missing original old edge is added and distinct old skeleton component
tags are never equated merely by common ambient group coordinates.

This is the raw signed input for the existing
SourceLabelEdgeQuotientGraphIso machinery, which will next give the
rank-independent complete directed signed edge quotient and EGraph.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The original signed raw graph over its LITERAL transported
component-tagged gluing quotient, for an arbitrary parent C rank.
The ambient group Γ need not be globally retractable. -/
noncomputable def arbitraryRankRootedOriginalRawGraph
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    LabelledGraph
      (Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
        C root P hadm hgen hret))
      ((K.subalphabetComponentSubgraph C root).MultiCosetRawEdge P) ι :=
  (K.subalphabetComponentSubgraph C root).multiCosetRawGraphOfSetoid
    P (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)

/-- The true local H[C] signed raw graph with its certified
proper-coset gluing quotient, not an ambient-coordinate quotient. -/
noncomputable def arbitraryRankRootedLocalRawGraph
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    LabelledGraph
      ((K.intrinsicComponentLocalSlice C root).MultiCosetVertex
        P hadm hgen hret)
      ((K.intrinsicComponentLocalSlice C root).MultiCosetRawEdge P) ι :=
  (K.intrinsicComponentLocalSlice C root).multiCosetRawGraphOfSetoid
    P ((K.intrinsicComponentLocalSlice C root).multiCosetSetoid
      P hadm hgen hret)

/-- On EVERY genuine oriented old/fresh raw edge token,
the actual original/source glued vertex equals the image
of its true normalized local source. This uses the old
single-D signed graph map, not ambient Cayley equality. -/
theorem arbitraryRankRootedRawGraph_source_natural
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (e : (K.intrinsicComponentLocalSlice C root).MultiCosetRawEdge P) :
    (K.arbitraryRankRootedOriginalRawGraph C root P hadm hgen hret).source
        (K.rootedLocalMultiCosetRawEdgeEquiv C root P e) =
      K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret
        ((K.arbitraryRankRootedLocalRawGraph
          C root P hadm hgen hret).source e) := by
  rcases e with ⟨b, edge⟩
  let f := K.rootedSingleCosetEGraphHom C b.1
    (P.proper b.1 b.2).subset root
  change
    Quotient.mk (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)
      (⟨b, ((K.subalphabetComponentSubgraph C root).singleCosetEGraph b.1).source
        (f.onEdge edge)⟩ :
        (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) =
    Quotient.mk (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)
      (⟨b, f.onVertex
        (((K.intrinsicComponentLocalSlice C root).singleCosetEGraph b.1).source
          edge)⟩ :
        (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P)
  exact congrArg
    (fun v : (K.subalphabetComponentSubgraph C root).AttachedCosetVertex b.1 =>
      (Quotient.mk (K.arbitraryRankRootedOriginalMultiCosetSetoid
        C root P hadm hgen hret)
        (⟨b, v⟩ :
          (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P)))
    (f.map_source edge)

/-- No loss of signed orientation, inverse tokens, or labels. -/
theorem arbitraryRankRootedRawGraph_label_natural
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (e : (K.intrinsicComponentLocalSlice C root).MultiCosetRawEdge P) :
    (K.arbitraryRankRootedOriginalRawGraph C root P hadm hgen hret).label
      (K.rootedLocalMultiCosetRawEdgeEquiv C root P e) =
    (K.arbitraryRankRootedLocalRawGraph C root P hadm hgen hret).label e :=
  K.rootedLocalMultiCosetRawEdgeLabel_natural C root P e

/-- The raw signed edge map commutes with FORMAL inversion,
for arbitrary parent rank and every actual D-summand. -/
theorem arbitraryRankRootedRawGraph_inv_natural
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (e : (K.intrinsicComponentLocalSlice C root).MultiCosetRawEdge P) :
    K.rootedLocalMultiCosetRawEdgeEquiv C root P
        ((K.arbitraryRankRootedLocalRawGraph C root P hadm hgen hret).inv e) =
      (K.arbitraryRankRootedOriginalRawGraph C root P hadm hgen hret).inv
        (K.rootedLocalMultiCosetRawEdgeEquiv C root P e) := by
  rcases e with ⟨b, edge⟩
  let f := K.rootedSingleCosetEGraphHom C b.1
    (P.proper b.1 b.2).subset root
  change
    (⟨b, f.onEdge
      (((K.intrinsicComponentLocalSlice C root).singleCosetEGraph b.1).inv
        edge)⟩ :
        (K.subalphabetComponentSubgraph C root).MultiCosetRawEdge P) =
    ⟨b, ((K.subalphabetComponentSubgraph C root).singleCosetEGraph b.1).inv
      (f.onEdge edge)⟩
  exact congrArg
    (fun e' => (⟨b, e'⟩ :
      (K.subalphabetComponentSubgraph C root).MultiCosetRawEdge P))
    (f.map_inv edge)

/-- The entire original/local signed RAW multi-coset graphs
are isomorphic on actually glued vertices and oriented raw
signed edge tokens. It is NOT yet the deterministic
edge-QUOTIENT of the source completion. -/
noncomputable def arbitraryRankRootedRawGraphHom
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    LabelledGraphHom
      (K.arbitraryRankRootedLocalRawGraph C root P hadm hgen hret)
      (K.arbitraryRankRootedOriginalRawGraph C root P hadm hgen hret) where
  onVertex := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm hgen hret
  onEdge := K.rootedLocalMultiCosetRawEdgeEquiv C root P
  map_source := K.arbitraryRankRootedRawGraph_source_natural
    C root P hadm hgen hret
  map_inv := K.arbitraryRankRootedRawGraph_inv_natural
    C root P hadm hgen hret
  map_label := K.arbitraryRankRootedRawGraph_label_natural
    C root P hadm hgen hret

/-- Full rank-independent RAW signed graph bijectivity,
including every original old edge that actually exists,
every new coset edge and both formal signed inverses. -/
theorem arbitraryRankRootedRawGraphHom_bijective
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    Function.Bijective
      (K.arbitraryRankRootedRawGraphHom C root P hadm hgen hret).onVertex ∧
    Function.Bijective
      (K.arbitraryRankRootedRawGraphHom C root P hadm hgen hret).onEdge :=
  ⟨(K.arbitraryRankRootedLocalMultiCosetVertexEquiv
      C root P hadm hgen hret).bijective,
    (K.rootedLocalMultiCosetRawEdgeEquiv C root P).bijective⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
