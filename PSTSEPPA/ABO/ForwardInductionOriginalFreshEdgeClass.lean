import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedCompletedEGraphIso
import PSTSEPPA.ABO.RootedSingleCosetEGraphHom
import PSTSEPPA.ABO.RootedTaggedAttachedCosetEquiv

/-!
# ABO 4.5: literal ORIGINAL signed-edge class of a selected fresh coset edge

The original-rooted multi-CE graph has true signed edge TOKENS formed
by quotienting the genuine old/fresh constituent edge disjoint union
by EQUAL GLUED SOURCE and FULL signed label. A local H[C] freshly
completed D-edge must map to the quotient class of its actual
ORIGINAL Γ-rooted freshly completed D-edge. Importantly the latter
retains the original old D-component tag through
`rootedLocalAttachedCosetMap`; equality of ambient Γ edge coordinates
alone is not used.

The proof is definitional computation of the already certified
source-label quotient equivalence and single-D signed EGraph map.
It preserves BOTH oriented signed edge types including trivial
generators, formal inverses and loops; no old edge is fabricated.
This serves the next ORIGINAL full-B-coset edge-presentation gate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Under exact rooted H[C]→ORIGINAL Γ multi-CE signed graph
isomorphism, a selected fresh D-edge is the literal source
quotient class of the ORIGINAL fresh D-edge with the correctly
transported old D-component-tagged attached coset point.
Neither signed orientation is collapsed to an ambient Γ value. -/
theorem arbitraryRankRootedCompletedSignedHom_freshEdge_eq_originalClass
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι) (hDP : D ∈ P.alphabets)
    (q : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D)
    (s : {s : SignedLabel ι // signedBase s ∈ D}) :
    (K.arbitraryRankRootedCompletedEGraphHom
      C root P hadm hgen hret).onEdge
      ((K.intrinsicComponentLocalSlice C root).multiCosetEdgeInclude
        P hadm hgen hret D hDP (Sum.inr (q, s))) =
    Quotient.mk
      (sourceLabelEdgeSetoid
        (K.arbitraryRankRootedOriginalRawGraph
          C root P hadm hgen hret).source
        (K.arbitraryRankRootedOriginalRawGraph
          C root P hadm hgen hret).label)
      (⟨⟨D,hDP⟩,
        Sum.inr
          (K.rootedLocalAttachedCosetMap C D
            (P.proper D hDP).subset root q, s)⟩ :
        (K.subalphabetComponentSubgraph C root).MultiCosetRawEdge P) := by
  rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
