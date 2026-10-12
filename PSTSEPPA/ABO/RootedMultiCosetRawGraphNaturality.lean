import PSTSEPPA.ABO.RootedSourceMultiCosetVertexQuotient
import PSTSEPPA.ABO.RootedMultiCosetRawEdgeEquiv
import PSTSEPPA.ABO.MultiCosetRawEdgeInversion

/-!
# Genuine signed raw-edge graph equivalence for rooted original H1 components

For each proper-alphabet family P over a two-letter A, the local
Γ[A] normalized component and the true source-rooted Γ component have
an equivalence of component/alphabet-TAGGED glued vertex quotients,
even when Γ is only 2-retractable and not globally retractable (#380).

The signed directed raw edge token disjoint unions also have an exact
bijection preserving their outer alphabet tags (#381). The key remaining
geometric check is that the edge bijection sends the actual tagged
SOURCE vertex to its already-glued equivalent, and COMMUTES WITH FORMAL
EDGE REVERSAL. Both facts follow summandwise from the genuine single-B
signed graph isomorphisms (#377), not from ambient coordinates.

A raw signed graph remembers its edge involution and label before any
source-and-label EDGE identifications. This file proves an honest signed
labelled graph isomorphism on those raw graphs, with bijective maps on
both glued vertices and RAW oriented edge tokens. Quotienting those raw
tokens to form the final deterministic multi-coset EGraph is separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The literal alphabet-tagged signed raw-edge multigraph over ANY
setoid of the component-tagged raw points. The chosen vertex setoid
need not arise from a globally retractable ambient group. There is
not yet any edge quotient, hence no target-congruence requirement. -/
noncomputable def multiCosetRawGraphOfSetoid
    (P : CosetFamilySpec S)
    (s : Setoid (K.MultiCosetRawVertex P)) :
    LabelledGraph (Quotient s) (K.MultiCosetRawEdge P) ι where
  source e :=
    Quotient.mk s
      (⟨e.1, (K.singleCosetEGraph e.1.1).source e.2⟩ :
        K.MultiCosetRawVertex P)
  inv := K.multiCosetRawEdgeInv P
  inv_inv := K.multiCosetRawEdgeInv_inv P
  inv_ne := K.multiCosetRawEdgeInv_ne P
  label := K.multiCosetRawEdgeLabel P
  label_inv := K.multiCosetRawEdgeLabel_inv P

/-- Raw graph of the *true* source-rooted incomplete A-component.
Its glued vertex setoid is transported from the locally normalized
Γ[A] and never identifies distinct component tags by group value. -/
noncomputable def rootedAmbientMultiCosetRawGraph
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A) :
    LabelledGraph
      (Quotient (K.rootedAmbientMultiCosetSetoid A hcard hret root P))
      ((K.subalphabetComponentSubgraph A root).MultiCosetRawEdge P) ι :=
  (K.subalphabetComponentSubgraph A root).multiCosetRawGraphOfSetoid P
    (K.rootedAmbientMultiCosetSetoid A hcard hret root P)

/-- Raw graph over the local Γ[A] representative, with the TRUE
gluing setoid arising from global retractability only INSIDE Γ[A]. -/
noncomputable def rootedLocalMultiCosetRawGraph
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A) :
    LabelledGraph
      ((K.intrinsicComponentLocalSlice A root).MultiCosetVertex P
        ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le))
      ((K.intrinsicComponentLocalSlice A root).MultiCosetRawEdge P) ι :=
  (K.intrinsicComponentLocalSlice A root).multiCosetRawGraphOfSetoid P
    ((K.intrinsicComponentLocalSlice A root).multiCosetSetoid P
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))

/-- The actual multi-coset signed RAW edge equivalence transports
the glued source of EVERY old/outside-B or new/inside-B edge.
In particular this uses the true signed single-B graph morphism and
exact quotient-natural tagged vertex mapping, never the ambient value. -/
theorem rootedMultiCosetRawGraph_source_natural
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A)
    (e : (K.intrinsicComponentLocalSlice A root).MultiCosetRawEdge P) :
    (K.rootedAmbientMultiCosetRawGraph A hcard hret root P).source
      (K.rootedLocalMultiCosetRawEdgeEquiv A root P e) =
    K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret root P
      ((K.rootedLocalMultiCosetRawGraph A hcard hret root P).source e) := by
  rcases e with ⟨b, edge⟩
  let f := K.rootedSingleCosetEGraphHom A b.1
    (P.proper b.1 b.2).subset root
  change
    Quotient.mk (K.rootedAmbientMultiCosetSetoid A hcard hret root P)
      (⟨b, ((K.subalphabetComponentSubgraph A root).singleCosetEGraph b.1).source
        (f.onEdge edge)⟩ :
        (K.subalphabetComponentSubgraph A root).MultiCosetRawVertex P) =
    Quotient.mk (K.rootedAmbientMultiCosetSetoid A hcard hret root P)
      (⟨b, f.onVertex
        (((K.intrinsicComponentLocalSlice A root).singleCosetEGraph b.1).source
          edge)⟩ :
        (K.subalphabetComponentSubgraph A root).MultiCosetRawVertex P)
  exact congrArg
    (fun v : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex b.1 =>
      (Quotient.mk (K.rootedAmbientMultiCosetSetoid A hcard hret root P)
        (⟨b, v⟩ :
          (K.subalphabetComponentSubgraph A root).MultiCosetRawVertex P)))
    (f.map_source edge)

/-- The genuine signed raw edge map preserves the full signed label,
not just its unsigned letter. -/
theorem rootedMultiCosetRawGraph_label_natural
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A)
    (e : (K.intrinsicComponentLocalSlice A root).MultiCosetRawEdge P) :
    (K.rootedAmbientMultiCosetRawGraph A hcard hret root P).label
      (K.rootedLocalMultiCosetRawEdgeEquiv A root P e) =
    (K.rootedLocalMultiCosetRawGraph A hcard hret root P).label e :=
  K.rootedLocalMultiCosetRawEdgeLabel_natural A root P e

/-- The genuine raw signed map COMMUTES WITH FORMAL EDGE REVERSAL.
The inverse token remains in its original B-summand and preserves
the source/local component tag exactly. -/
theorem rootedMultiCosetRawGraph_inv_natural
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A)
    (e : (K.intrinsicComponentLocalSlice A root).MultiCosetRawEdge P) :
    K.rootedLocalMultiCosetRawEdgeEquiv A root P
      ((K.rootedLocalMultiCosetRawGraph A hcard hret root P).inv e) =
    (K.rootedAmbientMultiCosetRawGraph A hcard hret root P).inv
      (K.rootedLocalMultiCosetRawEdgeEquiv A root P e) := by
  rcases e with ⟨b, edge⟩
  let f := K.rootedSingleCosetEGraphHom A b.1
    (P.proper b.1 b.2).subset root
  change
    (⟨b, f.onEdge
      (((K.intrinsicComponentLocalSlice A root).singleCosetEGraph b.1).inv
        edge)⟩ :
        (K.subalphabetComponentSubgraph A root).MultiCosetRawEdge P) =
    ⟨b, ((K.subalphabetComponentSubgraph A root).singleCosetEGraph b.1).inv
      (f.onEdge edge)⟩
  exact congrArg
    (fun e' =>
      (⟨b, e'⟩ :
        (K.subalphabetComponentSubgraph A root).MultiCosetRawEdge P))
    (f.map_inv edge)

/-- Entire RAW signed multi-coset graphs of the actual source-rooted
component and locally normalized component are isomorphic. This
is an honest labelled graph map on the exact quotient vertices
and on EVERY prequotient oriented signed edge token. -/
noncomputable def rootedMultiCosetRawGraphHom
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A) :
    LabelledGraphHom
      (K.rootedLocalMultiCosetRawGraph A hcard hret root P)
      (K.rootedAmbientMultiCosetRawGraph A hcard hret root P) where
  onVertex := K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret root P
  onEdge := K.rootedLocalMultiCosetRawEdgeEquiv A root P
  map_source := K.rootedMultiCosetRawGraph_source_natural
    A hcard hret root P
  map_inv := K.rootedMultiCosetRawGraph_inv_natural A hcard hret root P
  map_label := K.rootedMultiCosetRawGraph_label_natural A hcard hret root P

/-- The genuine raw source/local graph morphism is bijective on both
tagged quotient vertices and all oriented signed edge TOKENS. -/
theorem rootedMultiCosetRawGraphHom_bijective
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A) :
    Function.Bijective
      (K.rootedMultiCosetRawGraphHom A hcard hret root P).onVertex ∧
    Function.Bijective
      (K.rootedMultiCosetRawGraphHom A hcard hret root P).onEdge := by
  exact ⟨(K.rootedLocalMultiCosetVertexQuotientEquiv
      A hcard hret root P).bijective,
    (K.rootedLocalMultiCosetRawEdgeEquiv A root P).bijective⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
