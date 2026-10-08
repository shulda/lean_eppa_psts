import PSTSEPPA.ABO.ComponentMultiCosetEmbedding
import PSTSEPPA.ABO.ComponentSingleCosetHom

/-!
# Local multi-coset extension E-graph morphism

For the literal intrinsic B-component L of an admissible A-skeleton K,
the canonical map of multi-coset quotients (for the same lower family P)
extends from vertices to all signed directed edge tokens.

The raw edge map is the disjoint union of the checked single-C local
embedding maps. Equal raw edges in the source quotient map to equal
edges in the target quotient because the vertex map preserves glued
sources and every single-C map preserves signed labels.

The resulting labelled E-graph morphism is injective on vertices by
reflection of intersection support; deterministic E-graphs then force
injectivity also on formal directed edge tokens. This is a precise
multi-alphabet local embedding, not injectivity into ambient Cayley.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Map an oriented raw edge from the multi-alphabet extension of
an intrinsic B-component into the corresponding original-K summand. -/
noncomputable def componentMultiCosetRawEdgeMap
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (e : (K.subalphabetComponentSubgraph B root).MultiCosetRawEdge P) :
    K.MultiCosetRawEdge (P.intoLarger hBA) :=
  ⟨⟨e.1.1, e.1.2⟩,
    K.componentSubgraphSingleCosetEdgeMap B e.1.1
      (P.proper e.1.1 e.1.2).subset root e.2⟩

/-- Raw source is transported by the previously checked local quotient
vertex map. -/
theorem componentMultiCosetRawEdgeMap_source
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : (K.subalphabetComponentSubgraph B root).MultiCosetRawEdge P) :
    K.multiCosetRawEdgeSource (P.intoLarger hBA) hadm hgen hret
        (K.componentMultiCosetRawEdgeMap B hBA root P e) =
      K.componentMultiCosetVertexMap B hBA root P hadm hgen hret
        ((K.subalphabetComponentSubgraph B root).multiCosetRawEdgeSource
          P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
          hgen hret e) := by
  rcases e with ⟨C, e⟩
  change
    K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret C.1 C.2
      ((K.singleCosetEGraph C.1).source
        (K.componentSubgraphSingleCosetEdgeMap B C.1
          (P.proper C.1 C.2).subset root e)) =
    K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret C.1 C.2
      (K.componentSubgraphAttachedMap B C.1
        (P.proper C.1 C.2).subset root
        (((K.subalphabetComponentSubgraph B root).singleCosetEGraph C.1).source e))
  exact congrArg
    (K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret C.1 C.2)
    (K.componentSubgraphSingleCosetEdgeMap_source B C.1
      (P.proper C.1 C.2).subset root e)

/-- The local raw edge map preserves signed labels exactly. -/
theorem componentMultiCosetRawEdgeMap_label
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (e : (K.subalphabetComponentSubgraph B root).MultiCosetRawEdge P) :
    K.multiCosetRawEdgeLabel (P.intoLarger hBA)
        (K.componentMultiCosetRawEdgeMap B hBA root P e) =
      (K.subalphabetComponentSubgraph B root).multiCosetRawEdgeLabel P e := by
  rcases e with ⟨C, e⟩
  exact K.componentSubgraphSingleCosetEdgeMap_label B C.1
    (P.proper C.1 C.2).subset root e

/-- Identification by glued source and signed label is respected
by inclusion of the actual B-component into the global skeleton. -/
theorem componentMultiCosetRawEdgeMap_congr
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e f : (K.subalphabetComponentSubgraph B root).MultiCosetRawEdge P)
    (hef :
      (K.subalphabetComponentSubgraph B root).MultiCosetRawEdgeRelated
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret e f) :
    K.MultiCosetRawEdgeRelated (P.intoLarger hBA) hadm hgen hret
      (K.componentMultiCosetRawEdgeMap B hBA root P e)
      (K.componentMultiCosetRawEdgeMap B hBA root P f) := by
  rcases hef with ⟨hs, hl⟩
  constructor
  · calc
      K.multiCosetRawEdgeSource (P.intoLarger hBA) hadm hgen hret
          (K.componentMultiCosetRawEdgeMap B hBA root P e) =
        K.componentMultiCosetVertexMap B hBA root P hadm hgen hret
          ((K.subalphabetComponentSubgraph B root).multiCosetRawEdgeSource
            P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
            hgen hret e) :=
        K.componentMultiCosetRawEdgeMap_source
          B hBA root P hadm hgen hret e
      _ = K.componentMultiCosetVertexMap B hBA root P hadm hgen hret
          ((K.subalphabetComponentSubgraph B root).multiCosetRawEdgeSource
            P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
            hgen hret f) :=
        congrArg _ hs
      _ = K.multiCosetRawEdgeSource (P.intoLarger hBA) hadm hgen hret
          (K.componentMultiCosetRawEdgeMap B hBA root P f) :=
        (K.componentMultiCosetRawEdgeMap_source
          B hBA root P hadm hgen hret f).symm
  · calc
      K.multiCosetRawEdgeLabel (P.intoLarger hBA)
          (K.componentMultiCosetRawEdgeMap B hBA root P e) =
        (K.subalphabetComponentSubgraph B root).multiCosetRawEdgeLabel P e :=
        K.componentMultiCosetRawEdgeMap_label B hBA root P e
      _ = (K.subalphabetComponentSubgraph B root).multiCosetRawEdgeLabel P f := hl
      _ = K.multiCosetRawEdgeLabel (P.intoLarger hBA)
          (K.componentMultiCosetRawEdgeMap B hBA root P f) :=
        (K.componentMultiCosetRawEdgeMap_label B hBA root P f).symm

/-- Descended map of all multi-coset oriented edge quotient classes. -/
noncomputable def componentMultiCosetEdgeMap
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : (K.subalphabetComponentSubgraph B root).MultiCosetEdgeVertexIncidenceQuotient
      P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
      hgen hret) :
    K.MultiCosetEdgeVertexIncidenceQuotient
      (P.intoLarger hBA) hadm hgen hret :=
  Quotient.liftOn e
    (fun raw =>
      Quotient.mk (K.multiCosetRawEdgeSetoid (P.intoLarger hBA) hadm hgen hret)
        (K.componentMultiCosetRawEdgeMap B hBA root P raw))
    (by
      intro p q hpq
      apply Quotient.sound
      exact K.componentMultiCosetRawEdgeMap_congr
        B hBA root P hadm hgen hret p q hpq)

/-- Descended edge source commutes with the vertex comparison map. -/
theorem componentMultiCosetEdgeMap_source
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : (K.subalphabetComponentSubgraph B root).MultiCosetEdgeVertexIncidenceQuotient
      P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
      hgen hret) :
    (K.multiCosetEGraph (P.intoLarger hBA) hadm hgen hret).source
      (K.componentMultiCosetEdgeMap B hBA root P hadm hgen hret e) =
    K.componentMultiCosetVertexMap B hBA root P hadm hgen hret
      (((K.subalphabetComponentSubgraph B root).multiCosetEGraph
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret).source e) := by
  induction e using Quotient.inductionOn with
  | h raw =>
      exact K.componentMultiCosetRawEdgeMap_source
        B hBA root P hadm hgen hret raw

/-- Signed labels on all directed edge classes are preserved. -/
theorem componentMultiCosetEdgeMap_label
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : (K.subalphabetComponentSubgraph B root).MultiCosetEdgeVertexIncidenceQuotient
      P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
      hgen hret) :
    (K.multiCosetEGraph (P.intoLarger hBA) hadm hgen hret).label
      (K.componentMultiCosetEdgeMap B hBA root P hadm hgen hret e) =
    ((K.subalphabetComponentSubgraph B root).multiCosetEGraph
      P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
      hgen hret).label e := by
  induction e using Quotient.inductionOn with
  | h raw =>
      exact K.componentMultiCosetRawEdgeMap_label B hBA root P raw

/-- The local edge map respects formal reversal on signed edge tokens. -/
theorem componentMultiCosetEdgeMap_inv
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : (K.subalphabetComponentSubgraph B root).MultiCosetEdgeVertexIncidenceQuotient
      P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
      hgen hret) :
    K.componentMultiCosetEdgeMap B hBA root P hadm hgen hret
      (((K.subalphabetComponentSubgraph B root).multiCosetEGraph
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret).inv e) =
    (K.multiCosetEGraph (P.intoLarger hBA) hadm hgen hret).inv
      (K.componentMultiCosetEdgeMap B hBA root P hadm hgen hret e) := by
  induction e using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨C, e⟩
      change
        K.multiCosetEdgeInclude (P.intoLarger hBA) hadm hgen hret C.1 C.2
          (K.componentSubgraphSingleCosetEdgeMap B C.1
            (P.proper C.1 C.2).subset root
            (((K.subalphabetComponentSubgraph B root).singleCosetEGraph C.1).inv e)) =
        K.multiCosetEdgeInclude (P.intoLarger hBA) hadm hgen hret C.1 C.2
          ((K.singleCosetEGraph C.1).inv
            (K.componentSubgraphSingleCosetEdgeMap B C.1
              (P.proper C.1 C.2).subset root e))
      exact congrArg
        (K.multiCosetEdgeInclude (P.intoLarger hBA) hadm hgen hret C.1 C.2)
        (K.componentSubgraphSingleCosetEdgeMap_inv B C.1
          (P.proper C.1 C.2).subset root e)

/-- Full local-to-global morphism of actual multi-coset E-graphs. -/
noncomputable def componentMultiCosetHom
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    LabelledGraphHom
      ((K.subalphabetComponentSubgraph B root).multiCosetEGraph
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret).toLabelledGraph
      (K.multiCosetEGraph (P.intoLarger hBA) hadm hgen hret).toLabelledGraph where
  onVertex := K.componentMultiCosetVertexMap B hBA root P hadm hgen hret
  onEdge := K.componentMultiCosetEdgeMap B hBA root P hadm hgen hret
  map_source := K.componentMultiCosetEdgeMap_source B hBA root P hadm hgen hret
  map_inv := K.componentMultiCosetEdgeMap_inv B hBA root P hadm hgen hret
  map_label := K.componentMultiCosetEdgeMap_label B hBA root P hadm hgen hret

/-- Local multi-coset morphism embeds quotient vertices. -/
theorem componentMultiCosetHom_vertex_injective
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Function.Injective
      (K.componentMultiCosetHom B hBA root P hadm hgen hret).onVertex :=
  K.componentMultiCosetVertexMap_injective B hBA root P hadm hgen hret

/-- Local multi-coset morphism embeds formal directed edge tokens too. -/
theorem componentMultiCosetHom_edge_injective
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Function.Injective
      (K.componentMultiCosetHom B hBA root P hadm hgen hret).onEdge :=
  LabelledGraphHom.edge_injective_of_vertex_injective
    (K.componentMultiCosetHom B hBA root P hadm hgen hret)
    (K.componentMultiCosetHom_vertex_injective B hBA root P hadm hgen hret)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
