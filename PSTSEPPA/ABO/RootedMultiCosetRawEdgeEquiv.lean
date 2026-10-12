import PSTSEPPA.ABO.RootedSingleCosetEGraphIso
import PSTSEPPA.ABO.MultiCosetRawEdges

/-!
# Component-tagged raw signed edges under genuine source/local normalization

For the ACTUAL rooted A-component of an incomplete Γ-Cayley skeleton,
the certified single-B EGraph isomorphism (the prerequisite #377)
induces an equivalence on the disjoint union of the directed edge tokens
of all B-coset extensions, for any family P of proper subalphabets B⊂A.

Crucially this map keeps the outer alphabet B TAG unchanged and maps the
true oriented signed edges inside that summand. It neither identifies
distinct connected-component tags nor adds missing old edges.

This prepares transport of the full source-and-label edge quotient.
That quotient itself, its glued-vertex incidence and the target/inverse
congruence are separate obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- An equivalence of the WHOLE genuine raw oriented signed-edge
universe, preserving the literal outer B-index of each constituent.
It is a disjoint union of actual signed single-coset EGraph edge
bijections, not an ambient-coordinate quotient. -/
noncomputable def rootedLocalMultiCosetRawEdgeEquiv
    (A : Finset ι) (root : K.Vertex) (P : CosetFamilySpec A) :
    (K.intrinsicComponentLocalSlice A root).MultiCosetRawEdge P ≃
      (K.subalphabetComponentSubgraph A root).MultiCosetRawEdge P :=
  Equiv.sigmaCongrRight (fun b =>
    Equiv.ofBijective
      (K.rootedSingleCosetEGraphHom A b.1
        (P.proper b.1 b.2).subset root).onEdge
      (K.rootedSingleCosetEGraphHom_bijective A b.1
        (P.proper b.1 b.2).subset root).2)

/-- Transport of each raw signed edge uses the TRUE corresponding
single-coset EGraph morphism without changing its outer alphabet tag. -/
theorem rootedLocalMultiCosetRawEdgeEquiv_apply
    (A : Finset ι) (root : K.Vertex) (P : CosetFamilySpec A)
    (e :
      (K.intrinsicComponentLocalSlice A root).MultiCosetRawEdge P) :
    K.rootedLocalMultiCosetRawEdgeEquiv A root P e =
      ⟨e.1,
        (K.rootedSingleCosetEGraphHom A e.1.1
          (P.proper e.1.1 e.1.2).subset root).onEdge e.2⟩ :=
  rfl

/-- The raw edge equivalence preserves the entire signed label,
not merely its generator or its image in the ambient group. -/
theorem rootedLocalMultiCosetRawEdgeLabel_natural
    (A : Finset ι) (root : K.Vertex) (P : CosetFamilySpec A)
    (e :
      (K.intrinsicComponentLocalSlice A root).MultiCosetRawEdge P) :
    (K.subalphabetComponentSubgraph A root).multiCosetRawEdgeLabel P
      (K.rootedLocalMultiCosetRawEdgeEquiv A root P e) =
    (K.intrinsicComponentLocalSlice A root).multiCosetRawEdgeLabel P e := by
  rcases e with ⟨b, edge⟩
  change
    ((K.subalphabetComponentSubgraph A root).singleCosetEGraph b.1).label
      ((K.rootedSingleCosetEGraphHom A b.1
        (P.proper b.1 b.2).subset root).onEdge edge) =
    ((K.intrinsicComponentLocalSlice A root).singleCosetEGraph b.1).label edge
  exact (K.rootedSingleCosetEGraphHom A b.1
    (P.proper b.1 b.2).subset root).map_label edge

end CayleySubgraphSpec
end ABO
end PSTSEPPA
