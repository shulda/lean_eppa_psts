import PSTSEPPA.ABO.OriginalRootedAComponentSurjectiveCover

/-!
# Every literal first-rank H old A-root has a G root covering its A-component

In the corrected ABO Theorem 4.7 setup the H-level old
skeleton for the true printed T(Y₁) has ALL real H group
vertices but only the original signed input edges.
A selected original H old A-component is identified
by one original H skeleton root.

The actual first-rank labelled quotient
    Q : T(X₂^all) ↠ T(Y₁)
is surjective on its full group, but it is only 1-stable.
We cannot claim that the full original G pullback is
A-connected or that an A-component map is injective
for a two-letter A.

Instead we prove the exact source-selection statement:
for EVERY selected genuine H old root and EVERY A,
there is a chosen REAL G old skeleton point above it
whose ONE original A-component surjects onto the
specified H original A-component on ALL OLD vertices
and ALL formally oriented signed A-edge tokens.
The construction chooses one lift of the H root by
the already certified honest G/H old covering; path
lifting provides the rest with no extra assumptions.

This is precisely the source-compatible existential
ROOTED coverage (not ambient A-component injectivity)
needed to align the selected G and H original covers
in the first actual rank-two application.

We do not yet construct the required normalized
Cayley(G[A])→completed-H-root-stage morphism, prove
the R8 bridge clause, Condition 5.2 at rank two,
higher induction or ordinary finite PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Every genuine original incomplete H=T(Y₁)
skeleton root lifts to a true original G=T(X₂^all)
root covering the ENTIRE chosen H A-component
on real signed OLD vertices and edge tokens.

This does NOT require injectivity or connectedness
of the whole group-pullback old graph, and it
does not confuse the chosen A-component with its
potentially larger ambient A-generated coset. -/
theorem sourceLiteralY1X2AllOriginal_eachHRoot_AComponent_cover
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (hRoot : (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex) :
    ∃ gRoot : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex,
      (sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex gRoot = hRoot ∧
      Function.Surjective
        ((sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotient_intrinsicBComponentVertexMap
            (sourceLiteralY1X2AllToY1 src dst) A gRoot) ∧
      Function.Surjective
        ((sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotient_intrinsicBComponentEdgeMap
            (sourceLiteralY1X2AllToY1 src dst) A gRoot) := by
  obtain ⟨gRoot, hMap⟩ :=
    sourceLiteralY1X2AllOriginalToY1_vertex_surjective
      src dst base hRoot
  exact ⟨gRoot, hMap,
    sourceLiteralY1X2AllOriginal_AComponentVertex_surjective
      src dst base A gRoot,
    sourceLiteralY1X2AllOriginal_AComponentEdge_surjective
      src dst base A gRoot⟩

end ABO
end PSTSEPPA
