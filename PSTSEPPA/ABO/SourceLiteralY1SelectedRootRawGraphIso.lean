import PSTSEPPA.ABO.SourceLiteralY1RootSingleCosetSignedEdges
import PSTSEPPA.ABO.SourceH1OriginalRankTwoRawTargetCongruence
import PSTSEPPA.ABO.RootedMultiCosetRawGraphNaturality

/-!
# Actual selected paper T(Y₁) / source H₁ rooted rank-two RAW signed EGraph geometry

All ingredients are now certified on main: an actual signed old-root
A-component graph isomorphism, its full component-tagged attached B-coset
family natural in B, the EXACT rank-two intersection-supported gluing
Setoid, and all signed OLD and NEW single-B/raw edge bijections.

We show directly that the already-certified equivalence of glued quotient
vertices sends every raw paper edge's genuine source to its corresponding
source-H₁ raw edge's source, including B=∅, signed inverses, loops,
repeated labels and absent original edges. This produces a true vertex-
and-oriented-edge-bijective labelled RAW multigraph morphism. No
ambient group-coordinate equality is substituted for glued vertex equality.

The edge source+signed-label quotient and selected completed EGraph
will be constructed separately by transferring the independently
certified original source-H₁ rank-two target congruence.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Genuine original paper selected-root RAW graph:
vertices are quotiented by the certified precise (B∩C)-support
Setoid; signed edge tokens have not yet been quotient-identified. -/
noncomputable abbrev sourceLiteralY1SelectedRootRawGraph
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :=
  (sourceLiteralY1DirectRootComponent src dst base A root).multiCosetRawGraphOfSetoid
    P (sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root P)

/-- On each genuine alphabet-and-intrinsic-component-tagged raw point,
the checked selected-root quotient vertex equivalence is EXACTLY
the class of its separately certified attached B-coset transport. -/
theorem sourceLiteralY1RootToH1MultiCosetVertexEquiv_mk
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (p : (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawVertex P) :
    sourceLiteralY1RootToH1MultiCosetVertexEquiv src dst base A hcard root P
      (Quotient.mk (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root P) p) =
    Quotient.mk
      (sourceH1OriginalRootMultiCosetSetoid src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root) P)
      (sourceLiteralY1DirectRootMultiCosetRawVertexEquiv
        src dst base A root P p) := by
  rfl

/-- The ACTUAL selected paper→source signed raw edge bijection
preserves the source INCIDENCE over the exact two vertex-quotient
Setoids. This cannot be concluded from group coset coordinates. -/
theorem sourceLiteralY1SelectedRootRawGraph_source_natural
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (e : (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawEdge P) :
    (sourceH1OriginalRankTwoRootRawGraph src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root) P).source
      (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv src dst base A root P e) =
    (sourceLiteralY1RootToH1MultiCosetVertexEquiv
      src dst base A hcard root P)
      ((sourceLiteralY1SelectedRootRawGraph
        src dst base A hcard root P).source e) := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  let rootK := (sourceH1EquivLiteralY1Transition src dst).symm root
  let K := sourceH1OriginalRootComponent src dst base A rootK
  let sL := sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root P
  let sK := sourceH1OriginalRootMultiCosetSetoid src dst base A hcard rootK P
  change
    Quotient.mk sK
      (⟨(sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv src dst base A root P e).1,
        (K.singleCosetEGraph
          (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv src dst base A root P e).1.1).source
          (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv src dst base A root P e).2⟩ :
          K.MultiCosetRawVertex P) =
    (sourceLiteralY1RootToH1MultiCosetVertexEquiv
      src dst base A hcard root P)
      (Quotient.mk sL
        (⟨e.1, (L.singleCosetEGraph e.1.1).source e.2⟩ :
          L.MultiCosetRawVertex P))
  rw [sourceLiteralY1RootToH1MultiCosetVertexEquiv_mk]
  exact congrArg (Quotient.mk sK)
    (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv_source
      src dst base A root P e).symm

/-- Genuine original paper-to-source labelled RAW multigraph
homomorphism: already correctly glued vertices, but still
separately tagged raw old/new directed signed edge tokens. -/
noncomputable def sourceLiteralY1SelectedRootRawGraphHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    LabelledGraphHom
      (sourceLiteralY1SelectedRootRawGraph src dst base A hcard root P)
      (sourceH1OriginalRankTwoRootRawGraph src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root) P) where
  onVertex := sourceLiteralY1RootToH1MultiCosetVertexEquiv
    src dst base A hcard root P
  onEdge := sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv
    src dst base A root P
  map_source := sourceLiteralY1SelectedRootRawGraph_source_natural
    src dst base A hcard root P
  map_inv := sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv_inv
    src dst base A root P
  map_label := sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv_label
    src dst base A root P

/-- The original paper selected-root/source-H₁ selected-root
signed RAW graph comparison is bijective on both real glued
vertex carriers and all formal directed signed raw edge tokens. -/
theorem sourceLiteralY1SelectedRootRawGraphHom_bijective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    Function.Bijective
      (sourceLiteralY1SelectedRootRawGraphHom
        src dst base A hcard root P).onVertex ∧
    Function.Bijective
      (sourceLiteralY1SelectedRootRawGraphHom
        src dst base A hcard root P).onEdge :=
  ⟨(sourceLiteralY1RootToH1MultiCosetVertexEquiv
      src dst base A hcard root P).bijective,
    (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv
      src dst base A root P).bijective⟩

end ABO
end PSTSEPPA
