import PSTSEPPA.ABO.DependentDisjointFibreTransitionQuotient
import PSTSEPPA.ABO.SourceLiteralY1X2AllExactCayleyRanges

/-!
# Genuine literal T(X₂-all) quotient onto each original printed P_A stage

The actual first-rank printed graph
  X₂^all = Y₁ ⊔ (dependent disjoint real three-kind Z₁^all)
has a true transition group. Its certified right-summand
labelled surjection, followed by the independent generic
dependent-fibre restriction quotient, yields a concrete
generator-preserving SURJECTIVE map directly onto the
transition group of EVERY genuine original incomplete-input
rank-two ROOTED P_A proper-family LEGALLY completed stage.

This is a literal individual-fibre transition-group quotient;
it retains the original basepoint, A, true T(Y₁) root, every
component-tagged old intersection-support quotient point and
the formal signed action-edge tokens.

The resulting based Cayley(T(X₂^all)) morphism is proved to
reach exactly all vertices and all signed oriented edges in
the chosen plain completed-stage reachable component, and
the canonical word endpoint formula holds. This is precisely
the input needed for a following conditional B-coset bridge
lifting theorem from the complete stage back to its genuine
INCOMPLETE old P_A extension.

It is NOT the full exact equivariant Definition-5.3 selection,
nor itself Theorem 4.7's global embedding/bridge-freeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The LITERAL generated transition subgroup of the full
printed X₂^all surjects, preserving every original generator,
onto one exactly specified OLD P_A completed fibre. -/
noncomputable def sourceLiteralY1X2AllToPrintedPlainStage
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGroupQuotient
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).transitionSubgroupGenerator := by
  let j : sourceLiteralY1ThreeKindIndex src dst :=
    Sum.inl ⟨base, ⟨⟨A, hcard⟩, root⟩⟩
  exact (sourceLiteralY1X2AllToThreeKind src dst).comp
    (dependentDisjointStage_fibreTransitionQuotient
      (fun t : sourceLiteralY1ThreeKindIndex src dst =>
        (sourceLiteralY1ThreeKindActionDatum src dst t).stage) j)

/-- Based genuine signed Cayley map from the ACTUAL printed
X₂ transition group to the specified true OLD P_A complete
stage, without forgetting the chosen component-tagged root. -/
noncomputable def sourceLiteralY1X2AllPrintedPlainCayleyHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A))) :
    LabelledGraphHom
      (cayleyGraph (sourceLiteralY1X2AllGenerator src dst)).toEGraph.toLabelledGraph
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).toEGraph.toLabelledGraph :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).cayleyProjectionFromGroup
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).hom
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).map_gen
      u

/-- The actual second-transition group identity maps exactly
to the requested original tagged old coset-quotient point. -/
theorem sourceLiteralY1X2AllPrintedPlainCayleyHom_one
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A))) :
    (sourceLiteralY1X2AllPrintedPlainCayleyHom
      src dst base A hcard root u).onVertex 1 = u :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).cayleyProjectionFromGroup_one
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).hom
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).map_gen u

/-- The based Cayley image hits EXACTLY the signed-word
reachable old P_A plain-stage vertices; no unrelated
component-index-tagged roots are spuriously identified. -/
theorem sourceLiteralY1X2AllPrintedPlainCayleyHom_vertex_range
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A))) :
    Set.range (sourceLiteralY1X2AllPrintedPlainCayleyHom
      src dst base A hcard root u).onVertex =
      {v | (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).Reachable u v} :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).cayleyProjectionFromGroup_vertex_range_of_surjective
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).hom
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).map_gen
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).surjective u

/-- EVERY oriented signed action-edge token with reachable
source lies in the true based Cayley(T(X₂^all)) image,
including both inverse signs and newly added stationary loops. -/
theorem sourceLiteralY1X2AllPrintedPlainCayleyHom_edge_range
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A))) :
    Set.range (sourceLiteralY1X2AllPrintedPlainCayleyHom
      src dst base A hcard root u).onEdge =
      {e : ActionEdge
        (Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
          src dst base A hcard root (allProperCosetFamily A))) ι |
        (sourceLiteralY1SelectedRootPlainCompleteStage
          src dst base A hcard root).Reachable u
          ((sourceLiteralY1SelectedRootPlainCompleteStage
            src dst base A hcard root).source e)} :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).cayleyProjectionFromGroup_edge_range_of_surjective
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).hom
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).map_gen
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).surjective u

/-- Exact chronological signed-word endpoints in the ORIGINAL
printed selected rooted P_A complete stage. -/
theorem sourceLiteralY1X2AllPrintedPlainCayleyHom_word
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A)))
    (w : LabelWord ι) :
    (sourceLiteralY1X2AllPrintedPlainCayleyHom
      src dst base A hcard root u).onVertex
      (PSTS.SignedWord.evalGroup
        (sourceLiteralY1X2AllGenerator src dst) w) =
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).followWord u w :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).cayleyProjectionFromGroup_evalGroup
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).hom
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root).map_gen u w

end ABO
end PSTSEPPA
