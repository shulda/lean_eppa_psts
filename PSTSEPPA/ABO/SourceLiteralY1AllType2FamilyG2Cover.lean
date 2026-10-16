import PSTSEPPA.ABO.SourceLiteralY1SelectedType2ActualG2Action
import PSTSEPPA.ABO.DependentDisjointWordCongruence
import PSTSEPPA.ABO.CompleteStageWordCongruenceReachableCover

/-!
# The ENTIRE authentic selected off-B type-(2) paper T(Y₁) action family

The corrected first-rank ABO Section-5 type-(2) stages include
EVERY rank-two original-paper rooted A-component, every true
proper B ⊊ A (including empty B), and every genuine old
component-tagged quotient vertex z OUTSIDE the entire B-constituent.
The new full B-coset is attached at z, and only absent signed
stationary loops are added to legally complete the action.

The previous certified or candidate single-stage G₂ theorem
identifies the exact old/fresh action of each such stage with
one genuine input-derived G₂-covered source-local fibre.
Here we assemble ALL these literal printed type-(2) stages into
one dependent disjoint action, never identifying different
(original basepoint,A,root,B,z) tags or equal-coordinate old vertices.
This source code proves signed whole-family word-value congruence
and true based Cayley(G₂) morphisms with exact vertex/edge ranges.

This TYPE-(2) family is only one of the three corrected paper
Z₁ families; assembling the full three-kind selected Z₁
action and checking history/equivariance remain separate.
No global H₁ retractability or arbitrary-rank PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The exact selected PRINTED type-(2) index: original input
basepoint, genuine rank-two A, actual paper T(Y₁) A-root,
proper B and old component-tagged quotient vertex off B.
All such indices are retained, including B empty. -/
abbrev sourceLiteralY1Type2Index (src dst : ι → V) :=
  Σ base : V,
    Σ a : {A : Finset ι // A.card = 2},
      Σ root : (sourceLiteralY1 src dst).transitionGroup,
        Σ b : {B : Finset ι //
          B ∈ (allProperCosetFamily a.1).alphabets},
          LiteralPaperSelectedOffBPoint
            src dst base a.1 a.2 root b.1 b.2

/-- The actual old/fresh completed-stage vertex carrier,
depending on the ALL-PROPER coset gluing Setoid and true
ambient group value of the specified tagged old root. -/
abbrev sourceLiteralY1Type2StageVertex
    (src dst : ι → V)
    (j : sourceLiteralY1Type2Index src dst) :=
  IsolatedCosetGluing.Vertex
    (Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst j.1 j.2.1.1 j.2.1.2 j.2.2.1
      (allProperCosetFamily j.2.1.1)))
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    j.2.2.2.1.1
    (sourceLiteralY1SelectedRootAmbientValue
      src dst j.1 j.2.1.1 j.2.1.2 j.2.2.1
      (allProperCosetFamily j.2.1.1) j.2.2.2.2.vertex)

/-- The actual dependent disjoint carrier of EVERY original
printed off-B type-(2) stage, preserving original index tags
and the fresh/old vertex separation within each stage. -/
abbrev sourceLiteralY1AllType2FamilyVertex (src dst : ι → V) :=
  Σ j : sourceLiteralY1Type2Index src dst,
    sourceLiteralY1Type2StageVertex src dst j

/-- ONE completed signed EGraph for ALL actually selected
printed type-(2) stages, tagged by their genuine original
base, A-component, B and old off-B quotient vertex. -/
noncomputable def sourceLiteralY1AllType2FamilyStage
    (src dst : ι → V) :
    CompleteEGraph
      (sourceLiteralY1AllType2FamilyVertex src dst)
      (ActionEdge (sourceLiteralY1AllType2FamilyVertex src dst) ι) ι :=
  dependentDisjointStage
    (fun j : sourceLiteralY1Type2Index src dst =>
      literalPaperSelectedOffBCompletedStage
        src dst j.1 j.2.1.1 j.2.1.2 j.2.2.1
        j.2.2.2.1.1 j.2.2.2.1.2 j.2.2.2.2)

/-- Actual equality of arbitrary finite input-derived G₂
signed-word values acts identically at EVERY old or fresh
component-tagged vertex of the ENTIRE printed type-(2)
selected family, not merely at one specially chosen stage. -/
theorem sourceG2LiteralY1AllType2Family_wordValue_congr
    (src dst : ι → V)
    (p q : LabelWord ι)
    (hpq :
      PSTS.SignedWord.evalGroup (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup (sourceAllLocalG2Generator src dst) q) :
    ∀ x : sourceLiteralY1AllType2FamilyVertex src dst,
      (sourceLiteralY1AllType2FamilyStage src dst).followWord x p =
      (sourceLiteralY1AllType2FamilyStage src dst).followWord x q := by
  exact (dependentDisjointStage_wordEquality_all_iff
    (fun j : sourceLiteralY1Type2Index src dst =>
      literalPaperSelectedOffBCompletedStage
        src dst j.1 j.2.1.1 j.2.1.2 j.2.2.1
        j.2.2.2.1.1 j.2.2.2.1.2 j.2.2.2.2) p q).mpr (by
    intro j x
    exact literalPaperSelectedOffB_G2_wordValue_congr
      src dst j.1 j.2.1.1 j.2.1.2 j.2.2.1
      j.2.2.2.1.1 j.2.2.2.1.2 j.2.2.2.2
      p q hpq x)

/-- Based concrete signed Cayley(G₂) morphism into the
entire genuine paper type-(2) dependent disjoint action. -/
noncomputable def sourceG2LiteralY1AllType2FamilyCayleyHom
    (src dst : ι → V)
    (u : sourceLiteralY1AllType2FamilyVertex src dst) :
    LabelledGraphHom
      (cayleyGraph (sourceAllLocalG2Generator src dst)).toEGraph.toLabelledGraph
      (sourceLiteralY1AllType2FamilyStage src dst).toEGraph.toLabelledGraph :=
  (sourceLiteralY1AllType2FamilyStage src dst).cayleyCoverFromWordCongruence
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1AllType2Family_wordValue_congr src dst) u

/-- Every based Cayley(G₂) morphism starts at the requested
genuine original paper old/fresh tagged type-(2) stage vertex. -/
theorem sourceG2LiteralY1AllType2FamilyCayleyHom_one
    (src dst : ι → V)
    (u : sourceLiteralY1AllType2FamilyVertex src dst) :
    (sourceG2LiteralY1AllType2FamilyCayleyHom src dst u).onVertex 1 = u :=
  (sourceLiteralY1AllType2FamilyStage src dst).cayleyCoverFromWordCongruence_one
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1AllType2Family_wordValue_congr src dst) u

/-- The Cayley(G₂) image hits exactly the reachable vertices
of the specified genuine original selected type-(2) stage
component, without spanning unrelated indices. -/
theorem sourceG2LiteralY1AllType2FamilyCayleyHom_vertex_range
    (src dst : ι → V)
    (u : sourceLiteralY1AllType2FamilyVertex src dst) :
    Set.range (sourceG2LiteralY1AllType2FamilyCayleyHom
      src dst u).onVertex =
      {v : sourceLiteralY1AllType2FamilyVertex src dst |
        (sourceLiteralY1AllType2FamilyStage src dst).Reachable u v} :=
  (sourceLiteralY1AllType2FamilyStage src dst).cayleyCoverFromWordCongruence_vertex_range
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1AllType2Family_wordValue_congr src dst) u

/-- Every formally oriented edge token, positive or negative
(including legally inserted fixed loops), is hit whenever
its old/fresh source lies in the requested reachable component. -/
theorem sourceG2LiteralY1AllType2FamilyCayleyHom_edge_range
    (src dst : ι → V)
    (u : sourceLiteralY1AllType2FamilyVertex src dst) :
    Set.range
      (sourceG2LiteralY1AllType2FamilyCayleyHom src dst u).onEdge =
      {e : ActionEdge (sourceLiteralY1AllType2FamilyVertex src dst) ι |
        (sourceLiteralY1AllType2FamilyStage src dst).Reachable u
          ((sourceLiteralY1AllType2FamilyStage src dst).source e)} :=
  (sourceLiteralY1AllType2FamilyStage src dst).cayleyCoverFromWordCongruence_edge_range
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1AllType2Family_wordValue_congr src dst) u

end ABO
end PSTSEPPA
