import PSTSEPPA.ABO.SourceLiteralY1AllType2FamilyG2Cover
import PSTSEPPA.ABO.SourceLiteralY1AllType1FamilyG2Cover
import PSTSEPPA.ABO.SourceLiteralY1SelectedPlainG2CayleyCover
import PSTSEPPA.ABO.SourceOriginalH1Z1ThreeFamilyAction

/-!
# A single genuine literal T(Y₁) THREE-KIND selected first-rank signed action

Corrected ABO Definition 5.3 at the first rank uses three actual
geometric kinds of legally COMPLETE signed stages:
  0. original-rooted ordinary P_A multi-coset completion;
  1. an anchored augmented P-cluster;
  2. an old component-tagged quotient off-B root with a fresh full
     B-left coset attached at its true group coordinate.

The previous certified or candidate results construct these
structures DIRECTLY in the printed T(Y₁), using the original
incomplete input signed edge support, not a fake X₁ completion.
All old/fresh, B-component, root and basepoint tags remain distinct.

We assemble all such actual PRINTED stages with their real
signed oriented action-edge tokens into one dependent disjoint
complete EGraph. Its entire arbitrary chronological word-action
congruence is controlled by the same explicitly constructed
finite original-input-dependent source group G₂. Based Cayley(G₂)
maps cover exactly the reachable vertices AND signed edge tokens.

The resulting superfamily retains redundant original-rooted
indices, rather than claiming a canonical representative
system or the yet-unproved full Definition-5.3 choice
equivariance. Corrected Condition 5.2, Theorem 4.7, higher
Yₖ/Zₖ, reflecting group and concrete fibre-MAX→PSTS EPPA
are NOT deduced from this first-rank G₂ action theorem.
-/

namespace PSTSEPPA
namespace ABO

universe uι uV
variable {ι : Type uι} {V : Type uV}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Every actual original printed rank-two A-root of the
input-edge preimage provides an ordinary completed P_A stage.
The index retains its original base vertex, alphabet and
literal T(Y₁) root, even if redundant. -/
abbrev sourceLiteralY1PlainStageIndex (src dst : ι → V) :=
  Σ base : V,
    Σ a : {A : Finset ι // A.card = 2},
      (sourceLiteralY1 src dst).transitionGroup

/-- The literal redundant three-kind Z₁ index selection;
there is no ambient-coordinate collapse of separate stages. -/
abbrev sourceLiteralY1ThreeKindIndex (src dst : ι → V) :=
  (sourceLiteralY1PlainStageIndex src dst) ⊕
    ((sourceLiteralY1Type1Index src dst) ⊕
      (sourceLiteralY1Type2Index src dst))

/-- Actual unaugmented original paper completed P_A action,
at the specified TRUE original incomplete-cover root. -/
noncomputable def sourceLiteralY1PlainActionDatum
    (src dst : ι → V)
    (j : sourceLiteralY1PlainStageIndex src dst) :
    SourceCompleteActionDatum.{uι, uV} ι :=
  { Carrier := _
    stage := sourceLiteralY1SelectedRootPlainCompleteStage
      src dst j.1 j.2.1.1 j.2.1.2 j.2.2 }

/-- The genuine anchored old+fresh augmented type-(1) cluster
with its independently checked LEGAL signed completion. -/
noncomputable def sourceLiteralY1Type1ActionDatum
    (src dst : ι → V)
    (j : sourceLiteralY1Type1Index src dst) :
    SourceCompleteActionDatum.{uι, uV} ι :=
  { Carrier := ClusterSpec.augmentedType1Vertex j.2
    stage := ClusterSpec.augmentedType1Stage j.2 }

/-- The genuinely selected old off-B tagged quotient vertex,
fresh full B-left coset and LEGALLY completed printed type-(2)
signed action, with the true noninjective group anchor. -/
noncomputable def sourceLiteralY1Type2ActionDatum
    (src dst : ι → V)
    (j : sourceLiteralY1Type2Index src dst) :
    SourceCompleteActionDatum.{uι, uV} ι :=
  { Carrier := sourceLiteralY1Type2StageVertex src dst j
    stage := literalPaperSelectedOffBCompletedStage
      src dst j.1 j.2.1.1 j.2.1.2 j.2.2.1
      j.2.2.2.1.1 j.2.2.2.1.2 j.2.2.2.2 }

/-- Each actual printed original selected plain, type-(1) or
type-(2) stage is a genuine complete signed EGraph with
formal vertex/sign directed action-edge tokens. -/
noncomputable def sourceLiteralY1ThreeKindActionDatum
    (src dst : ι → V) :
    sourceLiteralY1ThreeKindIndex src dst →
      SourceCompleteActionDatum.{uι, uV} ι
  | .inl t => sourceLiteralY1PlainActionDatum src dst t
  | .inr (.inl t) => sourceLiteralY1Type1ActionDatum src dst t
  | .inr (.inr t) => sourceLiteralY1Type2ActionDatum src dst t

/-- The source-dependently typed vertex carrier of the whole
original printed three-kind completed family. -/
abbrev sourceLiteralY1ThreeKindStageVertex
    (src dst : ι → V)
    (j : sourceLiteralY1ThreeKindIndex src dst) :=
  (sourceLiteralY1ThreeKindActionDatum src dst j).Carrier

/-- The complete signed action of ALL original printed
rank-two proper-coset and augmented stages, retaining the
selected old/tagged coordinates of the actual input graph. -/
noncomputable def sourceLiteralY1ThreeKindStage
    (src dst : ι → V) :
    CompleteEGraph
      (Σ j : sourceLiteralY1ThreeKindIndex src dst,
        sourceLiteralY1ThreeKindStageVertex src dst j)
      (ActionEdge (Σ j : sourceLiteralY1ThreeKindIndex src dst,
        sourceLiteralY1ThreeKindStageVertex src dst j) ι) ι :=
  dependentDisjointStage
    (fun j : sourceLiteralY1ThreeKindIndex src dst =>
      (sourceLiteralY1ThreeKindActionDatum src dst j).stage)

/-- One concrete finite input-derived G₂ controls ALL actual
literal printed selected first-rank three-kind signed actions,
at EVERY old/fresh stage vertex, in every original index. -/
theorem sourceG2LiteralY1ThreeKind_wordValue_congr
    (src dst : ι → V)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ x : Σ j : sourceLiteralY1ThreeKindIndex src dst,
      sourceLiteralY1ThreeKindStageVertex src dst j,
      (sourceLiteralY1ThreeKindStage src dst).followWord x p =
      (sourceLiteralY1ThreeKindStage src dst).followWord x q := by
  apply (dependentDisjointStage_wordEquality_all_iff
    (fun j : sourceLiteralY1ThreeKindIndex src dst =>
      (sourceLiteralY1ThreeKindActionDatum src dst j).stage) p q).mpr
  intro j x
  cases j with
  | inl t =>
      exact sourceG2LiteralY1SelectedPlain_wordValue_congr
        src dst t.1 t.2.1.1 t.2.1.2 t.2.2 p q hpq x
  | inr s =>
      cases s with
      | inl t =>
          exact sourceG2LiteralY1Type1_wordValue_congr
            src dst t.1.1 t.1.2
            t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
            p q hpq x
      | inr t =>
          exact literalPaperSelectedOffB_G2_wordValue_congr
            src dst t.1 t.2.1.1 t.2.1.2 t.2.2.1
            t.2.2.2.1.1 t.2.2.2.1.2 t.2.2.2.2
            p q hpq x

/-- A based labelled signed Cayley(G₂) morphism into the
genuine combined printed plain + both augmented families. -/
noncomputable def sourceG2LiteralY1ThreeKindCayleyHom
    (src dst : ι → V)
    (u : Σ j : sourceLiteralY1ThreeKindIndex src dst,
      sourceLiteralY1ThreeKindStageVertex src dst j) :
    LabelledGraphHom
      (cayleyGraph (sourceAllLocalG2Generator src dst)).toEGraph.toLabelledGraph
      (sourceLiteralY1ThreeKindStage src dst).toEGraph.toLabelledGraph :=
  (sourceLiteralY1ThreeKindStage src dst).cayleyCoverFromWordCongruence
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1ThreeKind_wordValue_congr src dst) u

/-- The based Cayley map returns the selected actual printed
stage point at the finite source G₂ group identity. -/
theorem sourceG2LiteralY1ThreeKindCayleyHom_one
    (src dst : ι → V)
    (u : Σ j : sourceLiteralY1ThreeKindIndex src dst,
      sourceLiteralY1ThreeKindStageVertex src dst j) :
    (sourceG2LiteralY1ThreeKindCayleyHom src dst u).onVertex 1 = u :=
  (sourceLiteralY1ThreeKindStage src dst).cayleyCoverFromWordCongruence_one
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1ThreeKind_wordValue_congr src dst) u

/-- Exact reachable vertex image of the whole three-kind
printed G₂ Cayley covering. Original stage indices never
spuriously merge just because their group values agree. -/
theorem sourceG2LiteralY1ThreeKindCayleyHom_vertex_range
    (src dst : ι → V)
    (u : Σ j : sourceLiteralY1ThreeKindIndex src dst,
      sourceLiteralY1ThreeKindStageVertex src dst j) :
    Set.range (sourceG2LiteralY1ThreeKindCayleyHom
      src dst u).onVertex =
      {v | (sourceLiteralY1ThreeKindStage src dst).Reachable u v} :=
  (sourceLiteralY1ThreeKindStage src dst).cayleyCoverFromWordCongruence_vertex_range
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1ThreeKind_wordValue_congr src dst) u

/-- Actual reachable oriented signed action-edge image,
both signs and every legally inserted fixed loop, in the
full three-kind printed stage family. -/
theorem sourceG2LiteralY1ThreeKindCayleyHom_edge_range
    (src dst : ι → V)
    (u : Σ j : sourceLiteralY1ThreeKindIndex src dst,
      sourceLiteralY1ThreeKindStageVertex src dst j) :
    Set.range (sourceG2LiteralY1ThreeKindCayleyHom
      src dst u).onEdge =
      {e : ActionEdge
        (Σ j : sourceLiteralY1ThreeKindIndex src dst,
          sourceLiteralY1ThreeKindStageVertex src dst j) ι |
        (sourceLiteralY1ThreeKindStage src dst).Reachable u
          ((sourceLiteralY1ThreeKindStage src dst).source e)} :=
  (sourceLiteralY1ThreeKindStage src dst).cayleyCoverFromWordCongruence_edge_range
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1ThreeKind_wordValue_congr src dst) u

end ABO
end PSTSEPPA
