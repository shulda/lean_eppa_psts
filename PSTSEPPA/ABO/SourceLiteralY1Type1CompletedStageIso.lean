import PSTSEPPA.ABO.SourceLiteralY1Type1AugmentedClusterGraphIso
import PSTSEPPA.ABO.LabelledMulEquivAugmentedCompleteActionIso

/-!
# Real printed T(Y₁) versus SourceH₁ complete signed anchored type-(1) stages

The original signed augmented cluster graph in the literal
first-rank paper T(Y₁)=T(X₁ ⊔ copies of one-letter Cayley graphs)
is isomorphic to the corresponding actual SourceH₁ augmented
cluster, even though neither ambient group is globally retractable.

Both graphs have locally paired signed labels and therefore
can be legally completed by adding ONLY missing stationary loops,
including both inverse-oriented tokens at fixed loops. The
generic group-isomorphism complete-augmentation API upgrades the
concrete type-(1) morphism to an isomorphism of actual COMPLETE
signed EGraphs, on their genuine source-defined augmented
vertex carriers and formally oriented signed action edges.

No quotient by ambient group values, fake nonloop original
completion edges or unproved globally retractable H₁ is used.
This is a fibrewise type-(1) complete stage comparison. Exact
literal printed index family, entire Z₁ action and G₂ word
congruence, type-(2), higher ranks and PSTS EPPA are separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The true source-to-paper group isomorphism maps every
original anchored signed B-augmented cluster complete action
(including LEGAL missing-label fixed loops) bijectively. -/
noncomputable def sourceLiteralY1Type1CompletedStageHom
    (src dst : ι → V)
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      (P.augmentedTrivialStage
        (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
        B hBA v).toEGraph.toLabelledGraph
      (P.augmentedTrivialStage
        (gen := sourceH1Generator src dst) B hBA
        ((sourceH1EquivLiteralY1Transition src dst).symm v)).toEGraph.toLabelledGraph :=
  labelledMulEquivAugmentedTrivialStageHom
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1Generator src dst)
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    P B hBA v

/-- Actual type-(1) augmented stages over literal paper T(Y₁)
and SourceH₁ are bijective on EVERY augmented vertex and EVERY
formal directed signed action-edge token, including fresh loops. -/
theorem sourceLiteralY1Type1CompletedStageHom_bijective
    (src dst : ι → V)
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Bijective
      (sourceLiteralY1Type1CompletedStageHom
        src dst P B hBA v).onVertex ∧
    Function.Bijective
      (sourceLiteralY1Type1CompletedStageHom
        src dst P B hBA v).onEdge :=
  labelledMulEquivAugmentedTrivialStageHom_bijective
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1Generator src dst)
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    P B hBA v

/-- Every chronological signed word/path in a genuine literal
type-(1) augmented complete action is realised iff the same
word/path is realised between the transported SourceH₁ vertices.
This includes old/new B-coset edges and stationary fixed loops. -/
theorem sourceLiteralY1Type1CompletedStageHom_follows_iff
    (src dst : ι → V)
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : (sourceLiteralY1 src dst).transitionGroup)
    (x y : (P.augmentedCayleySubgraph
      (sourceLiteralY1 src dst).transitionSubgroupGenerator B hBA v).Vertex)
    (w : LabelWord ι) :
    (P.augmentedTrivialStage
      (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
      B hBA v).toEGraph.Follows x w y ↔
    (P.augmentedTrivialStage
      (gen := sourceH1Generator src dst) B hBA
      ((sourceH1EquivLiteralY1Transition src dst).symm v)).toEGraph.Follows
      ((sourceLiteralY1Type1CompletedStageHom
        src dst P B hBA v).onVertex x) w
      ((sourceLiteralY1Type1CompletedStageHom
        src dst P B hBA v).onVertex y) := by
  exact EGraph.follows_iff_bijective
    (sourceLiteralY1Type1CompletedStageHom src dst P B hBA v)
    (sourceLiteralY1Type1CompletedStageHom_bijective
      src dst P B hBA v).1
    (sourceLiteralY1Type1CompletedStageHom_bijective
      src dst P B hBA v).2 x y w

end ABO
end PSTSEPPA
