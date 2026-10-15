import PSTSEPPA.ABO.LabelledMulEquivAugmentedClusterIso
import PSTSEPPA.ABO.SourceLiteralY1TaggedCosetAttachments

/-!
# Actual literal T(Y₁) ↔ SourceH₁ original type-(1) augmented-cluster signed graph

Corrected first-rank ABO type-(1) objects begin with a cluster
of genuine proper-alphabet subgroup pieces in the real source
transition group and attach ONE full B-left coset at a specified
cluster vertex. The paper's literal group is T(Y₁); our independent
SourceH₁ model is labelled-group-isomorphic to it, but merely
2-retractable and not assumed globally retractable.

Instantiate the generic exact labelled-group isomorphism theorem
for augmented clusters: every original subgroup piece and
new attached B-left coset point and signed oriented old/new edge
token matches, with full formal inverse and label compatibility.
Unlike the quotient-stability augmented-cluster theorem, this
source-specific bridge requires NO unsupported global group
retractability. It is valid for arbitrary finite cluster family P,
all B (including ∅), signed loops and nonfaithful generators.

This is the TRUE geometric PRECOMPLETION type-(1) bridge.
Proving exact selected original (A,P,B,v) stage-index equivalence,
locally paired legality of missing-loop completion, all selected
Z₁ family coverage, higher ranks and PSTS EPPA are separate gates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Literal printed H₁=T(Y₁) to SourceH₁ signed augmented
cluster map, for ANY genuine original cluster family P, B,
and attached B-left coset anchor. All group coordinates are
transported by the true generator-preserving group isomorphism. -/
noncomputable def sourceLiteralY1Type1AugmentedClusterGraphHom
    (src dst : ι → V)
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι)
    (v : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      (P.augmentedToLabelledGraph
        (sourceLiteralY1 src dst).transitionSubgroupGenerator B v)
      (P.augmentedToLabelledGraph
        (sourceH1Generator src dst) B
        ((sourceH1EquivLiteralY1Transition src dst).symm v)) :=
  labelledMulEquivAugmentedClusterHom
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1Generator src dst)
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    P B v

/-- Every original paper/source first-rank type-(1) augmented
cluster under the TRUE labelled group equivalence is genuinely
bijective ON VERTICES AND FULL ORIENTED SIGNED OLD+NEW EDGE TOKENS.
This is strictly stronger than matching untagged group coordinates. -/
theorem sourceLiteralY1Type1AugmentedClusterGraphHom_bijective
    (src dst : ι → V)
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι)
    (v : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Bijective
      (sourceLiteralY1Type1AugmentedClusterGraphHom
        src dst P B v).onVertex ∧
    Function.Bijective
      (sourceLiteralY1Type1AugmentedClusterGraphHom
        src dst P B v).onEdge :=
  labelledMulEquivAugmentedClusterHom_bijective
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1Generator src dst)
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    P B v

end ABO
end PSTSEPPA
