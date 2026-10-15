import PSTSEPPA.ABO.LabelledMulEquivAugmentedClusterIso
import PSTSEPPA.ABO.AugmentedClusterTrivialStage
import PSTSEPPA.ABO.TrivialLoopCompletionIsomorphism

/-!
# Complete signed type-(1) augmented-cluster stages under labelled group isomorphisms

The true ABO anchored type-(1) stage is the old augmented Cayley
cluster plus a stationary loop for each missing signed label.
The old subgraph has paired positive and negative labels, so this
loop completion is legal for arbitrary labelled groups, without
global retractability.

Any generator-preserving GROUP ISOMORPHISM, rather than merely
a quotient, maps the true OLD cluster and attached B-left-coset
signed edges bijectively. Hence the canonical signed fixed-loop
completions are likewise vertex- and directed signed edge-
isomorphic. Real full chronological signed-word paths reflect
as well as preserve.

The result is generic and is designed for the independently
certified printed T(Y₁)≃*SourceH₁ first-rank type-(1) geometric
comparison. It does not by itself identify the selected stage
family or provide an action of a later-rank reflection group.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable (genΓ : ι → Γ) (genΔ : ι → Δ)
variable (E : Γ ≃* Δ)
variable (hgen : ∀ i : ι, E (genΓ i) = genΔ i)

/-- A genuine group isomorphism extends to the legally LOOP-COMPLETED
signed type-(1) augmented-cluster action. No missing original
nonloop edge is manufactured. -/
noncomputable def labelledMulEquivAugmentedTrivialStageHom
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    LabelledGraphHom
      (P.augmentedTrivialStage (gen := genΓ) B hBA v).toEGraph.toLabelledGraph
      (P.augmentedTrivialStage (gen := genΔ) B hBA (E v)).toEGraph.toLabelledGraph :=
  ((P.augmentedCayleySubgraph genΓ B hBA v).toEGraph).trivialLoopCompletionIsoHom
    ((P.augmentedCayleySubgraph genΔ B hBA (E v)).toEGraph)
    (labelledMulEquivAugmentedClusterHom genΓ genΔ E hgen P B v)
    (labelledMulEquivAugmentedClusterHom_bijective
      genΓ genΔ E hgen P B v).1
    (labelledMulEquivAugmentedClusterHom_bijective
      genΓ genΔ E hgen P B v).2
    (P.augmentedCayleySubgraph_locallyPairedLabels
      (gen := genΓ) B hBA v)
    (P.augmentedCayleySubgraph_locallyPairedLabels
      (gen := genΔ) B hBA (E v))

/-- The complete signed augmented stage isomorphism is BIJECTIVE
on every vertex AND oriented signed action-edge token, including
both orientations of its newly inserted stationary loops. -/
theorem labelledMulEquivAugmentedTrivialStageHom_bijective
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    Function.Bijective
      (labelledMulEquivAugmentedTrivialStageHom
        genΓ genΔ E hgen P B hBA v).onVertex ∧
    Function.Bijective
      (labelledMulEquivAugmentedTrivialStageHom
        genΓ genΔ E hgen P B hBA v).onEdge :=
  ((P.augmentedCayleySubgraph genΓ B hBA v).toEGraph).trivialLoopCompletionIsoHom_bijective
    ((P.augmentedCayleySubgraph genΔ B hBA (E v)).toEGraph)
    (labelledMulEquivAugmentedClusterHom genΓ genΔ E hgen P B v)
    (labelledMulEquivAugmentedClusterHom_bijective
      genΓ genΔ E hgen P B v).1
    (labelledMulEquivAugmentedClusterHom_bijective
      genΓ genΔ E hgen P B v).2
    (P.augmentedCayleySubgraph_locallyPairedLabels
      (gen := genΓ) B hBA v)
    (P.augmentedCayleySubgraph_locallyPairedLabels
      (gen := genΔ) B hBA (E v))

/-- Both complete actions realise exactly the same signed paths,
including all old/new proper-coset edges and completed fixed loops. -/
theorem labelledMulEquivAugmentedTrivialStageHom_follows_iff
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (x y : (P.augmentedCayleySubgraph genΓ B hBA v).Vertex)
    (w : LabelWord ι) :
    (P.augmentedTrivialStage (gen := genΓ) B hBA v).toEGraph.Follows x w y ↔
      (P.augmentedTrivialStage (gen := genΔ) B hBA (E v)).toEGraph.Follows
        ((labelledMulEquivAugmentedTrivialStageHom
          genΓ genΔ E hgen P B hBA v).onVertex x) w
        ((labelledMulEquivAugmentedTrivialStageHom
          genΓ genΔ E hgen P B hBA v).onVertex y) := by
  exact EGraph.follows_iff_bijective
    (labelledMulEquivAugmentedTrivialStageHom
      genΓ genΔ E hgen P B hBA v)
    (labelledMulEquivAugmentedTrivialStageHom_bijective
      genΓ genΔ E hgen P B hBA v).1
    (labelledMulEquivAugmentedTrivialStageHom_bijective
      genΓ genΔ E hgen P B hBA v).2 x y w

end ABO
end PSTSEPPA
