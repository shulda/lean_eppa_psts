import PSTSEPPA.ABO.AugmentedClusterTrivialStage
import PSTSEPPA.ABO.AugmentedClusterPathInclusion
import PSTSEPPA.ABO.IsolatedCosetGluing

/-!
# A genuine full H[B] coset embeds in the NONISOLATED augmented cluster stage

The literal ABO augmented cluster is the UNION of the existing
proper cluster (which MAY ALREADY HAVE B-labelled signed edges)
with the complete ambient B-coset. Its missing-label completion
adds only stationary loops.

Here we construct the TRUE signed graph embedding of that newly
full H[B] coset into BOTH the actual augmented Cayley subgraph
and its legally loop-completed stage. All original signed
oriented edges of the full B-coset map to actual ORIGINAL
edges of the augmented graph before completion. In particular
this does not infer B-connectivity from equality of ambient
group values or invent any edges at an old multiCE root.

The stage embedding is injective on full-coset VERTICES.
No no-old-B-edge hypothesis appears, because existing B-edges
are preserved in the union rather than competing with an
independent duplicate at the same source.

This is the concrete canonical-cluster J required by the
general embedded-full-coset word-equality theorem. Extending
it to the HISTORY-SELECTED ORIGINAL component-tagged H CE
B-augmentation still requires the source signed B-component
canonical-cluster isomorphism and a correct whole-component
pushout/transport. No such history match is claimed here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {A : Finset ι}

namespace ClusterSpec

variable (P : ClusterSpec A)

/-- The actual complete B-coset injects as a SIGNED labelled
subgraph of the literal union of the original proper cluster
and the full B-coset. Both positive and inverse old edge
tokens are preserved, even if the proper cluster already
contains B-edges at the chosen gluing core. -/
noncomputable def fullBCosetToAugmentedSkeletonHom
    (gen : ι → Γ) (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph gen B v).toEGraph).toLabelledGraph
      (P.augmentedCayleySubgraph gen B hBA v).toLabelledGraph where
  onVertex p := ⟨p.1, Or.inr p.2⟩
  onEdge e := ⟨e.1, Or.inr e.2⟩
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

/-- Actual signed full B-coset embedding in the LEGALLY
loop-completed (possibly nonisolated) augmented proper
cluster stage: first use the true coset signed subgraph
inclusion, then the true stationary-loop completion hom. -/
noncomputable def fullBCosetToAugmentedStageHom
    (gen : ι → Γ) (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph gen B v).toEGraph).toLabelledGraph
      (P.augmentedTrivialStage (gen := gen) B hBA v).toEGraph.toLabelledGraph :=
  (((P.augmentedCayleySubgraph gen B hBA v).toEGraph).trivialLoopCompletionHom
    (P.augmentedCayleySubgraph_locallyPairedLabels (gen := gen) B hBA v)).comp
      (P.fullBCosetToAugmentedSkeletonHom gen B hBA v)

/-- No two different genuine full B-coset vertices collapse
in the legally completed augmented proper cluster, even when
the original cluster has many old B-edges at that core. -/
theorem fullBCosetToAugmentedStageHom_vertex_injective
    (gen : ι → Γ) (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    Function.Injective
      (P.fullBCosetToAugmentedStageHom gen B hBA v).onVertex := by
  intro x y h
  apply Subtype.ext
  have hv := congrArg
    (fun z : (P.augmentedCayleySubgraph gen B hBA v).Vertex => z.1) h
  change x.1 = y.1 at hv
  exact hv

end ClusterSpec
end ABO
end PSTSEPPA
