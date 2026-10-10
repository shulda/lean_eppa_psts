import PSTSEPPA.ABO.TrivialCompletionPaths
import PSTSEPPA.ABO.ClusterCayleySkeleton
import PSTSEPPA.ABO.AugmentedCluster

/-!
# Actual trivial-completion stages for clusters and AUGMENTED clusters

Corrected ABO Section 5 / Definition 5.3 constructs the finite
family Z_k not only from full coset extensions but also from
augmented clusters. The earlier completion modules certify that an
incomplete EGraph may be completed by adding *only loops* when
its available positive and negative signs are paired at every vertex.

Unlike an arbitrary incomplete EGraph, the literal ABO cluster
and its augmentation are unions of COMPLETE constituent coset
graphs. Consequently, whenever an old positive or negative
signed edge exists, the opposite signed label also has an edge
at the SAME SOURCE, in that same constituent. The formal edge
reversal at the edge TARGET is not what proves this fact.

We formalize this separately for genuine ClusterSpec.EdgeSet and
AugmentedEdgeSet, then construct actual complete EGraphs on
the SAME augmented vertex sets. Every old edge maps injectively
into the completion, and every newly added edge is a loop.

Moreover all genuine C-path relations between old vertices
of either a cluster or an augmented cluster are preserved AND
reflected for every subalphabet C.

This is a direct piece of the **type (1) Z_k stage** of ABO
Definition 5.3, including the source's k=1 repair R2.
It does NOT classify all augmented singleton components, build
the finite disjoint union Z_1, or prove stability of G_2 -> H_1.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Sufficient geometric condition for a literal oriented
Cayley subgraph to have paired outgoing +i and -i at every
vertex: a signed edge may be reversed in LABEL while keeping
its ORIGINAL SOURCE and remaining in the literal edge set. -/
theorem locallyPairedLabels_of_sameSourceOpposite
    (hopp : ∀ (e : ActionEdge Γ ι), e ∈ K.edges →
      (e.1, PSTS.SignedLetter.inv e.2) ∈ K.edges) :
    K.toEGraph.LocallyPairedLabels := by
  intro u i
  constructor
  · rintro ⟨e, hSource, hLabel⟩
    let f : K.Edge :=
      ⟨(e.1.1, PSTS.SignedLetter.inv e.1.2),
        hopp e.1 e.2⟩
    refine ⟨f, ?_, ?_⟩
    · exact hSource
    · change PSTS.SignedLetter.inv e.1.2 =
        PSTS.SignedLetter.neg i
      have h : e.1.2 = PSTS.SignedLetter.pos i := hLabel
      rw [h]
      rfl
  · rintro ⟨e, hSource, hLabel⟩
    let f : K.Edge :=
      ⟨(e.1.1, PSTS.SignedLetter.inv e.1.2),
        hopp e.1 e.2⟩
    refine ⟨f, ?_, ?_⟩
    · exact hSource
    · change PSTS.SignedLetter.inv e.1.2 =
        PSTS.SignedLetter.pos i
      have h : e.1.2 = PSTS.SignedLetter.neg i := hLabel
      rw [h]
      rfl

end CayleySubgraphSpec

namespace ClusterSpec

variable {A : Finset ι}
variable (P : ClusterSpec A)

/-- Each old cluster edge has an opposite-SIGNED-label
companion edge at the SAME SOURCE, inside its constituent
full coset. No global ambient Cayley injection is assumed. -/
theorem clusterEdgeSet_sameSourceOpposite
    (e : ActionEdge Γ ι)
    (he : e ∈ P.EdgeSet gen) :
    (e.1, PSTS.SignedLetter.inv e.2) ∈ P.EdgeSet gen := by
  obtain ⟨C, hCP, hSource, hLabel⟩ := he
  refine ⟨C, hCP, hSource, ?_⟩
  change signedBase (PSTS.SignedLetter.inv e.2) ∈ C
  change signedBase e.2 ∈ C at hLabel
  simpa only [signedBase_inv] using hLabel

/-- The same property survives augmentation by an entire full
B-coset, whether or not it meets the original cluster.
The added coset's own full B-edges provide each companion. -/
theorem augmentedEdgeSet_sameSourceOpposite
    (B : Finset ι) (v : Γ)
    (e : ActionEdge Γ ι)
    (he : e ∈ P.AugmentedEdgeSet gen B v) :
    (e.1, PSTS.SignedLetter.inv e.2) ∈
      P.AugmentedEdgeSet gen B v := by
  rcases he with hOld | hNew
  · exact Or.inl (P.clusterEdgeSet_sameSourceOpposite e hOld)
  · refine Or.inr ⟨hNew.1, ?_⟩
    change signedBase (PSTS.SignedLetter.inv e.2) ∈ B
    have hb : signedBase e.2 ∈ B := hNew.2
    simpa only [signedBase_inv] using hb

/-- The literal cluster, represented as the already-checked
incomplete Cayley skeleton, satisfies paired signed labels. -/
theorem clusterCayleySubgraph_locallyPairedLabels :
    (P.toCayleySubgraph gen).toEGraph.LocallyPairedLabels := by
  apply (P.toCayleySubgraph gen).locallyPairedLabels_of_sameSourceOpposite
  intro e he
  exact P.clusterEdgeSet_sameSourceOpposite e he

/-- More importantly, the literal AUGMENTED cluster skeleton
inherits paired signed labels even across the attachment.
This justifies completion by adding loops only. -/
theorem augmentedCayleySubgraph_locallyPairedLabels
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    (P.augmentedCayleySubgraph gen B hBA v).toEGraph.LocallyPairedLabels := by
  apply (P.augmentedCayleySubgraph gen B hBA v).locallyPairedLabels_of_sameSourceOpposite
  intro e he
  exact P.augmentedEdgeSet_sameSourceOpposite B v e he

/-- A concrete, genuinely COMPLETE action EGraph on the same
vertices of the original augmented cluster. Every missing
signed edge becomes a geometric loop, never a connecting edge. -/
noncomputable def augmentedTrivialStage
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ) :
    CompleteEGraph
      (P.augmentedCayleySubgraph gen B hBA v).Vertex
      (ActionEdge
        (P.augmentedCayleySubgraph gen B hBA v).Vertex ι) ι :=
  ((P.augmentedCayleySubgraph gen B hBA v).toEGraph).trivialLoopCompletion
    (P.augmentedCayleySubgraph_locallyPairedLabels B hBA v)

/-- Completing the augmented cluster by missing loops does not
create ANY new genuine C-labelled connections for ANY C.
In particular its singleton-component geometry, once the
source's component classification is applied, remains exact. -/
theorem augmentedTrivialStage_C_reachable_iff
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (C : Finset ι)
    (x y : (P.augmentedCayleySubgraph gen B hBA v).Vertex) :
    (∃ w : LabelWord ι, LabelWord.Uses C w ∧
      (P.augmentedTrivialStage B hBA v).toEGraph.Follows x w y) ↔
    (P.augmentedCayleySubgraph gen B hBA v).SubalphabetReachable C x y := by
  exact ((P.augmentedCayleySubgraph gen B hBA v).toEGraph).trivialLoopCompletion_B_reachable_iff
    (P.augmentedCayleySubgraph_locallyPairedLabels B hBA v)
    C x y

end ClusterSpec
end ABO
end PSTSEPPA
