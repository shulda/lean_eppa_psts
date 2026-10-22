import PSTSEPPA.ABO.AugmentedClusterTrivialStage
import PSTSEPPA.ABO.CayleySubgraphFullCosetPaths
import PSTSEPPA.ABO.AugmentedClusterPathInclusion

/-!
# Exact signed B-word endpoints in a GENUINE augmented proper cluster

The source's corrected upward ABO Theorem 4.7(iii), for a
NONTRIVIAL proper B-cluster, augments the WHOLE existing
B-component by a full B-coset. This is NOT an isolated-root
attachment: the original proper cluster may already have
many genuine positive/inverse B-labelled edges.

Here we work on the already certified literal
`ClusterSpec.AugmentedVertexSet` and `AugmentedEdgeSet`,
whose old cluster and newly completed coset overlap by
their ACTUAL Cayley group values. The completion adds
ONLY stationary signed loops for missing labels. All
original signed oriented edge tokens survive.

The full B-coset in that augmented cluster contains
an actual B-path for EVERY B-supported signed word.
Thus the endpoint of such a word in the genuine
completed stage has EXACT ambient group value
  x * [w]_Γ.
Two words from the SAME full B-coset point with
the SAME real completed-stage endpoint must have the
SAME Γ group value.

Unlike the isolated `IsolatedCosetGluing` model, no
hypothesis that the core has no old B-edges occurs.
The remaining source-level task is gluing the
ENTIRE original component-tagged H CE B-cluster
onto this local canonical augmented-cluster model
and supplying the genuine G-Cayley cover.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace ClusterSpec

variable (P : ClusterSpec A)

/-- Every B-supported signed word has the EXACT canonical
group-coordinate endpoint in the genuinely loop-completed
augmentation of an arbitrary cluster, even when the old
cluster ALREADY has genuine B-edges at the attachment core.
No ambient embedding of the completed graph is used. -/
theorem augmentedTrivialStage_B_followWord_exact
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (x : (P.augmentedCayleySubgraph gen B hBA v).Vertex)
    (hx : x.1 ∈ generatedLeftCoset gen B v)
    (w : LabelWord ι) (hw : LabelWord.Uses B w) :
    ∃ y : (P.augmentedCayleySubgraph gen B hBA v).Vertex,
      (P.augmentedTrivialStage (gen := gen) B hBA v).followWord x w = y ∧
      y.1 = x.1 * PSTS.SignedWord.evalGroup gen w := by
  let K := P.augmentedCayleySubgraph gen B hBA v
  let T := P.augmentedTrivialStage (gen := gen) B hBA v
  obtain ⟨y, hRealPath, hValue⟩ :=
    K.follows_word_in_fullCoset B v
      (fun e he =>
        P.fullCosetEdge_mem_augmented gen B hBA v e he)
      x hx w hw
  have hCompleted : T.toEGraph.Follows x w y := by
    have h := hRealPath.map
      (K.toEGraph.trivialLoopCompletionHom
        (P.augmentedCayleySubgraph_locallyPairedLabels
          (gen := gen) B hBA v))
    change T.toEGraph.Follows x w y at h
    exact h
  have hEndpoint : T.followWord x w = y :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord x w) hCompleted
  exact ⟨y, hEndpoint, hValue⟩

/-- Equality of TRUE completed B-augmentation endpoints
from the same attached full B-coset point implies equality
of the corresponding signed group-word evaluations. This
applies to arbitrary (possibly multi-constituent) canonical
B-clusters; no absence-of-old-B-edges assumption. -/
theorem augmentedTrivialStage_B_sameEndpoint_evalGroup_eq
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (x : (P.augmentedCayleySubgraph gen B hBA v).Vertex)
    (hx : x.1 ∈ generatedLeftCoset gen B v)
    (w₁ w₂ : LabelWord ι)
    (hw₁ : LabelWord.Uses B w₁)
    (hw₂ : LabelWord.Uses B w₂)
    (hSameEndpoint :
      (P.augmentedTrivialStage (gen := gen) B hBA v).followWord x w₁ =
      (P.augmentedTrivialStage (gen := gen) B hBA v).followWord x w₂) :
    PSTS.SignedWord.evalGroup gen w₁ =
      PSTS.SignedWord.evalGroup gen w₂ := by
  obtain ⟨y₁, hEnd₁, hVal₁⟩ :=
    P.augmentedTrivialStage_B_followWord_exact
      (gen := gen) B hBA v x hx w₁ hw₁
  obtain ⟨y₂, hEnd₂, hVal₂⟩ :=
    P.augmentedTrivialStage_B_followWord_exact
      (gen := gen) B hBA v x hx w₂ hw₂
  have hY : y₁ = y₂ :=
    hEnd₁.symm.trans (hSameEndpoint.trans hEnd₂)
  have hMul :
      x.1 * PSTS.SignedWord.evalGroup gen w₁ =
        x.1 * PSTS.SignedWord.evalGroup gen w₂ := by
    calc
      x.1 * PSTS.SignedWord.evalGroup gen w₁ = y₁.1 := hVal₁.symm
      _ = y₂.1 := congrArg Subtype.val hY
      _ = x.1 * PSTS.SignedWord.evalGroup gen w₂ := hVal₂
  exact mul_left_cancel hMul

end ClusterSpec
end ABO
end PSTSEPPA
