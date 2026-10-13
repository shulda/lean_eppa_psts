import PSTSEPPA.ABO.AugmentedClusterLocalSubgroupEquiv
import PSTSEPPA.ABO.LocalCosetCayleySlice
import PSTSEPPA.ABO.AugmentedClusterTrivialStage
import PSTSEPPA.ABO.TrivialLoopCompletionIsomorphism

/-!
# Exact signed complete original/local type-(1) augmented-cluster action isomorphism

A proper-subalphabet cluster with B⊆A augmentation lies entirely in
the true generated subgroup Γ[A]. The checked vertex/edge equivalences
and the signed local Cayley inverse-translation law allow us to upgrade
those data maps to a genuine vertex- and signed-edge-bijective graph
morphism between the local Γ[A] augmented cluster and the original
ambient Γ augmented cluster.

The source's LEGAL completion only adds the missing stationary signed
loops; naturality of that completion gives an actual COMPLETE ACTION
isomorphism. It preserves every positive and negative labelled word
path, including old/fresh B-coset edges and inverse tokens at loops.

This supplies the geometric source/local normalization mechanism
needed to match original rank-one Z₁ type-(1) clusters with finite
G₂'s all-local type-(1) action catalogue. Exact input-dependent Z₁
indexing is a separate subsequent Lean step.
-/

namespace PSTSEPPA
namespace ABO

namespace ClusterSpec

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {A : Finset ι}

/-- Honest signed graph homomorphism from the actual locally
generated Γ[A] augmented cluster into the original ambient Γ
augmented cluster, retaining every original signed edge token. -/
noncomputable def localAugmentedSignedGraphHom
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : generatedSubgroup gen A) :
    LabelledGraphHom
      ((P.augmentedCayleySubgraph
        (trivialCompletionGenerator gen A) B hBA v).toEGraph).toLabelledGraph
      ((P.augmentedCayleySubgraph
        gen B hBA (v : Γ)).toEGraph).toLabelledGraph where
  onVertex := P.localAugmentedVertexEquiv gen B hBA v
  onEdge := P.localAugmentedEdgeEquiv gen B hBA v
  map_source e := by
    apply Subtype.ext
    rfl
  map_label e := by
    rfl
  map_inv e := by
    apply Subtype.ext
    have hs : signedBase e.1.2 ∈ A := by
      rcases e.2 with heOld | heNew
      · rcases heOld with ⟨C, hCP, _, hlabel⟩
        exact (P.proper C hCP).subset hlabel
      · exact hBA heNew.2
    change
      (((((cayleyGraph (trivialCompletionGenerator gen A)).inv e.1).1 : Γ),
        ((cayleyGraph (trivialCompletionGenerator gen A)).inv e.1).2) :
          ActionEdge Γ ι) =
        (cayleyGraph gen).inv ((e.1.1 : Γ), e.1.2)
    simpa only [one_mul] using
      (localCayley_inv_leftTranslate gen A (1 : Γ) e.1 hs)

/-- The labelled graph homomorphism is bijective ON ALL VERTICES
AND DIRECTED SIGNED EDGE TOKENS, not just their ambient values. -/
theorem localAugmentedSignedGraphHom_bijective
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : generatedSubgroup gen A) :
    Function.Bijective
      (P.localAugmentedSignedGraphHom gen B hBA v).onVertex ∧
    Function.Bijective
      (P.localAugmentedSignedGraphHom gen B hBA v).onEdge := by
  exact ⟨(P.localAugmentedVertexEquiv gen B hBA v).bijective,
    (P.localAugmentedEdgeEquiv gen B hBA v).bijective⟩

/-- LEGAL loop-only completion of the actual original and local
type-(1) augmented-cluster graphs preserves the full signed
vertex/edge bijection and produces a complete action morphism. -/
noncomputable def localAugmentedCompletedStageHom
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : generatedSubgroup gen A) :
    LabelledGraphHom
      (P.augmentedTrivialStage
        (gen := trivialCompletionGenerator gen A) B hBA v).toEGraph.toLabelledGraph
      (P.augmentedTrivialStage
        (gen := gen) B hBA (v : Γ)).toEGraph.toLabelledGraph :=
  EGraph.trivialLoopCompletionIsoHom
    (P.augmentedCayleySubgraph
      (trivialCompletionGenerator gen A) B hBA v).toEGraph
    (P.augmentedCayleySubgraph
      gen B hBA (v : Γ)).toEGraph
    (P.localAugmentedSignedGraphHom gen B hBA v)
    (P.localAugmentedSignedGraphHom_bijective gen B hBA v).1
    (P.localAugmentedSignedGraphHom_bijective gen B hBA v).2
    (P.augmentedCayleySubgraph_locallyPairedLabels
      (gen := trivialCompletionGenerator gen A) B hBA v)
    (P.augmentedCayleySubgraph_locallyPairedLabels
      (gen := gen) B hBA (v : Γ))

/-- The source/local COMPLETE type-(1) stage map is bijective
on vertices and signed action-edge tokens, including every
newly inserted trivial loop. -/
theorem localAugmentedCompletedStageHom_bijective
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : generatedSubgroup gen A) :
    Function.Bijective
      (P.localAugmentedCompletedStageHom gen B hBA v).onVertex ∧
    Function.Bijective
      (P.localAugmentedCompletedStageHom gen B hBA v).onEdge := by
  exact EGraph.trivialLoopCompletionIsoHom_bijective
    (P.augmentedCayleySubgraph
      (trivialCompletionGenerator gen A) B hBA v).toEGraph
    (P.augmentedCayleySubgraph
      gen B hBA (v : Γ)).toEGraph
    (P.localAugmentedSignedGraphHom gen B hBA v)
    (P.localAugmentedSignedGraphHom_bijective gen B hBA v).1
    (P.localAugmentedSignedGraphHom_bijective gen B hBA v).2
    (P.augmentedCayleySubgraph_locallyPairedLabels
      (gen := trivialCompletionGenerator gen A) B hBA v)
    (P.augmentedCayleySubgraph_locallyPairedLabels
      (gen := gen) B hBA (v : Γ))

/-- Every chronological signed word has precisely matching
endpoints in the local Γ[A] and ORIGINAL ambient Γ completed
type-(1) augmented-cluster actions. -/
theorem localAugmentedCompletedStageHom_followWord
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A)
    (v : generatedSubgroup gen A)
    (x : (P.augmentedCayleySubgraph
      (trivialCompletionGenerator gen A) B hBA v).Vertex)
    (w : LabelWord ι) :
    (P.augmentedTrivialStage (gen := gen) B hBA (v : Γ)).followWord
      ((P.localAugmentedCompletedStageHom gen B hBA v).onVertex x) w =
    (P.localAugmentedCompletedStageHom gen B hBA v).onVertex
      ((P.augmentedTrivialStage
        (gen := trivialCompletionGenerator gen A) B hBA v).followWord x w) := by
  exact (P.augmentedTrivialStage
    (gen := trivialCompletionGenerator gen A) B hBA v).hom_followWord
    (P.augmentedTrivialStage
      (gen := gen) B hBA (v : Γ))
    (P.localAugmentedCompletedStageHom gen B hBA v) x w

end ClusterSpec
end ABO
end PSTSEPPA
