import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainOldAnchorCover
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainStageIso
import PSTSEPPA.ABO.SourceLabelEdgeQuotientEGraph
import PSTSEPPA.ABO.RootedMultiCosetRawGraphNaturality
import PSTSEPPA.ABO.SingleCosetSkeletonEmbedding

/-!
# Literal OLD H-component inclusion into its genuinely tagged completed P_A stage

The old input H A-component and the ordinary proper-coset completion
live in different E-graphs. In particular, the original H skeleton
is INCOMPLETE; we cannot identify it with the completed stage by
ambient group coordinates.

There is nevertheless a canonical LABELLED SIGNED morphism:
  original rooted old H A-component
    -> disjoint P-indexed single-coset RAW graph
    -> exact glued vertex / source-and-full-SIGNED-label edge quotient
    -> legally stationary-loop-completed P_A stage.

The first map uses the genuine skeleton-to-single-B extension for
a specified B in P. It works for ANY vertex gluing setoid and needs
neither global retractability nor ambient quotient injectivity.
The second is the universal raw-edge quotient projection; it
preserves both signs and formal inversion because target congruence
was independently certified. Finally legal completion adds no
nonstationary edges.

For the original printed T(Y₁) rank-two root, B=empty is a valid
proper alphabet. The resulting map sends the TRUE original old
root to its EXACT quotient component-tagged old anchor, and sends
every genuine old signed word path from it to exactly the same
chronological word endpoint in the complete printed H stage.

These facts are essential for comparing the source G[A] local cover
with the actual H OLD inclusion in corrected Theorem 4.7(ii).
We do not identify unrelated component tags or claim any global
H ambient embedding, bridge freeness, or unconditional PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V Edge : Type*}

/-- Universal exact raw signed-edge quotient projection: it is a
labelled graph morphism whenever the verified source+signed-label
relation is target-congruent. No injectivity of this projection is
assumed, because different raw constituent edge tokens may be glued. -/
noncomputable def LabelledGraph.sourceLabelQuotientProjection
    (G : LabelledGraph V Edge ι)
    (hcongr : G.SourceLabelTargetCongruent) :
    LabelledGraphHom G
      (sourceLabelGraphQuotientEGraph G hcongr).toLabelledGraph where
  onVertex := id
  onEdge := fun e => Quotient.mk
    (sourceLabelEdgeSetoid G.source G.label) e
  map_source := by
    intro e
    rfl
  map_inv := by
    intro e
    rfl
  map_label := by
    intro e
    rfl

variable {Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

/-- Genuine ORIGINAL incomplete old skeleton into an arbitrary
tagged P-coset RAW graph, using one chosen B constituent.
Its vertex carries the true intrinsic old B-component tag.
Both old B-edges and old outside-B edges are transported by the
already proved signed single-coset skeleton morphism. -/
noncomputable def skeletonToRawMultiCosetGraphHom
    (K : CayleySubgraphSpec gen S)
    (P : CosetFamilySpec S)
    (s : Setoid (K.MultiCosetRawVertex P))
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    LabelledGraphHom
      (K.toEGraph).toLabelledGraph
      (K.multiCosetRawGraphOfSetoid P s) where
  onVertex := fun x => Quotient.mk s
    (⟨⟨B, hBP⟩, K.attachedOfSkeletonVertex B x⟩ :
      K.MultiCosetRawVertex P)
  onEdge := fun e =>
    (⟨⟨B, hBP⟩, K.singleCosetSkeletonEdgeMap B e⟩ :
      K.MultiCosetRawEdge P)
  map_source := by
    intro e
    change Quotient.mk s
        (⟨⟨B, hBP⟩, (K.singleCosetEGraph B).source
          (K.singleCosetSkeletonEdgeMap B e)⟩ :
          K.MultiCosetRawVertex P) =
      Quotient.mk s
        (⟨⟨B, hBP⟩, K.attachedOfSkeletonVertex B
          ((K.toEGraph).source e)⟩ : K.MultiCosetRawVertex P)
    rw [K.singleCosetSkeletonEdgeMap_source B e]
  map_inv := by
    intro e
    change
      (⟨⟨B, hBP⟩, K.singleCosetSkeletonEdgeMap B
        ((K.toEGraph).inv e)⟩ : K.MultiCosetRawEdge P) =
      (⟨⟨B, hBP⟩, K.singleCosetInv B
        (K.singleCosetSkeletonEdgeMap B e)⟩ : K.MultiCosetRawEdge P)
    exact congrArg
      (fun f : K.SingleCosetEdge B =>
        (⟨⟨B, hBP⟩, f⟩ : K.MultiCosetRawEdge P))
      (K.singleCosetSkeletonEdgeMap_inv B e)
  map_label := by
    intro e
    exact K.singleCosetSkeletonEdgeMap_label B e

/-- Quotienting the genuine raw edge tokens gives a deterministic
completed multi-coset EGraph. The original old skeleton still maps
to it as a labelled graph on ACTUAL edges and component-tagged points,
without assuming global ambient retractability. -/
noncomputable def skeletonToSourceLabelMultiCosetHom
    (K : CayleySubgraphSpec gen S)
    (P : CosetFamilySpec S)
    (s : Setoid (K.MultiCosetRawVertex P))
    (hcongr : (K.multiCosetRawGraphOfSetoid P s).SourceLabelTargetCongruent)
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    LabelledGraphHom
      (K.toEGraph).toLabelledGraph
      (sourceLabelGraphQuotientEGraph
        (K.multiCosetRawGraphOfSetoid P s) hcongr).toLabelledGraph :=
  ((K.multiCosetRawGraphOfSetoid P s).sourceLabelQuotientProjection
    hcongr).comp
      (K.skeletonToRawMultiCosetGraphHom P s B hBP)

end CayleySubgraphSpec

variable {W : Type*}
variable [Fintype W] [DecidableEq W]

/-- An actual OLD rooted component of the PRINTED T(Y₁) original
incomplete skeleton embeds by a signed graph morphism into its
corresponding fully and legally completed rank-two P_A stage.
Every vertex retains its exact B-component tag and the exact
intersection-supported quotient, NOT only its ambient H group value. -/
noncomputable def sourceLiteralY1SelectedRootOldToPlainHom
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      ((sourceLiteralY1DirectRootComponent
        src dst base A root).toEGraph).toLabelledGraph
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).toEGraph.toLabelledGraph := by
  let K := sourceLiteralY1DirectRootComponent src dst base A root
  let P := allProperCosetFamily A
  let s := sourceLiteralY1DirectRootMultiCosetSetoid
    src dst base A hcard root P
  let G := sourceLiteralY1SelectedRootRawGraph
    src dst base A hcard root P
  let hcongr := sourceLiteralY1SelectedRootRawGraph_target_congruent
    src dst base A hcard root P
  have hn : A.Nonempty := Finset.card_pos.mp (by rw [hcard]; decide)
  let hEmpty : (∅ : Finset ι) ∈ P.alphabets :=
    empty_mem_allProperCosetFamily A hn
  let f := K.skeletonToSourceLabelMultiCosetHom P s hcongr ∅ hEmpty
  let H := sourceLiteralY1SelectedRootCompletedEGraph
    src dst base A hcard root P
  exact (H.trivialLoopCompletionHom
    (sourceLiteralY1SelectedRootAllProper_locallyPaired
      src dst base A hcard root)).comp f

/-- Its actual original OLD rooted H vertex maps to EXACTLY the
component-tagged old anchor already used to base the full
local G[A] stage cover. No equality of ambient H coset values is
used to prove this identity. -/
@[simp] theorem sourceLiteralY1SelectedRootOldToPlainHom_oldRoot
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedRootOldToPlainHom
      src dst base A hcard root).onVertex
        (sourceLiteralY1SelectedRootOldPoint
          src dst base A root) =
      sourceLiteralY1SelectedRootPlainOldAnchor
        src dst base A hcard root := by
  rfl

/-- Every TRUE ORIGINAL signed H path starting at the selected
old A-root has exactly the same endpoint as the same word in the
fully completed actual printed P_A stage, namely the image of
the EXACT original component-tagged H endpoint.
This is old-vertex compatibility without H ambient injectivity. -/
theorem sourceLiteralY1SelectedRootOldToPlainHom_rootWord
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (x : (sourceLiteralY1DirectRootComponent
      src dst base A root).Vertex)
    (w : LabelWord ι)
    (hp : ((sourceLiteralY1DirectRootComponent
      src dst base A root).toEGraph).Follows
        (sourceLiteralY1SelectedRootOldPoint
          src dst base A root) w x) :
    (sourceLiteralY1SelectedRootPlainCompleteStage
      src dst base A hcard root).followWord
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root) w =
      (sourceLiteralY1SelectedRootOldToPlainHom
        src dst base A hcard root).onVertex x := by
  let T := sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root
  let F := sourceLiteralY1SelectedRootOldToPlainHom
    src dst base A hcard root
  have hpStage : T.toEGraph.Follows
      (sourceLiteralY1SelectedRootPlainOldAnchor
        src dst base A hcard root) w (F.onVertex x) := by
    have h := hp.map F
    rw [sourceLiteralY1SelectedRootOldToPlainHom_oldRoot
      src dst base A hcard root] at h
    exact h
  exact T.toEGraph.follows_right_unique
    (T.follows_followWord
      (sourceLiteralY1SelectedRootPlainOldAnchor
        src dst base A hcard root) w)
    hpStage

end ABO
end PSTSEPPA
