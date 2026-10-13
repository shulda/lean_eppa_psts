import PSTSEPPA.ABO.RootedFullBAugmentationGraphIso
import PSTSEPPA.ABO.IsolatedCosetCompletion
import PSTSEPPA.ABO.TrivialLoopCompletionIsomorphism

/-!
# COMPLETE original-source B-augmented ACTION isomorphism under root translation

For corrected ABO Definition-5.3 type-(2) augmentation, an old signed
EGraph has no outgoing B-edges at the selected old root. Attach a
genuine full B-coset there and identify ONLY its basepoint with this
old root; preserve all other old tags and new fresh coset points.

The previous generic signed augmented EGraph isomorphism maps BOTH
old directed signed edges and genuinely new full B-coset edges, and
preserves the precise gluing root. The corrected ABO construction
then completes missing signed labels ONLY by stationary loops.
Provided the two old EGraphs are locally paired, their actual full
B-augmentations are locally paired by the verified generic gluing
lemma. The already certified completion-naturality theorem makes
the FULLY COMPLETED augmented actions genuinely isomorphic.

The output is an honest labelled-graph map of complete actions,
bijective on all vertices and oriented signed action-edge tokens,
preserving and reflecting every realised signed word path.
This is an abstract transport lemma; applying it to the actual H1
source-rooted rank-two stage and its Γ[A] local catalogue requires
identifying the exact old coset-quotient model and translated
augmentation basepoint (available in the main source geometry).
-/

namespace PSTSEPPA
namespace ABO

variable {V W E F ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Every actual signed loop-completed B-augmentation of
the old locally-paired G and H is isomorphic after rooted
translation, including old/root/fresh points and all inverse
signed action edges. No global Γ retractability is required. -/
noncomputable def rootedFullBAugmentationCompletedStageHom
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) (root : V)
    (hMissingG : ∀ e : E,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : F,
      H.source e = f.onVertex root → signedBase (H.label e) ∉ B)
    (hpairedG : G.LocallyPairedLabels)
    (hpairedH : H.LocallyPairedLabels) :
    LabelledGraphHom
      (IsolatedCosetGluing.completedStage
        G (trivialCompletionGenerator gen A) B g root
        hMissingG hpairedG).toEGraph.toLabelledGraph
      (IsolatedCosetGluing.completedStage
        H gen B (r * (g : Γ)) (f.onVertex root)
        hMissingH hpairedH).toEGraph.toLabelledGraph :=
  (IsolatedCosetGluing.gluedEGraph G
    (trivialCompletionGenerator gen A) B g root hMissingG).
    trivialLoopCompletionIsoHom
      (IsolatedCosetGluing.gluedEGraph H gen B
        (r * (g : Γ)) (f.onVertex root) hMissingH)
      (rootedFullBAugmentationGraphHom G H f hv he
        gen A B hBA r g root hMissingG hMissingH)
      (rootedFullBAugmentationGraphHom_bijective G H f hv he
        gen A B hBA r g root hMissingG hMissingH).1
      (rootedFullBAugmentationGraphHom_bijective G H f hv he
        gen A B hBA r g root hMissingG hMissingH).2
      (IsolatedCosetGluing.glued_locallyPairedLabels G
        (trivialCompletionGenerator gen A) B g root
        hMissingG hpairedG)
      (IsolatedCosetGluing.glued_locallyPairedLabels H
        gen B (r * (g : Γ)) (f.onVertex root)
        hMissingH hpairedH)

/-- The genuine COMPLETED augmented actions have a full
bijection of vertices and signed directed action-edge TOKENS.
Newly added fixed-point loops are not confused with genuine
old or new-B edges, and inversion is preserved. -/
theorem rootedFullBAugmentationCompletedStageHom_bijective
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) (root : V)
    (hMissingG : ∀ e : E,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : F,
      H.source e = f.onVertex root → signedBase (H.label e) ∉ B)
    (hpairedG : G.LocallyPairedLabels)
    (hpairedH : H.LocallyPairedLabels) :
    Function.Bijective
      (rootedFullBAugmentationCompletedStageHom G H f hv he gen
        A B hBA r g root hMissingG hMissingH hpairedG hpairedH).onVertex ∧
    Function.Bijective
      (rootedFullBAugmentationCompletedStageHom G H f hv he gen
        A B hBA r g root hMissingG hMissingH hpairedG hpairedH).onEdge := by
  exact
    (IsolatedCosetGluing.gluedEGraph G
      (trivialCompletionGenerator gen A) B g root hMissingG).
      trivialLoopCompletionIsoHom_bijective
        (IsolatedCosetGluing.gluedEGraph H gen B
          (r * (g : Γ)) (f.onVertex root) hMissingH)
        (rootedFullBAugmentationGraphHom G H f hv he
          gen A B hBA r g root hMissingG hMissingH)
        (rootedFullBAugmentationGraphHom_bijective G H f hv he
          gen A B hBA r g root hMissingG hMissingH).1
        (rootedFullBAugmentationGraphHom_bijective G H f hv he
          gen A B hBA r g root hMissingG hMissingH).2
        (IsolatedCosetGluing.glued_locallyPairedLabels G
          (trivialCompletionGenerator gen A) B g root
          hMissingG hpairedG)
        (IsolatedCosetGluing.glued_locallyPairedLabels H
          gen B (r * (g : Γ)) (f.onVertex root)
          hMissingH hpairedH)

/-- Every genuinely realised signed path in the entire
stationary-loop-completed type-(2) B-augmentation is reflected
AND preserved by the exact source/local map, including traversals
of newly attached B-cosets and fixed-point loops. -/
theorem rootedFullBAugmentationCompletedStageHom_follows_iff
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) (root : V)
    (hMissingG : ∀ e : E,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : F,
      H.source e = f.onVertex root → signedBase (H.label e) ∉ B)
    (hpairedG : G.LocallyPairedLabels)
    (hpairedH : H.LocallyPairedLabels)
    (u v : IsolatedCosetGluing.Vertex
      V (trivialCompletionGenerator gen A) B g)
    (w : LabelWord ι) :
    (IsolatedCosetGluing.completedStage
      G (trivialCompletionGenerator gen A) B g root
      hMissingG hpairedG).toEGraph.Follows u w v ↔
    (IsolatedCosetGluing.completedStage
      H gen B (r * (g : Γ)) (f.onVertex root)
      hMissingH hpairedH).toEGraph.Follows
        ((rootedFullBAugmentationCompletedStageHom G H f hv he
          gen A B hBA r g root hMissingG hMissingH
          hpairedG hpairedH).onVertex u)
        w
        ((rootedFullBAugmentationCompletedStageHom G H f hv he
          gen A B hBA r g root hMissingG hMissingH
          hpairedG hpairedH).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (rootedFullBAugmentationCompletedStageHom G H f hv he gen
      A B hBA r g root hMissingG hMissingH hpairedG hpairedH)
    (rootedFullBAugmentationCompletedStageHom_bijective G H f hv he gen
      A B hBA r g root hMissingG hMissingH hpairedG hpairedH).1
    (rootedFullBAugmentationCompletedStageHom_bijective G H f hv he gen
      A B hBA r g root hMissingG hMissingH hpairedG hpairedH).2
    u v w

end ABO
end PSTSEPPA
