import PSTSEPPA.ABO.IsolatedCosetGluing
import PSTSEPPA.ABO.TrivialCompletionPaths
import PSTSEPPA.ABO.CayleySubgraphFullCosetPaths

/-!
# Trivial completion of an isolated full-coset augmentation

The missing rank-two Definition-5.3 type-(2) objects are
augmentations of actual full multi-coset extensions.
For the off-component singleton case, the preceding file
gives a real EGraph constructed by gluing a complete
B-coset at a root with no original signed B-edges.

If the old EGraph has locally paired outgoing signs,
the glued EGraph retains that property. Old edges are
paired in the old graph, and each new complete coset
edge has an opposite-signed companion at the same
source inside the newly attached coset. Hence the
genuine glued object admits the canonical loop-only
completion on the SAME vertices.

For any B-word whose ambient group evaluation is 1,
the completed action fixes EVERY vertex of the newly
attached full B-coset, including its identified root.
This is the new geometric word-kernel case needed for
the corrected ABO Proposition 5.4 R2.

The behaviour on all OLD non-attached vertices, source-
specific rank-two instantiation, and the full finite
stage tower remain separate.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

open ClusterSpec

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Same-source inverse-label pairing is sufficient for
the local paired-sign condition. Formal edge reversal
alone would NOT be sufficient (its source is the target). -/
theorem paired_of_sameSourceOpposite
    {W F : Type*}
    (H : EGraph W F ι)
    (hOpp : ∀ e : F, ∃ f : F,
      H.source f = H.source e ∧
      H.label f = PSTS.SignedLetter.inv (H.label e)) :
    H.LocallyPairedLabels := by
  intro u i
  constructor
  · rintro ⟨e, hsrc, hlab⟩
    obtain ⟨f, hfs, hfl⟩ := hOpp e
    refine ⟨f, hfs.trans hsrc, ?_⟩
    rw [hfl, hlab]
    rfl
  · rintro ⟨e, hsrc, hlab⟩
    obtain ⟨f, hfs, hfl⟩ := hOpp e
    refine ⟨f, hfs.trans hsrc, ?_⟩
    rw [hfl, hlab]
    rfl

/-- The actual singleton-augmented EGraph is locally
paired when its original skeleton is locally paired.
For old edges the witness stays old; for new edges
the opposite-signed witness stays in the full B-coset. -/
theorem glued_locallyPairedLabels
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels) :
    (gluedEGraph G gen B g root hMissing).LocallyPairedLabels := by
  let H := gluedEGraph G gen B g root hMissing
  apply paired_of_sameSourceOpposite H
  intro e
  cases e with
  | inl e =>
      cases hs : G.label e with
      | pos i =>
          obtain ⟨f, hsrc, hlab⟩ :=
            (hpaired (G.source e) i).mp ⟨e, rfl, hs⟩
          refine ⟨Sum.inl f, ?_, ?_⟩
          · exact congrArg Sum.inl hsrc
          · change G.label f =
              PSTS.SignedLetter.inv (G.label e)
            rw [hlab, hs]
            rfl
      | neg i =>
          obtain ⟨f, hsrc, hlab⟩ :=
            (hpaired (G.source e) i).mpr ⟨e, rfl, hs⟩
          refine ⟨Sum.inl f, ?_, ?_⟩
          · exact congrArg Sum.inl hsrc
          · change G.label f =
              PSTS.SignedLetter.inv (G.label e)
            rw [hlab, hs]
            rfl
  | inr e =>
      let f : CosetEdge gen B g :=
        ⟨(e.1.1, PSTS.SignedLetter.inv e.1.2), by
          refine ⟨e.2.1, ?_⟩
          simpa only [signedBase_inv] using e.2.2⟩
      refine ⟨Sum.inr f, ?_, ?_⟩
      · rfl
      · rfl

/-- Complete the genuine glued graph on exactly its old
vertices plus new coset vertices. Only missing labels
receive trivial loops. -/
noncomputable def completedStage
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels) :
    CompleteEGraph
      (Vertex V gen B g)
      (ActionEdge (Vertex V gen B g) ι) ι :=
  (gluedEGraph G gen B g root hMissing).trivialLoopCompletion
    (glued_locallyPairedLabels G gen B g root hMissing hpaired)

/-- A singleton-supported identity-valued word, for the
attached alphabet B, fixes each point of the NEW completed
full B-coset. The proof follows the actual old B-coset
edges, maps the path through the certified gluing morphism,
then through the loop-only completion, and uses determinism.
No ambient projection injectivity is assumed for the old graph. -/
theorem completedStage_attached_B_identity_word_fixes
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels)
    (p : CosetPoint gen B g)
    (w : LabelWord ι)
    (hw : LabelWord.Uses B w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (completedStage G gen B g root hMissing hpaired).followWord
        (gluePoint gen B g root p) w =
      gluePoint gen B g root p := by
  let K := fullCosetSubgraph gen B g
  let H := gluedEGraph G gen B g root hMissing
  let paired : H.LocallyPairedLabels :=
    glued_locallyPairedLabels G gen B g root hMissing hpaired
  let T := completedStage G gen B g root hMissing hpaired
  obtain ⟨q, hpath, hvalue⟩ :=
    K.follows_word_in_fullCoset B g
      (by intro e he; exact he) p p.2 w hw
  have hqp : q = p := by
    apply Subtype.ext
    simpa [hval] using hvalue
  have hOld :
      H.Follows (gluePoint gen B g root p) w
        (gluePoint gen B g root p) := by
    have h := hpath.map (cosetHom G gen B g root hMissing)
    change H.Follows (gluePoint gen B g root p) w
      (gluePoint gen B g root q) at h
    rw [hqp] at h
    exact h
  have hCompleted :
      T.toEGraph.Follows (gluePoint gen B g root p) w
        (gluePoint gen B g root p) :=
    hOld.map (H.trivialLoopCompletionHom paired)
  exact T.toEGraph.follows_right_unique
    (T.follows_followWord (gluePoint gen B g root p) w)
    hCompleted

end IsolatedCosetGluing
end ABO
end PSTSEPPA
