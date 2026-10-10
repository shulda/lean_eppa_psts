import PSTSEPPA.ABO.IsolatedCosetCompletion
import PSTSEPPA.ABO.IsolatedCosetOldBCompletedWords

/-!
# Global B-word kernel of an isolated full B-coset augmentation

The rank-one (k=1) repair in corrected ABO Proposition 5.4 requires
the completed ACTION of a genuine type-(2) augmented full coset extension,
not just the original incomplete EGraph or a single new coset.

This lemma proves the precise word-kernel preservation theorem for
the singleton type-(2) attachment.

Let G be any locally paired EGraph, with a root carrying no old B-edge.
Attach the complete ambient coset gG[B] at root via the literal
deterministic EGraph gluing, then add only missing loops. For an actual
signed B-word w with value 1 in the ambient group, if the old
loop-completed EGraph acts trivially by w at EVERY old vertex, so
does the augmented completed EGraph at EVERY glued vertex.

The proof splits into exactly three disjoint geometries:
1. the old attachment root, represented by g in the new full coset;
2. every fresh coset point, represented injectively in that coset;
3. every old off-root vertex, whose complete B-word action is
   transported exactly from the old stage by the checked path/step lemmas.

In particular this is NOT an unsupported global morphism between
the old and new complete actions: that would fail at root.
No reflecting-group assumptions or finite induction are hidden.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Any B-word with trivial ambient group value which acts
trivially on all vertices of the original completed stage also
acts trivially on ALL vertices of the singleton-augmented
completed stage. The original graph is allowed to have missing
labels, loops, and arbitrary other-labelled components. -/
theorem completedStage_B_identity_word_fixes_every_vertex
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels)
    (w : LabelWord ι)
    (hw : LabelWord.Uses B w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1)
    (hOldKernel : ∀ x : V,
      (G.trivialLoopCompletion hpaired).followWord x w = x)
    (v : Vertex V gen B g) :
    (completedStage G gen B g root hMissing hpaired).followWord v w = v := by
  classical
  cases v with
  | inl x =>
      by_cases hx : x = root
      · subst x
        let p : CosetPoint gen B g :=
          ⟨g, self_mem_generatedLeftCoset gen B g⟩
        have hp : gluePoint gen B g root p = Sum.inl root := by
          simp [gluePoint, p]
        simpa only [hp] using
          (completedStage_attached_B_identity_word_fixes
            G gen B g root hMissing hpaired p w hw hval)
      · have htransport :=
          (glued_B_completed_followWord_old_ne_root
            G gen B g root hMissing hpaired
            (glued_locallyPairedLabels
              G gen B g root hMissing hpaired)
            x hx w hw).1
        calc
          (completedStage G gen B g root hMissing hpaired).followWord
              (Sum.inl x) w =
              Sum.inl ((G.trivialLoopCompletion hpaired).followWord x w) :=
            htransport
          _ = Sum.inl x := by rw [hOldKernel x]
  | inr q =>
      let p : CosetPoint gen B g := ⟨q.1, q.2.1⟩
      have hp : gluePoint gen B g root p = Sum.inr q := by
        simp [gluePoint, p, q.2.2]
      simpa only [hp] using
        (completedStage_attached_B_identity_word_fixes
          G gen B g root hMissing hpaired p w hw hval)

end IsolatedCosetGluing
end ABO
end PSTSEPPA
