import PSTSEPPA.ABO.IsolatedCosetCompletion
import PSTSEPPA.ABO.IsolatedCosetOldBPaths
import PSTSEPPA.ABO.Stability
import PSTSEPPA.ABO.KStableTranslatedCosetEquiv
import PSTSEPPA.ABO.Morphisms

/-!
# Augmented full B-coset detects nontrivial B-orbits over old vertices

The corrected ABO Theorem 4.7(iii) includes the TRUE type-(2)
augmentation of the genuine incomplete old multiCE: at a
selected OLD off-B vertex z having NO old signed B-edges,
attach a NEW full B-coset, identifying ONLY its basepoint
with z and keeping all other coset vertices freshly tagged.

The previous verified word-kernel theorem showed merely that
B-words of ambient group value one fix points of the attached
full coset. We prove the SIGNED CONVERSE: for ANY B-word,
the completed action at a newly attached coset point has
exactly the projected right group-word value. Thus a
B-word returns that point iff its genuine H[B] group value
is the identity.

In particular, starting from the attached OLD root,
a signed B-word ending at ANY OLD point of the augmented
completed stage must in fact end at exactly the root,
and its H group word value must be 1. This is not an
argument from fictitious original B-edges or from an
ambient-coordinate quotient.

Now let Q:G->H be an ACTUAL generator-preserving quotient
stable on B. Take ANY genuine based labelled signed
Cayley(G)->completed-augmented-H-stage morphism.
If two G-points lie in one G[B]-coset, the FIRST maps
to the augmentation OLD root, and the SECOND maps to
SOME OLD vertex (not an arbitrary fresh coset point),
then the group points themselves are EQUAL. The proof
uses an actual B-supported Cayley path, its exact
signed image, root return detection, and Q-stability.

This is a substantive generic geometric detector for
the remaining genuine first-rank off-B-orbit isolation
obligation. To use it on the entire selected original
G[A] old+fresh region, a further SOURCE-SPECIFIC
compatibility theorem must establish that the actual
chosen type-(2) Cayley cover sends EVERY relevant
original G multiCE vertex to an OLD vertex in that
particular augmentation, based correctly at the off-B
point. This last compatibility is NOT silently assumed
or concluded here. R8, general 4.7(iii), higher stages,
Condition 5.2, and PSTS EPPA remain separate.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Exact signed B-word action on EVERY point of the actual
newly attached full B-coset, after legal fixed-loop completion.
The endpoint's true B-coset coordinate is p*eval(w), and its
old/fresh tag is precisely the gluePoint tag of that coordinate.

No additional artificial edge or ambient embedding is needed. -/
theorem completedStage_attached_B_followWord_exact
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels)
    (p : CosetPoint gen B g)
    (w : LabelWord ι) (hw : LabelWord.Uses B w) :
    ∃ q : CosetPoint gen B g,
      (completedStage G gen B g root hMissing hpaired).followWord
        (gluePoint gen B g root p) w =
          gluePoint gen B g root q ∧
      q.1 = p.1 * PSTS.SignedWord.evalGroup gen w := by
  let K := fullCosetSubgraph gen B g
  let H := gluedEGraph G gen B g root hMissing
  let paired : H.LocallyPairedLabels :=
    glued_locallyPairedLabels G gen B g root hMissing hpaired
  let T := completedStage G gen B g root hMissing hpaired
  obtain ⟨q, hPath, hValue⟩ :=
    K.follows_word_in_fullCoset B g
      (by intro e he; exact he) p p.2 w hw
  have hGlued : H.Follows
      (gluePoint gen B g root p) w
      (gluePoint gen B g root q) := by
    exact hPath.map (cosetHom G gen B g root hMissing)
  have hCompleted : T.toEGraph.Follows
      (gluePoint gen B g root p) w
      (gluePoint gen B g root q) :=
    hGlued.map (H.trivialLoopCompletionHom paired)
  refine ⟨q, ?_, hValue⟩
  exact T.toEGraph.follows_right_unique
    (T.follows_followWord (gluePoint gen B g root p) w)
    hCompleted

/-- For a TRUE attached full B-coset, every signed B-word
return to a specified coset point is EQUIVALENT to the
underlying group word being the identity.

The forward direction is the important new converse to
the previously verified rank-two type-(2) word-kernel lemma. -/
theorem completedStage_attached_B_return_iff_kernel
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels)
    (p : CosetPoint gen B g)
    (w : LabelWord ι) (hw : LabelWord.Uses B w) :
    (completedStage G gen B g root hMissing hpaired).followWord
        (gluePoint gen B g root p) w =
      gluePoint gen B g root p ↔
        PSTS.SignedWord.evalGroup gen w = 1 := by
  constructor
  · intro hReturn
    obtain ⟨q, hFollow, hVal⟩ :=
      completedStage_attached_B_followWord_exact
        G gen B g root hMissing hpaired p w hw
    have hGlueEq :
        gluePoint gen B g root q = gluePoint gen B g root p :=
      hFollow.symm.trans hReturn
    have hq : q = p :=
      (gluePoint_injective gen B g root) hGlueEq
    have hMul :
        p.1 * PSTS.SignedWord.evalGroup gen w = p.1 * (1 : Γ) := by
      calc
        p.1 * PSTS.SignedWord.evalGroup gen w = q.1 := hVal.symm
        _ = p.1 := congrArg Subtype.val hq
        _ = p.1 * (1 : Γ) := by simp
    exact mul_left_cancel hMul
  · intro hVal
    exact completedStage_attached_B_identity_word_fixes
      G gen B g root hMissing hpaired p w hw hVal

/-- The old attachment root is the ONLY OLD endpoint of
any completed B-path from that OLD root; reaching any
old vertex forces a genuinely trivial H[B] group word.

The extra attached coset is the source of this detector.
A plain completion with stationary loops would not give
the same group-word conclusion. -/
theorem completedStage_root_B_old_endpoint_implies_kernel
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels)
    (w : LabelWord ι) (hw : LabelWord.Uses B w)
    (v : V)
    (hEnd :
      (completedStage G gen B g root hMissing hpaired).followWord
        (Sum.inl root) w = Sum.inl v) :
    v = root ∧ PSTS.SignedWord.evalGroup gen w = 1 := by
  classical
  let p₀ : CosetPoint gen B g :=
    ⟨g, self_mem_generatedLeftCoset gen B g⟩
  have hp₀ :
      gluePoint gen B g root p₀ = Sum.inl root := by
    simp [p₀, gluePoint]
  obtain ⟨q, hFollow, _hVal⟩ :=
    completedStage_attached_B_followWord_exact
      G gen B g root hMissing hpaired p₀ w hw
  have hqOld : gluePoint gen B g root q = Sum.inl v :=
    hFollow.symm.trans (by simpa only [hp₀] using hEnd)
  have hv : v = root :=
    gluePoint_inl_eq_root gen B g root v q hqOld
  have hReturn :
      (completedStage G gen B g root hMissing hpaired).followWord
        (gluePoint gen B g root p₀) w =
      gluePoint gen B g root p₀ := by
    calc
      (completedStage G gen B g root hMissing hpaired).followWord
          (gluePoint gen B g root p₀) w =
        Sum.inl v := by simpa only [hp₀] using hEnd
      _ = Sum.inl root := congrArg Sum.inl hv
      _ = gluePoint gen B g root p₀ := hp₀.symm
  exact ⟨hv,
    (completedStage_attached_B_return_iff_kernel
      G gen B g root hMissing hpaired p₀ w hw).mp hReturn⟩

end IsolatedCosetGluing

variable {ι V OldEdge Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

/-- Genuine signed type-(2) B-orbit detector for a stable
labelled group quotient.

Suppose a real complete signed Cayley(G)->augmented H stage
morphism takes some upstairs x to the OLD attachment root
and another upstairs y to ANY OLD vertex. If y lies in
xG[B] and Q:G->H is stable on B, then x=y.

This is a strong NONCOLLISION theorem for original OLD
augmented-stage images; it is independent of the global
geometry of any chosen G-rooted multi-coset extension.
Actual source compatibility for every relevant OLD G
multiCE vertex is a separate, nontrivial obligation. -/
theorem LabelledGroupQuotient.augmentedStage_old_B_orbit_injective
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hStable : Q.StableAt B)
    (H : EGraph V OldEdge ι)
    (g : Δ) (root : V)
    (hMissing : ∀ e : OldEdge,
      H.source e = root → signedBase (H.label e) ∉ B)
    (hpaired : H.LocallyPairedLabels)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (IsolatedCosetGluing.completedStage
        H genΔ B g root hMissing hpaired).toEGraph.toLabelledGraph)
    (x y : Γ)
    (hx : F.onVertex x = Sum.inl root)
    (hy : ∃ v : V, F.onVertex y = Sum.inl v)
    (hyB : y ∈ generatedLeftCoset genΓ B x) :
    x = y := by
  let T := IsolatedCosetGluing.completedStage
    H genΔ B g root hMissing hpaired
  obtain ⟨w, hw, hxy⟩ :=
    (mem_generatedLeftCoset_iff_subalphabetReachable genΓ B x y).mp hyB
  obtain ⟨v, hv⟩ := hy
  have hOldEnd : T.followWord (Sum.inl root) w = Sum.inl v := by
    have h := (cayleyGraph genΓ).hom_followWord T F x w
    rw [hx, hxy, hv] at h
    exact h
  have hDown :
      PSTS.SignedWord.evalGroup genΔ w = 1 :=
    (IsolatedCosetGluing.completedStage_root_B_old_endpoint_implies_kernel
      H genΔ B g root hMissing hpaired w hw v hOldEnd).2
  have hUp :
      PSTS.SignedWord.evalGroup genΓ w = 1 := by
    have hKernel := Q.evalGroup_eq_of_stableAt
      hStable hw (LabelWord.uses_nil B)
      (by simpa using hDown)
    simpa using hKernel
  have hWord :
      x * PSTS.SignedWord.evalGroup genΓ w = y := by
    calc
      x * PSTS.SignedWord.evalGroup genΓ w =
        (cayleyGraph genΓ).followWord x w :=
          (cayleyGraph.followWord_eq_mul_evalGroup genΓ x w).symm
      _ = y := hxy
  simpa [hUp] using hWord.symm

end ABO
end PSTSEPPA
