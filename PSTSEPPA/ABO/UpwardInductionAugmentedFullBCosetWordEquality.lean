import PSTSEPPA.ABO.IsolatedCosetCompletedBOrbitDetector
import PSTSEPPA.ABO.CosetConnectivity
import PSTSEPPA.ABO.KRetractableCosetIntersections

/-!
# Exact signed B-word equality in an ISOLATED full-coset attachment

This theorem applies to the genuinely constructed `IsolatedCosetGluing`
stage: its attachment root has NO OLD B-labelled outgoing edge. The
full H[B] coset is attached at that ONE old root with all other
coset vertices fresh, followed by legal stationary-loop completion.

This is a valid rank-one/type-(2) augmentation and a useful model
calculation for the word-equality step in corrected ABO 4.7(iii).
However, a NONTRIVIAL proper B-cluster already contains original
B-edges. The source's general proper n≥2 B-augmentation must
identify an ENTIRE existing B-component with its full H[B] coset.
The single-root construction and the theorems below DO NOT
implement or prove that general source-cover geometry.

For the present legal isolated attachment, every B-word w from a
genuine glued H[B]-coset point p has an EXACT completed-stage
endpoint `gluePoint(q)` with group coordinate
`q.1 = p.1 * SignedWord.evalGroup gen w`.
Two real signed B-words from the SAME such point ending at the
SAME actual stage vertex therefore have equal group word values.
The proof preserves both positive/inverse signed directed tokens
and treats all missing labels as stationary loops only.

No global ambient embedding of the completed stage in Cayley(H)
is assumed: outside-B loops generally preclude such a map.
-/
namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- In a genuine legally completed signed H-stage with a
new full H[B] coset attached at its old root, any two real
signed B-words from the SAME attached point with the SAME
actual completed-stage endpoint have exactly equal values
in H. No H ambient embedding assumption is used. -/
theorem completedStage_attached_B_sameEndpoint_evalGroup_eq
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels)
    (p : CosetPoint gen B g)
    (w₁ w₂ : LabelWord ι)
    (hw₁ : LabelWord.Uses B w₁)
    (hw₂ : LabelWord.Uses B w₂)
    (hEq :
      (completedStage G gen B g root hMissing hpaired).followWord
        (gluePoint gen B g root p) w₁ =
      (completedStage G gen B g root hMissing hpaired).followWord
        (gluePoint gen B g root p) w₂) :
    PSTS.SignedWord.evalGroup gen w₁ =
      PSTS.SignedWord.evalGroup gen w₂ := by
  obtain ⟨q₁, hEnd₁, hVal₁⟩ :=
    completedStage_attached_B_followWord_exact
      G gen B g root hMissing hpaired p w₁ hw₁
  obtain ⟨q₂, hEnd₂, hVal₂⟩ :=
    completedStage_attached_B_followWord_exact
      G gen B g root hMissing hpaired p w₂ hw₂
  have hGlue :
      gluePoint gen B g root q₁ =
      gluePoint gen B g root q₂ :=
    hEnd₁.symm.trans (hEq.trans hEnd₂)
  have hPoint : q₁ = q₂ :=
    (gluePoint_injective gen B g root) hGlue
  have hMul :
      p.1 * PSTS.SignedWord.evalGroup gen w₁ =
      p.1 * PSTS.SignedWord.evalGroup gen w₂ := by
    calc
      p.1 * PSTS.SignedWord.evalGroup gen w₁ = q₁.1 :=
        hVal₁.symm
      _ = q₂.1 := congrArg Subtype.val hPoint
      _ = p.1 * PSTS.SignedWord.evalGroup gen w₂ := hVal₂
  exact mul_left_cancel hMul

/-- Isolated-root augmentation analogue of the signed two-piece
word-equality calculation needed in corrected ABO 4.7(iii):
if the original ambient B-word p and the two constituent
words w₁ and w₂ (with the second path reversed) have the
same ACTUAL signed endpoint in the genuine completed
B-AUGMENTATION, then
  [p]_H = [w₁ inv(w₂)]_H.

This supplies the algebraic equality IN THIS ISOLATED-ROOT STAGE.
It is not by itself the source's general proper B-cluster
augmentation, whose root may have genuine old B-edges.
No distinct original quotient tags are identified by ambient
H-coordinate equality. -/
theorem completedStage_properTwoPiece_BWordEquality
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hpaired : G.LocallyPairedLabels)
    (p₀ : CosetPoint gen B g)
    (C₁ C₂ : Finset ι)
    (p w₁ w₂ : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hw₁ : LabelWord.Uses (B ∩ C₁) w₁)
    (hw₂ : LabelWord.Uses (B ∩ C₂) w₂)
    (hSameEndpoint :
      (completedStage G gen B g root hMissing hpaired).followWord
        (gluePoint gen B g root p₀) p =
      (completedStage G gen B g root hMissing hpaired).followWord
        (gluePoint gen B g root p₀)
          (w₁ ++ PSTS.SignedWord.inv w₂)) :
    PSTS.SignedWord.evalGroup gen p =
      PSTS.SignedWord.evalGroup gen
        (w₁ ++ PSTS.SignedWord.inv w₂) := by
  have hW₁ : LabelWord.Uses B w₁ :=
    LabelWord.Uses.mono_explicit
      (B ∩ C₁) B Finset.inter_subset_left w₁ hw₁
  have hW₂ : LabelWord.Uses B (PSTS.SignedWord.inv w₂) :=
    LabelWord.Uses.mono_explicit
      (B ∩ C₂) B Finset.inter_subset_left
      (PSTS.SignedWord.inv w₂) hw₂.inv
  have hConcat : LabelWord.Uses B
      (w₁ ++ PSTS.SignedWord.inv w₂) :=
    (LabelWord.uses_append B w₁ (PSTS.SignedWord.inv w₂)).mpr
      ⟨hW₁,hW₂⟩
  exact completedStage_attached_B_sameEndpoint_evalGroup_eq
    G gen B g root hMissing hpaired p₀
    p (w₁ ++ PSTS.SignedWord.inv w₂)
    hp hConcat hSameEndpoint

end IsolatedCosetGluing
end ABO
end PSTSEPPA
