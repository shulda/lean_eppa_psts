import PSTSEPPA.ABO.IsolatedCosetCompletedBOrbitDetector
import PSTSEPPA.ABO.CosetConnectivity

/-!
# ABO Theorem 4.7(iii): TRUE B-AUGMENTATION endpoints certify H-word equality

The published corrected upward proof's OFF-SKELETON proper
n≥2 B-cluster branch uses the canonical H-stage B-augmentation:
the proper B-cluster is blown up to a genuine FULL H[B] coset.
Two signed B-words from the same attached coset point with
the same actual completed-stage endpoint must have the SAME
group value in H. This group equality is then reflected
to G by k-stability (|B|≤k).

This is NOT a consequence of injectivity of an unaugmented
H coset extension into H, which can fail for different old
component tags. Nor can we assume the WHOLE loop-completed
H-stage maps to Cayley(H), since legal outside-B fixed loops
need not be H-generators equal to the identity.

Instead we use the already-certified EXACT signed B-word
action in the REAL attached H[B] coset after legal trivial
loop completion:

   T.followWord (gluePoint(p)) w = gluePoint(q),
   q.1 = p.1 * [w]_H.

The gluing map is injective on the actual full B-coset
points, even at the old attachment root. Hence equal
completed-stage endpoints yield equal coset point
coordinates; ordinary group cancellation now proves
equality of the two H-word values.

Both POSITIVE/INVERSE signed edge tokens and loops are
treated as real completed-stage paths; no false old edge
or ambient tag collapse is used. This is the exact
source AUGMENTATION word-equality step needed by
the independently formalized proper two-piece bridge
reassembly. Constructing the relevant B-augmented
G→H stage cover and proving its required endpoint
equality remain separate source 4.7(iii) obligations.
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

/-- SOURCE CORRECTED 4.7(iii) proper n≥2 H-equality:
if the original ambient B-word p and the two constituent
words w₁ and w₂ (with the second path reversed) have the
same ACTUAL signed endpoint in the genuine completed
B-AUGMENTATION, then
  [p]_H = [w₁ inv(w₂)]_H.

This supplies precisely the H-word relation used for
k-stable source G bridge reassembly, WITHOUT any
assumption that two H group coordinates identify
different original quotient tags. -/
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
