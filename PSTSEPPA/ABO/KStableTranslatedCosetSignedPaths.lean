import PSTSEPPA.ABO.KStableTranslatedCosetEquiv

/-!
# Exact signed B-word paths inside stable translated coset fibres

Corrected ABO Theorem 4.7 uses k-stability not merely to
identify B-coset vertex sets, but to transport/reconstruct
actual signed B-WORD paths in full B-coset constituents.

For a labelled group Γ and a fixed translated left
coset g·Γ[B], a genuine B-supported chronological signed
word w takes x to x·[w]Γ inside that SAME coset.

The labelled quotient Q : Γ ↠ Δ sends this path to
the identical signed word path in Q(g)·Δ[B].
If Q is stable at B, the already certified translated
coset equivalence reflects EVERY such labelled endpoint
equation uniquely: the downstairs B-path has the
corresponding upstairs B-path with exactly the original
signed word and chosen B-coset tag.

These lemmas concern ONE fixed coset constituent. They
do not identify distinct intrinsic B-components or
automatically embed the full MULTI-coset quotient; this
is the geometric collision analysis still required by
the corrected Theorem 4.7(ii).
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}

/-- Endpoint of a true signed B-word in the chosen
translated left B-coset; it remains in that same
coset because the full signed B-Cayley edges
are all present. Both inverse signs and B=∅ work. -/
noncomputable def leftCosetSignedWordEndpoint
    (gen : ι → Γ) (B : Finset ι) (g : Γ)
    (x : {x : Γ // x ∈ generatedLeftCoset gen B g})
    (w : LabelWord ι) (hw : LabelWord.Uses B w) :
    {y : Γ // y ∈ generatedLeftCoset gen B g} :=
  ⟨x.1 * PSTS.SignedWord.evalGroup gen w, by
    change g⁻¹ * (x.1 * PSTS.SignedWord.evalGroup gen w) ∈
      generatedSubgroup gen B
    rw [← mul_assoc]
    exact (generatedSubgroup gen B).mul_mem x.2
      (evalGroup_mem_generatedSubgroup_of_uses gen B hw)⟩

@[simp] theorem leftCosetSignedWordEndpoint_val
    (gen : ι → Γ) (B : Finset ι) (g : Γ)
    (x : {x : Γ // x ∈ generatedLeftCoset gen B g})
    (w : LabelWord ι) (hw : LabelWord.Uses B w) :
    (leftCosetSignedWordEndpoint gen B g x w hw).1 =
      x.1 * PSTS.SignedWord.evalGroup gen w :=
  rfl

namespace LabelledGroupQuotient

variable (Q : LabelledGroupQuotient genΓ genΔ)

/-- The genuine stable translated B-coset bijection
commutes with FOLLOWING AN ARBITRARY supported signed
word, not only individual positive generators. -/
theorem stableAt_leftCoset_signedWord_natural
    (B : Finset ι) (hB : Q.StableAt B)
    (g : Γ)
    (x : {x : Γ // x ∈ generatedLeftCoset genΓ B g})
    (w : LabelWord ι) (hw : LabelWord.Uses B w) :
    Q.stableAt_leftCosetEquiv B hB g
      (leftCosetSignedWordEndpoint genΓ B g x w hw) =
    leftCosetSignedWordEndpoint genΔ B (Q.hom g)
      (Q.stableAt_leftCosetEquiv B hB g x) w hw := by
  apply Subtype.ext
  change
    Q.hom (x.1 * PSTS.SignedWord.evalGroup genΓ w) =
      Q.hom x.1 * PSTS.SignedWord.evalGroup genΔ w
  rw [map_mul, Q.map_evalGroup]

/-- If two points of the SAME tagged g·G[B] are connected
by the given signed B-word upstairs, their images are
connected by the VERY SAME signed word downstairs.
Conversely, under B-stability such a downstairs path
has a UNIQUE upstairs endpoint in the fixed coset.
No ambient-group injectivity is assumed. -/
theorem stableAt_leftCoset_signedWord_endpoint_iff
    (B : Finset ι) (hB : Q.StableAt B)
    (g : Γ)
    (x y : {x : Γ // x ∈ generatedLeftCoset genΓ B g})
    (w : LabelWord ι) (hw : LabelWord.Uses B w) :
    x.1 * PSTS.SignedWord.evalGroup genΓ w = y.1 ↔
      (Q.stableAt_leftCosetEquiv B hB g x).1 *
        PSTS.SignedWord.evalGroup genΔ w =
      (Q.stableAt_leftCosetEquiv B hB g y).1 := by
  constructor
  · intro h
    have hmap := congrArg Q.hom h
    simpa only [map_mul, Q.map_evalGroup,
      Q.stableAt_leftCosetEquiv_apply] using hmap
  · intro h
    have hmap :
        Q.stableAt_leftCosetEquiv B hB g
          (leftCosetSignedWordEndpoint genΓ B g x w hw) =
        Q.stableAt_leftCosetEquiv B hB g y := by
      apply Subtype.ext
      change
        Q.hom (x.1 * PSTS.SignedWord.evalGroup genΓ w) =
          Q.hom y.1
      simpa only [map_mul, Q.map_evalGroup,
        Q.stableAt_leftCosetEquiv_apply] using h
    have heq :
        leftCosetSignedWordEndpoint genΓ B g x w hw = y :=
      (Q.stableAt_leftCosetEquiv B hB g).injective hmap
    exact congrArg Subtype.val heq

/-- Concrete rank-k reformulation: any signed B-path
inside a full translated B-coset is preserved AND
REFLECTED under k-stability whenever |B| ≤ k. -/
theorem kStable_leftCoset_signedWord_endpoint_iff
    (k : ℕ) (hk : Q.KStable k)
    (B : Finset ι) (hB : B.card ≤ k)
    (g : Γ)
    (x y : {x : Γ // x ∈ generatedLeftCoset genΓ B g})
    (w : LabelWord ι) (hw : LabelWord.Uses B w) :
    x.1 * PSTS.SignedWord.evalGroup genΓ w = y.1 ↔
      (Q.kStable_leftCosetEquiv k hk B hB g x).1 *
        PSTS.SignedWord.evalGroup genΔ w =
      (Q.kStable_leftCosetEquiv k hk B hB g y).1 := by
  exact Q.stableAt_leftCoset_signedWord_endpoint_iff
    B (hk B hB) g x y w hw

end LabelledGroupQuotient
end ABO
end PSTSEPPA
