import PSTSEPPA.ABO.KStableTranslatedCosetEquiv
import PSTSEPPA.ABO.LocalRankRetractableSubalphabet
import PSTSEPPA.ABO.KRetractableCosetIntersections
import PSTSEPPA.ABO.StageStabilityWordKernel
import PSTSEPPA.ABO.SourceLiteralY1X2AllRankOne

/-!
# Local generated-subgroup restriction of actual stable labelled quotients

The full corrected ABO Theorem 4.7(ii) coset geometry is stated
over globally RETRACTABLE generated groups. However the actual
first-rank source tower provides only 2-retractable
    G = T(X₂^all), H = T(Y₁)
and a 1-stable surjection Q:G↠H.

We already proved that the genuine local generated group Γ[A],
with outside-A generator labels sent to 1, is GLOBALLY retractable
whenever Γ is k-retractable and |A|≤k.

This file supplies the other indispensable link: every
generator-preserving labelled group quotient Q:G↠H RESTRICTS to
the actual local generated subgroups Q_A:G[A]↠H[A],
with all original labels preserved, INCLUDING outside-A
labels (which become identity); and k-stability of Q is
inherited by Q_A at the SAME rank k.

The latter requires real signed-word calculation, because
local group words may contain labels outside A even though
these act trivially in the completed local group. Restrict
the word to A, preserve support in any tested B, use original
Q-stability on B, and coerce back to the genuine generated
subgroup (not an abstract quotient or a false ambient value
identification).

We instantiate the construction at the actual printed
first-rank G₂→H₁ group tower on any two-letter A.
The resulting local G[A] and H[A] are BOTH genuinely
retractable, and Q_A is still 1-stable. This is the
precise algebraic input for the source's local P_A
coset extensions, not itself the original G-level
old-skeleton component and full multiCE embeddedness
proof or bridge freeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}

namespace LabelledGroupQuotient

variable (Q : LabelledGroupQuotient genΓ genΔ)

/-- An honest generator-preserving SURJECTIVE labelled
quotient G[A]↠H[A], with every label outside A acting
as the identity on both sides. This is the actual
restriction of Q.hom, not an assumed local cover. -/
noncomputable def localGeneratedSubgroupQuotient
    (A : Finset ι) :
    LabelledGroupQuotient
      (trivialCompletionGenerator genΓ A)
      (trivialCompletionGenerator genΔ A) where
  hom := Q.subgroupHom A
  map_gen := by
    intro i
    by_cases hi : i ∈ A
    · apply Subtype.ext
      change Q.hom (genΓ i) = genΔ i
      exact Q.map_gen i
    · simp [trivialCompletionGenerator, hi]
  surjective := Q.subgroupHom_surjective A

/-- The genuine local subgroup homomorphism forgets NO
additional group coordinate: its underlying ambient
value is precisely the original quotient homomorphism. -/
@[simp] theorem localGeneratedSubgroupQuotient_val
    (A : Finset ι) (x : generatedSubgroup genΓ A) :
    (((Q.localGeneratedSubgroupQuotient A).hom x :
        generatedSubgroup genΔ A) : Δ) =
      Q.hom x.1 :=
  rfl

/-- Every rank-k stable surjective labelled quotient
remains rank-k stable after passage to ACTUAL A-generated
subgroups with identity completion of all outside-A labels.
No condition A⊆B or B⊆A is assumed on the tested B:
words over B are first restricted to A∩B. -/
theorem localGeneratedSubgroupQuotient_kStable
    (A : Finset ι) (k : ℕ)
    (hk : Q.KStable k) :
    (Q.localGeneratedSubgroupQuotient A).KStable k := by
  apply (Q.localGeneratedSubgroupQuotient A).kStable_of_word_kernel k
  intro B hB w hw hDown
  have hDown' :
      PSTS.SignedWord.evalGroup genΔ (LabelWord.restrictTo A w) = 1 := by
    have h := congrArg
      (fun x : generatedSubgroup genΔ A => (x : Δ)) hDown
    simpa only [coe_evalGroup_trivialCompletionGenerator,
      Subgroup.coe_one] using h
  have hwB : LabelWord.Uses B (LabelWord.restrictTo A w) :=
    LabelWord.Uses.of_deleteGenerators B (Finset.univ \ A) w hw
  have hDownEq :
      PSTS.SignedWord.evalGroup genΔ (LabelWord.restrictTo A w) =
      PSTS.SignedWord.evalGroup genΔ ([] : LabelWord ι) := by
    simpa using hDown'
  have hUp :=
    Q.evalGroup_eq_of_stableAt
      (hk B hB) hwB (LabelWord.uses_nil B) hDownEq
  have hUp' :
      PSTS.SignedWord.evalGroup genΓ (LabelWord.restrictTo A w) = 1 := by
    simpa using hUp
  apply Subtype.ext
  change
    ((PSTS.SignedWord.evalGroup
      (trivialCompletionGenerator genΓ A) w :
        generatedSubgroup genΓ A) : Γ) = (1 : Γ)
  rw [coe_evalGroup_trivialCompletionGenerator]
  exact hUp'

end LabelledGroupQuotient

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual first-rank printed one-stable group projection
G₂=T(X₂^all) → H₁=T(Y₁), restricted to its true
A-generated finite local subgroup actions. -/
noncomputable def sourceLiteralY1X2AllLocalQuotient
    (src dst : ι → V) (A : Finset ι) :
    LabelledGroupQuotient
      (trivialCompletionGenerator
        (sourceLiteralY1X2AllGenerator src dst) A)
      (trivialCompletionGenerator
        (sourceLiteralY1 src dst).transitionSubgroupGenerator A) :=
  (sourceLiteralY1X2AllToY1 src dst).localGeneratedSubgroupQuotient A

/-- The true local group quotient retains the rank-one
stability established for the original literal
T(X₂^all)→T(Y₁) first-rank projection. -/
theorem sourceLiteralY1X2AllLocalQuotient_oneStable
    (src dst : ι → V) (A : Finset ι) :
    (sourceLiteralY1X2AllLocalQuotient src dst A).KStable 1 :=
  (sourceLiteralY1X2AllToY1 src dst).localGeneratedSubgroupQuotient_kStable
    A 1 (sourceLiteralY1X2AllToY1_oneStable src dst)

/-- The genuine G₂[A] local labelled group is
GLOBALLY retractable for every |A|≤2, even though
the full literal group is only 2-retractable. -/
theorem sourceLiteralY1X2AllLocal_retractable
    (src dst : ι → V)
    (A : Finset ι) (hA : A.card ≤ 2) :
    Retractable (trivialCompletionGenerator
      (sourceLiteralY1X2AllGenerator src dst) A) :=
  retractable_trivialCompletionGenerator_of_kRetractable
    (sourceLiteralY1X2AllGenerator src dst) 2
    (sourceLiteralY1X2All_twoRetractable src dst) A hA

/-- Similarly the true printed H₁[A] local group is
globally retractable for each |A|≤2,
as needed for the ACTUAL source local P_A geometry. -/
theorem sourceLiteralY1Local_retractable
    (src dst : ι → V)
    (A : Finset ι) (hA : A.card ≤ 2) :
    Retractable (trivialCompletionGenerator
      (sourceLiteralY1 src dst).transitionSubgroupGenerator A) :=
  retractable_trivialCompletionGenerator_of_kRetractable
    (sourceLiteralY1 src dst).transitionSubgroupGenerator 2
    (sourceLiteralY1_transitionTwoRetractable src dst) A hA

end ABO
end PSTSEPPA
