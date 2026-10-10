import PSTSEPPA.ABO.RankOneRetractability
import PSTSEPPA.ABO.LocalRankRetractableSubalphabet

/-!
# A finite globally retractable unary-detector labelled group

This is a possible algebraic ingredient of the still-open source
Theorem-3.8 base H₁ construction, NOT a finished H₁-cover.

Given arbitrary labelled Γ, for each label i consider its actual
cyclic subgroup Γ[{i}], completed by trivial generators outside i.
The dependent product D = Π i Γ[{i}] carries the generator j acting
on coordinate i as gen j if i=j, otherwise as identity.

Every coordinate's labelled generator family is GLOBALLY RETRACTABLE
by the certified rank-one-to-global subalphabet lemma (#310) and the
automatic KRetractable-one fact. Since word evaluation in the product
is coordinatewise, the ENTIRE detector group is globally
retractable. If Γ is finite and the alphabet is finite, D is finite.

No commuting or injective/trivial-generator assumptions are imposed
on Γ itself. The crucial equalities hold for arbitrary signed words,
including inverses.

Next possible step (NOT claimed here): synchronize D with Γ and
prove the resulting generated subgroup provides a finite 1-stable,
2-retractable group above Γ. The necessary Y₁-cover geometry from
corrected ABO Theorem 3.8 is still a separate hard obligation.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Product of all ACTUAL singleton-generated subgroups;
coordinates are dependent on their unsigned generator label. -/
abbrev UnaryDetectorGroup (gen : ι → Γ) :=
  ∀ i : ι, generatedSubgroup gen ({i} : Finset ι)

/-- Each positive letter j acts on precisely its own cyclic
coordinate. All other coordinates see the identity. -/
def unaryDetectorGenerator (gen : ι → Γ) :
    ι → UnaryDetectorGroup gen :=
  fun j i => trivialCompletionGenerator gen ({i} : Finset ι) j

@[simp]
theorem unaryDetectorGenerator_apply
    (gen : ι → Γ) (j i : ι) :
    unaryDetectorGenerator gen j i =
      trivialCompletionGenerator gen ({i} : Finset ι) j :=
  rfl

/-- Full signed-word evaluation in D is coordinatewise evaluation
in the actual trivially completed singleton subgroup Γ[{i}]. -/
theorem evalGroup_unaryDetector_apply
    (gen : ι → Γ) (w : LabelWord ι) (i : ι) :
    (PSTS.SignedWord.evalGroup (unaryDetectorGenerator gen) w) i =
      PSTS.SignedWord.evalGroup
        (trivialCompletionGenerator gen ({i} : Finset ι)) w := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      cases s <;>
        simp [PSTS.SignedWord.evalGroup_cons,
          unaryDetectorGenerator, ih]

/-- Every singleton group factor is globally retractable, although
the ambient Γ need not be; this is the precise application of
the automatic KRetractable-one theorem and local-to-global bridge. -/
theorem retractable_singletonCompletion
    (gen : ι → Γ) (i : ι) :
    Retractable (trivialCompletionGenerator gen ({i} : Finset ι)) := by
  exact retractable_trivialCompletionGenerator_of_kRetractable
    gen 1 (kRetractable_one gen) {i} (by simp)

/-- The entire detector generator family on Π_i Γ[{i}]
is GLOBALLY RETRACTABLE. Equality in the product is projected
to each factor, its one-letter retraction applied, then the
resulting coordinates reassembled by function extensionality.
No global retractability of Γ is assumed. -/
theorem retractable_unaryDetectorGenerator
    (gen : ι → Γ) :
    Retractable (unaryDetectorGenerator gen) := by
  intro a p q hpq
  apply funext
  intro i
  have hEq :
      PSTS.SignedWord.evalGroup
          (trivialCompletionGenerator gen ({i} : Finset ι)) p =
        PSTS.SignedWord.evalGroup
          (trivialCompletionGenerator gen ({i} : Finset ι)) q := by
    have hCoord :=
      congrArg (fun x : UnaryDetectorGroup gen => x i) hpq
    simpa only [evalGroup_unaryDetector_apply] using hCoord
  have hErase :=
    (retractable_singletonCompletion gen i) a p q hEq
  simpa only [evalGroup_unaryDetector_apply] using hErase

variable [Finite Γ]

/-- The true dependent product of the singleton-generated subgroups
is FINITE, even for repeated or trivial generators. -/
theorem finite_unaryDetectorGroup (gen : ι → Γ) :
    Finite (UnaryDetectorGroup gen) := by
  classical
  letI : Fintype Γ := Fintype.ofFinite _
  infer_instance

end ABO
end PSTSEPPA
