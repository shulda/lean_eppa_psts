import PSTSEPPA.ABO.RetractabilityRetraction
import PSTSEPPA.ABO.SynchronizedGeneratedGroup

/-!
# Canonical isomorphism of generated labelled groups with identical word kernels

For two genuinely generated groups Γ and Δ over the SAME labelled
positive-generator alphabet ι, assume exactly the same chronological
signed words evaluate to the identity in both groups.

Then equality of arbitrary signed word values is also equivalent:
compare the identity value of (inverse p) ++ q in each group.

Choose a representative signed word for every element of Γ. Evaluating
it in Δ is INDEPENDENT of the choice, because of the common full
word kernel, and gives a true group homomorphism preserving every
distinguished generator. Generation of Δ proves its surjectivity;
the opposite kernel implication proves injectivity. The resulting
MulEquiv is therefore an honest generator-preserving labelled-group
isomorphism, not merely a bijection of word sets.

The proof is generic; it does not assume finite groups, generator
injectivity, free groups, an existing quotient map, commutativity or
a bound on lengths/number of labels. In particular it applies to
the paper's literal T(Y₁) and the separately constructed synchronized
source H₁ after their two-sided kernel comparison has been proved.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

/-- The same signed IDENTITY-word kernel implies that ALL
chronological signed-word value equalities transfer, not only
identity relations. Both directions can be obtained by swapping
Γ and Δ and taking the symmetric kernel equivalence. -/
theorem labelled_evalGroup_eq_of_kernel_iff
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (hker : ∀ w : LabelWord ι,
      PSTS.SignedWord.evalGroup genΓ w = 1 ↔
      PSTS.SignedWord.evalGroup genΔ w = 1)
    {p q : LabelWord ι}
    (hpq :
      PSTS.SignedWord.evalGroup genΓ p =
        PSTS.SignedWord.evalGroup genΓ q) :
    PSTS.SignedWord.evalGroup genΔ p =
      PSTS.SignedWord.evalGroup genΔ q := by
  have hrelation :
      PSTS.SignedWord.evalGroup genΓ
        (PSTS.SignedWord.inv p ++ q) = 1 := by
    rw [PSTS.SignedWord.evalGroup_append,
      PSTS.SignedWord.evalGroup_inv, hpq]
    simp
  have hdown := (hker (PSTS.SignedWord.inv p ++ q)).mp hrelation
  rw [PSTS.SignedWord.evalGroup_append,
    PSTS.SignedWord.evalGroup_inv] at hdown
  exact inv_mul_eq_one.mp hdown

/-- Genuine generator-preserving homomorphism induced by a
common signed word kernel. The word-representative choice is
used ONLY internally and has no effect on group values. -/
noncomputable def labelledWordKernelHom
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (hgenΓ : IsGenerated genΓ)
    (hker : ∀ w : LabelWord ι,
      PSTS.SignedWord.evalGroup genΓ w = 1 ↔
      PSTS.SignedWord.evalGroup genΔ w = 1) :
    Γ →* Δ where
  toFun g :=
    PSTS.SignedWord.evalGroup genΔ (wordRep genΓ hgenΓ g)
  map_one' := by
    have hΓ :
        PSTS.SignedWord.evalGroup genΓ
          (wordRep genΓ hgenΓ 1) = 1 :=
      evalGroup_wordRep genΓ hgenΓ 1
    exact (hker _).mp hΓ
  map_mul' x y := by
    have hΓ :
        PSTS.SignedWord.evalGroup genΓ (wordRep genΓ hgenΓ (x * y)) =
        PSTS.SignedWord.evalGroup genΓ
          (wordRep genΓ hgenΓ x ++ wordRep genΓ hgenΓ y) := by
      simp [evalGroup_wordRep, PSTS.SignedWord.evalGroup_append]
    have hΔ :=
      labelled_evalGroup_eq_of_kernel_iff genΓ genΔ hker hΓ
    simpa only [PSTS.SignedWord.evalGroup_append] using hΔ

/-- The canonical word-induced homomorphism preserves each
positive labelled generator *literally*, including repeated
or identity generators. -/
@[simp] theorem labelledWordKernelHom_generator
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (hgenΓ : IsGenerated genΓ)
    (hker : ∀ w : LabelWord ι,
      PSTS.SignedWord.evalGroup genΓ w = 1 ↔
      PSTS.SignedWord.evalGroup genΔ w = 1)
    (i : ι) :
    labelledWordKernelHom genΓ genΔ hgenΓ hker (genΓ i) = genΔ i := by
  have hΓ :
      PSTS.SignedWord.evalGroup genΓ
        (wordRep genΓ hgenΓ (genΓ i)) =
      PSTS.SignedWord.evalGroup genΓ
        [PSTS.SignedLetter.pos i] := by simp
  have hΔ :=
    labelled_evalGroup_eq_of_kernel_iff genΓ genΔ hker hΓ
  change PSTS.SignedWord.evalGroup genΔ
    (wordRep genΓ hgenΓ (genΓ i)) = genΔ i
  simpa [PSTS.SignedWord.evalGroup] using hΔ

/-- Equal signed-word kernels give the honest labelled GROUP
ISOMORPHISM, with no ambient free-group assumption. All elements
of Δ are reached by word evaluation because its generator family
is genuinely generating; the reverse kernel test makes the map
injective. -/
noncomputable def labelledWordKernelMulEquiv
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (hgenΓ : IsGenerated genΓ) (hgenΔ : IsGenerated genΔ)
    (hker : ∀ w : LabelWord ι,
      PSTS.SignedWord.evalGroup genΓ w = 1 ↔
      PSTS.SignedWord.evalGroup genΔ w = 1) :
    Γ ≃* Δ := by
  let F := labelledWordKernelHom genΓ genΔ hgenΓ hker
  apply MulEquiv.ofBijective F
  constructor
  · intro x y hxy
    have hΔ :
        PSTS.SignedWord.evalGroup genΔ (wordRep genΓ hgenΓ x) =
        PSTS.SignedWord.evalGroup genΔ (wordRep genΓ hgenΓ y) := hxy
    have hΓ :=
      labelled_evalGroup_eq_of_kernel_iff genΔ genΓ
        (fun w => (hker w).symm) hΔ
    simpa only [evalGroup_wordRep] using hΓ
  · intro y
    obtain ⟨w, hw⟩ := hgenΔ.exists_evalGroup_eq y
    refine ⟨PSTS.SignedWord.evalGroup genΓ w, ?_⟩
    have hΓ :
        PSTS.SignedWord.evalGroup genΓ
          (wordRep genΓ hgenΓ
            (PSTS.SignedWord.evalGroup genΓ w)) =
        PSTS.SignedWord.evalGroup genΓ w :=
      evalGroup_wordRep genΓ hgenΓ _
    have hΔ :=
      labelled_evalGroup_eq_of_kernel_iff genΓ genΔ hker hΓ
    exact hΔ.trans hw

/-- Generator preservation is part of the concrete MulEquiv API;
the isomorphism cannot silently permute the generator alphabet. -/
@[simp] theorem labelledWordKernelMulEquiv_generator
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (hgenΓ : IsGenerated genΓ) (hgenΔ : IsGenerated genΔ)
    (hker : ∀ w : LabelWord ι,
      PSTS.SignedWord.evalGroup genΓ w = 1 ↔
      PSTS.SignedWord.evalGroup genΔ w = 1)
    (i : ι) :
    labelledWordKernelMulEquiv genΓ genΔ hgenΓ hgenΔ hker (genΓ i) =
      genΔ i := by
  exact labelledWordKernelHom_generator genΓ genΔ hgenΓ hker i

end ABO
end PSTSEPPA
