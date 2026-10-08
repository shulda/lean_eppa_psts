import PSTSEPPA.ABO.CosetConnectivity
import Mathlib.Data.Finset.Card

/-!
# Stable labelled group quotients

This file isolates the algebraic notion of k-stability used throughout
Auinger--Bitterlich--Otto Sections 3--5.

A labelled quotient maps each distinguished generator to the equally labelled
generator downstairs.  Stability at an alphabet A means that the induced map
G[A] -> H[A] is injective.  k-stability means this for every alphabet of
cardinality at most k.
-/

namespace PSTSEPPA
namespace ABO

open PSTS

variable {ι Γ Δ Θ : Type*}

/-- A surjective homomorphism of labelled groups, preserving every
distinguished positive generator. -/
structure LabelledGroupQuotient
    [Group Γ] [Group Δ]
    (genΓ : ι → Γ) (genΔ : ι → Δ) where
  hom : Γ →* Δ
  map_gen : ∀ i, hom (genΓ i) = genΔ i
  surjective : Function.Surjective hom

namespace LabelledGroupQuotient

variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable (Q : LabelledGroupQuotient genΓ genΔ)

@[simp]
theorem map_evalGroupLetter (s : SignedLabel ι) :
    Q.hom (PSTS.SignedWord.evalGroupLetter genΓ s) =
      PSTS.SignedWord.evalGroupLetter genΔ s := by
  cases s with
  | pos i =>
      exact Q.map_gen i
  | neg i =>
      simp [PSTS.SignedWord.evalGroupLetter, Q.map_gen]

@[simp]
theorem map_evalGroup (w : LabelWord ι) :
    Q.hom (PSTS.SignedWord.evalGroup genΓ w) =
      PSTS.SignedWord.evalGroup genΔ w := by
  induction w with
  | nil =>
      simp
  | cons s w ih =>
      simp [PSTS.SignedWord.evalGroup, Q.map_evalGroupLetter, ih]

/-- The ambient quotient sends every subalphabet-generated
subgroup into the corresponding subgroup downstairs. -/
theorem hom_mem_generatedSubgroup
    (A : Finset ι) {x : Γ}
    (hx : x ∈ generatedSubgroup genΓ A) :
    Q.hom x ∈ generatedSubgroup genΔ A := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with ⟨i, rfl⟩
      rw [Q.map_gen]
      exact generator_mem_generatedSubgroup genΔ A i.2
  | one =>
      simp
  | mul x y hx hy ihx ihy =>
      exact (generatedSubgroup genΔ A).mul_mem ihx ihy
  | inv x hx ih =>
      exact (generatedSubgroup genΔ A).inv_mem ih

/-- The labelled quotient restricts to every subalphabet-generated subgroup. -/
def subgroupHom (A : Finset ι) :
    generatedSubgroup genΓ A →* generatedSubgroup genΔ A where
  toFun x :=
    ⟨Q.hom x.1, Q.hom_mem_generatedSubgroup A x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

@[simp]
theorem subgroupHom_val (A : Finset ι)
    (x : generatedSubgroup genΓ A) :
    ((Q.subgroupHom A x : generatedSubgroup genΔ A) : Δ) =
      Q.hom x.1 :=
  rfl

/-- Every element of a generated subgroup downstairs has a preimage in
the equally generated subgroup upstairs. -/
theorem exists_subgroup_preimage
    (A : Finset ι) {y : Δ}
    (hy : y ∈ generatedSubgroup genΔ A) :
    ∃ x : Γ,
      x ∈ generatedSubgroup genΓ A ∧ Q.hom x = y := by
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
      rcases hz with ⟨i, rfl⟩
      exact
        ⟨genΓ i.1,
          generator_mem_generatedSubgroup genΓ A i.2,
          Q.map_gen i.1⟩
  | one =>
      exact ⟨1, by simp, by simp⟩
  | mul x y hx hy ihx ihy =>
      rcases ihx with ⟨x', hxA, hx'⟩
      rcases ihy with ⟨y', hyA, hy'⟩
      refine ⟨x' * y', (generatedSubgroup genΓ A).mul_mem hxA hyA, ?_⟩
      simp [hx', hy']
  | inv x hx ih =>
      rcases ih with ⟨x', hxA, hx'⟩
      refine ⟨x'⁻¹, (generatedSubgroup genΓ A).inv_mem hxA, ?_⟩
      simp [hx']

/-- Generator preservation alone already makes every induced subalphabet map
surjective. -/
theorem subgroupHom_surjective (A : Finset ι) :
    Function.Surjective (Q.subgroupHom A) := by
  intro y
  rcases Q.exists_subgroup_preimage A y.2 with ⟨x, hxA, hxy⟩
  refine ⟨⟨x, hxA⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- Stability on one specified subalphabet. -/
def StableAt (A : Finset ι) : Prop :=
  Function.Injective (Q.subgroupHom A)

/-- k-stability in the source convention: all generated subgroups on at most
k labels are preserved injectively. -/
def KStable (k : Nat) : Prop :=
  ∀ A : Finset ι, A.card ≤ k → Q.StableAt A

theorem stableAt_of_kStable {k : Nat}
    (hk : Q.KStable k) (A : Finset ι) (hA : A.card ≤ k) :
    Q.StableAt A :=
  hk A hA

/-- Stability is downward closed in the rank. -/
theorem kStable_mono {j k : Nat}
    (hk : Q.KStable k) (hjk : j ≤ k) :
    Q.KStable j := by
  intro A hA
  exact hk A (hA.trans hjk)

/-- A stable restriction is a bijection on the corresponding generated
subgroups. -/
theorem subgroupHom_bijective {A : Finset ι}
    (hA : Q.StableAt A) :
    Function.Bijective (Q.subgroupHom A) :=
  ⟨hA, Q.subgroupHom_surjective A⟩

/-- Equality of A-supported word values downstairs reflects to equality
upstairs under stability at A. -/
theorem evalGroup_eq_of_stableAt
    [Fintype ι] [DecidableEq ι]
    {A : Finset ι} (hA : Q.StableAt A)
    {p q : LabelWord ι}
    (hp : LabelWord.Uses A p)
    (hq : LabelWord.Uses A q)
    (heq :
      PSTS.SignedWord.evalGroup genΔ p =
        PSTS.SignedWord.evalGroup genΔ q) :
    PSTS.SignedWord.evalGroup genΓ p =
      PSTS.SignedWord.evalGroup genΓ q := by
  let xp : generatedSubgroup genΓ A :=
    ⟨PSTS.SignedWord.evalGroup genΓ p,
      evalGroup_mem_generatedSubgroup_of_uses genΓ A hp⟩
  let xq : generatedSubgroup genΓ A :=
    ⟨PSTS.SignedWord.evalGroup genΓ q,
      evalGroup_mem_generatedSubgroup_of_uses genΓ A hq⟩
  have himage : Q.subgroupHom A xp = Q.subgroupHom A xq := by
    apply Subtype.ext
    change
      Q.hom (PSTS.SignedWord.evalGroup genΓ p) =
        Q.hom (PSTS.SignedWord.evalGroup genΓ q)
    rw [Q.map_evalGroup, Q.map_evalGroup]
    exact heq
  exact congrArg Subtype.val (hA himage)

/-- Composition of labelled quotients. -/
def comp
    [Group Θ]
    {genΘ : ι → Θ}
    (R : LabelledGroupQuotient genΔ genΘ) :
    LabelledGroupQuotient genΓ genΘ where
  hom := R.hom.comp Q.hom
  map_gen i := by
    simp [Q.map_gen, R.map_gen]
  surjective := R.surjective.comp Q.surjective

end LabelledGroupQuotient

end ABO
end PSTSEPPA
