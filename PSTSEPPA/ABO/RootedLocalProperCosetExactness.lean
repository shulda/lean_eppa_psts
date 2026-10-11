import PSTSEPPA.ABO.LocalSubgroupCosetNaturality

/-!
# Exact rooted proper-coset translation from a local subgroup into H1

Let A be any parent alphabet, D a subalphabet of A and g an
arbitrary ambient root. The local group Γ[A] is genuinely embedded
in Γ and outside-A labels are trivially completed.

For every two points x,z of Γ[A], membership of z in the local
D-coset of x is equivalent to membership of g*z in the ambient
D-coset of g*x. Moreover EVERY ambient point in the latter
coset comes from a UNIQUE local z, despite the coordinate map
Γ[A] -> Γ NOT being globally surjective.

This is the source H1[A] component-to-H1 coset translation
required for attached tagged coset copies in the first corrected
ABO stage. It applies to noncommutative groups, signed inverse
letters, repetitions and geometric loop generators. Crucially,
it is ONLY asserted for D ⊆ A; allowing arbitrary outside-A
letters would make reverse surjectivity FALSE.

The quotient component-tag compatibility is a separate theorem
(#361); the FULL CE glued quotient/augmentation comparison and
higher-rank Section 5 induction remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- An ambient left translation of the actual subgroup Γ[A]
preserves and reflects each smaller D-left coset EXACTLY.
No global retractability, free generators, or injectivity of
the label map is assumed. -/
theorem localLeftCoset_translate_iff
    (gen : ι → Γ)
    (A D : Finset ι) (hDA : D ⊆ A)
    (g : Γ) (x z : generatedSubgroup gen A) :
    z ∈ generatedLeftCoset
          (trivialCompletionGenerator gen A) D x ↔
      g * (z : Γ) ∈ generatedLeftCoset gen D (g * (x : Γ)) := by
  have hlocal :=
    mem_localGeneratedLeftCoset_iff_ambient gen D A hDA x z
  have htranslate :
      g * (z : Γ) ∈ generatedLeftCoset gen D (g * (x : Γ)) ↔
        (z : Γ) ∈ generatedLeftCoset gen D (x : Γ) := by
    change
      (g * (x : Γ))⁻¹ * (g * (z : Γ)) ∈ generatedSubgroup gen D ↔
        (x : Γ)⁻¹ * (z : Γ) ∈ generatedSubgroup gen D
    have heq :
        (g * (x : Γ))⁻¹ * (g * (z : Γ)) =
        (x : Γ)⁻¹ * (z : Γ) := by group
    rw [heq]
  exact hlocal.trans htranslate.symm

/-- Strong reverse range theorem: every point y of the
ACTUAL ambient D-coset of g*x has a unique predecessor z
inside Γ[A], since D ⊆ A. The predecessor is literally
g-inverse*y (as an element of the subgroup Γ[A]). -/
theorem localLeftCoset_translate_exists_unique
    (gen : ι → Γ)
    (A D : Finset ι) (hDA : D ⊆ A)
    (g : Γ) (x : generatedSubgroup gen A) (y : Γ)
    (hy : y ∈ generatedLeftCoset gen D (g * (x : Γ))) :
    ∃! z : generatedSubgroup gen A,
      z ∈ generatedLeftCoset
        (trivialCompletionGenerator gen A) D x ∧
      g * (z : Γ) = y := by
  have hD :
      (g * (x : Γ))⁻¹ * y ∈ generatedSubgroup gen D := hy
  have hA :
      (g * (x : Γ))⁻¹ * y ∈ generatedSubgroup gen A :=
    generatedSubgroup_mono gen hDA hD
  have hmember : g⁻¹ * y ∈ generatedSubgroup gen A := by
    have heq :
        g⁻¹ * y = (x : Γ) * ((g * (x : Γ))⁻¹ * y) := by group
    rw [heq]
    exact Subgroup.mul_mem _ x.2 hA
  let z : generatedSubgroup gen A := ⟨g⁻¹ * y, hmember⟩
  have hzValue : g * (z : Γ) = y := by
    dsimp [z]
    group
  have hzCoset :
      z ∈ generatedLeftCoset
        (trivialCompletionGenerator gen A) D x := by
    apply (localLeftCoset_translate_iff gen A D hDA g x z).mpr
    simpa only [hzValue] using hy
  refine ⟨z, ⟨hzCoset, hzValue⟩, ?_⟩
  intro w hw
  apply Subtype.ext
  exact mul_left_cancel (hw.2.trans hzValue.symm)

end ABO
end PSTSEPPA
