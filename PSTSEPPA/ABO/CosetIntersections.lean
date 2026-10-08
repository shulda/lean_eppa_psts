import PSTSEPPA.ABO.SubgroupIntersections

/-!
# Coset intersections in retractable labelled groups

Because Cayley edges multiply labelled generators on the right, subalphabet
components are left cosets `g G[A]` (fixed representative on the left).

For a retractable generated labelled group, every nonempty intersection of
two such cosets is exactly a coset over the intersection alphabet.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- The left coset `g G[A]`, written as a vertex set. -/
def generatedLeftCoset (gen : ι → Γ) (A : Finset ι) (g : Γ) : Set Γ :=
  {x | g⁻¹ * x ∈ generatedSubgroup gen A}

@[simp]
theorem mem_generatedLeftCoset
    (gen : ι → Γ) (A : Finset ι) (g x : Γ) :
    x ∈ generatedLeftCoset gen A g ↔
      g⁻¹ * x ∈ generatedSubgroup gen A :=
  Iff.rfl

@[simp]
theorem self_mem_generatedLeftCoset
    (gen : ι → Γ) (A : Finset ι) (g : Γ) :
    g ∈ generatedLeftCoset gen A g := by
  simp [generatedLeftCoset]

/-- Any point of a left coset may be used as its representative. -/
theorem generatedLeftCoset_eq_of_mem
    (gen : ι → Γ) (A : Finset ι) {g z : Γ}
    (hz : z ∈ generatedLeftCoset gen A g) :
    generatedLeftCoset gen A g = generatedLeftCoset gen A z := by
  ext x
  constructor
  · intro hx
    change g⁻¹ * x ∈ generatedSubgroup gen A at hx
    change g⁻¹ * z ∈ generatedSubgroup gen A at hz
    change z⁻¹ * x ∈ generatedSubgroup gen A
    have hinv :
        (g⁻¹ * z)⁻¹ ∈ generatedSubgroup gen A :=
      (generatedSubgroup gen A).inv_mem hz
    have hmul :=
      (generatedSubgroup gen A).mul_mem hinv hx
    simpa [mul_assoc] using hmul
  · intro hx
    change z⁻¹ * x ∈ generatedSubgroup gen A at hx
    change g⁻¹ * z ∈ generatedSubgroup gen A at hz
    change g⁻¹ * x ∈ generatedSubgroup gen A
    have hmul :=
      (generatedSubgroup gen A).mul_mem hz hx
    simpa [mul_assoc] using hmul

/-- Exact intersection formula, based at any chosen common point. -/
theorem generatedLeftCoset_inter
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (A B : Finset ι) (g h z : Γ)
    (hzA : z ∈ generatedLeftCoset gen A g)
    (hzB : z ∈ generatedLeftCoset gen B h) :
    generatedLeftCoset gen A g ∩ generatedLeftCoset gen B h =
      generatedLeftCoset gen (A ∩ B) z := by
  rw [generatedLeftCoset_eq_of_mem gen A hzA,
    generatedLeftCoset_eq_of_mem gen B hzB]
  ext x
  constructor
  · rintro ⟨hxA, hxB⟩
    change z⁻¹ * x ∈ generatedSubgroup gen A at hxA
    change z⁻¹ * x ∈ generatedSubgroup gen B at hxB
    change z⁻¹ * x ∈ generatedSubgroup gen (A ∩ B)
    have hInf :
        z⁻¹ * x ∈
          generatedSubgroup gen A ⊓ generatedSubgroup gen B :=
      ⟨hxA, hxB⟩
    rwa [generatedSubgroup_inf gen hgen hret A B] at hInf
  · intro hx
    change z⁻¹ * x ∈ generatedSubgroup gen (A ∩ B) at hx
    have hInf :
        z⁻¹ * x ∈
          generatedSubgroup gen A ⊓ generatedSubgroup gen B := by
      rwa [generatedSubgroup_inf gen hgen hret A B]
    exact ⟨hInf.1, hInf.2⟩

/-- Every nonempty intersection of subalphabet cosets is a coset over the
intersection alphabet. -/
theorem generatedLeftCoset_inter_of_nonempty
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (A B : Finset ι) (g h : Γ)
    (hne :
      (generatedLeftCoset gen A g ∩
        generatedLeftCoset gen B h).Nonempty) :
    ∃ z : Γ,
      z ∈ generatedLeftCoset gen A g ∩ generatedLeftCoset gen B h ∧
      generatedLeftCoset gen A g ∩ generatedLeftCoset gen B h =
        generatedLeftCoset gen (A ∩ B) z := by
  rcases hne with ⟨z, hzA, hzB⟩
  exact
    ⟨z, ⟨hzA, hzB⟩,
      generatedLeftCoset_inter gen hgen hret A B g h z hzA hzB⟩

end ABO
end PSTSEPPA
