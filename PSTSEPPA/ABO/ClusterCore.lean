import PSTSEPPA.ABO.CosetConnectivity

/-!
# Common cores for cluster constituents

This file isolates the retractability argument behind ABO Lemma 3.11.

For a fixed subalphabet B, the retraction onto G[B] yields a canonical
projection
  pi_B(x) = x * psi_B(x)^{-1}.
It is constant on every left B-coset.  Moreover, if x lies in G[C], then
pi_B(x) also lies in G[C].  Hence every subgroup G[C] meeting a fixed
B-coset contains the same canonical point of that coset.  This immediately
gives the common-intersection statement used in the cluster analysis.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Canonical point associated with x and the B-retraction. -/
noncomputable def cosetCoreProjection
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (x : Γ) : Γ :=
  x *
    (((retractHom gen hgen hret B x :
        generatedSubgroup gen B) : Γ))⁻¹

/-- The canonical projection stays in the B-coset of x. -/
theorem cosetCoreProjection_mem_self_coset
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (x : Γ) :
    cosetCoreProjection gen hgen hret B x ∈
      generatedLeftCoset gen B x := by
  change
    x⁻¹ *
        (x *
          (((retractHom gen hgen hret B x :
              generatedSubgroup gen B) : Γ))⁻¹) ∈
      generatedSubgroup gen B
  have hinv :
      (((retractHom gen hgen hret B x :
          generatedSubgroup gen B) : Γ))⁻¹ ∈
        generatedSubgroup gen B :=
    (generatedSubgroup gen B).inv_mem
      (retractHom gen hgen hret B x).property
  simpa [mul_assoc] using hinv

/-- If x lies in G[C], its B-core projection still lies in G[C]. -/
theorem cosetCoreProjection_mem_generatedSubgroup
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) {x : Γ}
    (hx : x ∈ generatedSubgroup gen C) :
    cosetCoreProjection gen hgen hret B x ∈
      generatedSubgroup gen C := by
  have himageInter :=
    retractHom_generatedSubgroup_mem_inter
      gen hgen hret C B hx
  have himageC :
      ((retractHom gen hgen hret B x :
          generatedSubgroup gen B) : Γ) ∈
        generatedSubgroup gen C := by
    apply generatedSubgroup_mono gen
      (show C ∩ B ⊆ C by
        intro i hi
        exact (Finset.mem_inter.mp hi).1)
    exact himageInter
  exact
    (generatedSubgroup gen C).mul_mem hx
      ((generatedSubgroup gen C).inv_mem himageC)

/-- The B-core projection is constant on each left B-coset. -/
theorem cosetCoreProjection_eq_of_mem_coset
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) {x y : Γ}
    (hy : y ∈ generatedLeftCoset gen B x) :
    cosetCoreProjection gen hgen hret B x =
      cosetCoreProjection gen hgen hret B y := by
  have hb : x⁻¹ * y ∈ generatedSubgroup gen B := hy
  have hyEq : y = x * (x⁻¹ * y) := by
    simp [mul_assoc]
  have hfix :
      retractHom gen hgen hret B (x⁻¹ * y) =
        (⟨x⁻¹ * y, hb⟩ : generatedSubgroup gen B) :=
    retractHom_on_generatedSubgroup
      gen hgen hret B ⟨x⁻¹ * y, hb⟩
  unfold cosetCoreProjection
  rw [hyEq]
  have hmul :
      retractHom gen hgen hret B (x * (x⁻¹ * y)) =
        retractHom gen hgen hret B x *
          retractHom gen hgen hret B (x⁻¹ * y) := by
    exact map_mul (retractHom gen hgen hret B) x (x⁻¹ * y)
  rw [hmul, hfix]
  simp [mul_assoc]

/-- If G[C] meets the left B-coset of v, the canonical B-core point of v
lies in G[C]. -/
theorem cosetCoreProjection_mem_of_subgroup_meets_coset
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (v : Γ)
    (hne :
      ((generatedSubgroup gen C : Set Γ) ∩
        generatedLeftCoset gen B v).Nonempty) :
    cosetCoreProjection gen hgen hret B v ∈
      generatedSubgroup gen C := by
  rcases hne with ⟨u, huC, huB⟩
  have huProj :
      cosetCoreProjection gen hgen hret B u ∈
        generatedSubgroup gen C :=
    cosetCoreProjection_mem_generatedSubgroup
      gen hgen hret B C huC
  have heq :
      cosetCoreProjection gen hgen hret B v =
        cosetCoreProjection gen hgen hret B u :=
    cosetCoreProjection_eq_of_mem_coset
      gen hgen hret B huB
  rwa [heq]

/-- ABO Lemma 3.11, in finite-family form.

If every constituent subgroup G[C], C in P, meets the same left B-coset
v G[B], then all of them have a common point in that coset. -/
theorem subgroup_family_inter_coset_nonempty
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : Finset (Finset ι)) (B : Finset ι) (v : Γ)
    (hmeet :
      ∀ C ∈ P,
        ((generatedSubgroup gen C : Set Γ) ∩
          generatedLeftCoset gen B v).Nonempty) :
    ∃ z : Γ,
      z ∈ generatedLeftCoset gen B v ∧
      ∀ C ∈ P, z ∈ generatedSubgroup gen C := by
  let z := cosetCoreProjection gen hgen hret B v
  refine ⟨z, ?_, ?_⟩
  · exact
      cosetCoreProjection_mem_self_coset
        gen hgen hret B v
  · intro C hCP
    exact
      cosetCoreProjection_mem_of_subgroup_meets_coset
        gen hgen hret B C v (hmeet C hCP)

end ABO
end PSTSEPPA
