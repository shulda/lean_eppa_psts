import PSTSEPPA.ABO.Stability
import PSTSEPPA.ABO.CosetConnectivity

/-!
# Exact translated subgroup-coset fibres under k-stable labelled quotients

The corrected ABO Theorem 4.7 simultaneously involves a genuine
labelled quotient Q : G ↠ H, its k-stability on every proper
subalphabet B⊊A, and separately tagged B-coset constituents.

A stable Q restricts to an isomorphism G[B] ≃ H[B].
Here we strengthen this to every translated LEFT coset

    g * G[B]  ≃  Q(g) * H[B]

by the RESTRICTION of the actual quotient itself.
The map is injective on each chosen coset, surjective onto the
corresponding target coset, and carries group values exactly.
It does not identify distinct coset tags or assert injectivity
between DIFFERENT translated cosets. This distinction is
essential for the two-support collision argument in corrected
Theorem 4.7(ii).

No global retractability, group freeness, faithful generators,
or whole-group injectivity is assumed. k-stability only enters
to prove injectivity on the specified B-coset.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}

namespace LabelledGroupQuotient

variable (Q : LabelledGroupQuotient genΓ genΔ)

/-- Any labelled quotient sends a translated B-coset into
the same-labelled translated B-coset downstairs. This
direction needs no stability or whole-group surjectivity. -/
theorem map_mem_generatedLeftCoset
    (B : Finset ι) (g x : Γ)
    (hx : x ∈ generatedLeftCoset genΓ B g) :
    Q.hom x ∈ generatedLeftCoset genΔ B (Q.hom g) := by
  change (Q.hom g)⁻¹ * Q.hom x ∈ generatedSubgroup genΔ B
  simpa only [map_mul, map_inv] using
    (Q.hom_mem_generatedSubgroup B (x := g⁻¹ * x) hx)

/-- At a B-stable quotient, equal downstairs group
coordinates of two points of the SAME g G[B] coset
already imply equal original points. No such conclusion
is asserted for two DIFFERENT coset tags. -/
theorem injective_on_generatedLeftCoset_of_stableAt
    (B : Finset ι) (hB : Q.StableAt B) (g : Γ)
    {x y : Γ}
    (hx : x ∈ generatedLeftCoset genΓ B g)
    (hy : y ∈ generatedLeftCoset genΓ B g)
    (hxy : Q.hom x = Q.hom y) :
    x = y := by
  let sx : generatedSubgroup genΓ B := ⟨g⁻¹ * x, hx⟩
  let sy : generatedSubgroup genΓ B := ⟨g⁻¹ * y, hy⟩
  have hsub : Q.subgroupHom B sx = Q.subgroupHom B sy := by
    apply Subtype.ext
    change Q.hom (g⁻¹ * x) = Q.hom (g⁻¹ * y)
    calc
      Q.hom (g⁻¹ * x) = (Q.hom g)⁻¹ * Q.hom x := by
        rw [map_mul, map_inv]
      _ = (Q.hom g)⁻¹ * Q.hom y := congrArg _ hxy
      _ = Q.hom (g⁻¹ * y) := by
        rw [map_mul, map_inv]
  have hinj : g⁻¹ * x = g⁻¹ * y :=
    congrArg Subtype.val (hB hsub)
  exact mul_left_cancel hinj

/-- Every point of the downstairs translated B-coset
has an actual upstairs point in the corresponding
specified coset. It is NOT necessary to choose a
representative of any other component-tagged coset. -/
theorem exists_generatedLeftCoset_preimage
    (B : Finset ι) (g : Γ) (y : Δ)
    (hy : y ∈ generatedLeftCoset genΔ B (Q.hom g)) :
    ∃ x : Γ,
      x ∈ generatedLeftCoset genΓ B g ∧ Q.hom x = y := by
  obtain ⟨z, hzB, hz⟩ :=
    Q.exists_subgroup_preimage B
      (y := (Q.hom g)⁻¹ * y) hy
  refine ⟨g * z, ?_, ?_⟩
  · change g⁻¹ * (g * z) ∈ generatedSubgroup genΓ B
    simpa [mul_assoc] using hzB
  · calc
      Q.hom (g * z) = Q.hom g * Q.hom z := map_mul _ _ _
      _ = Q.hom g * ((Q.hom g)⁻¹ * y) :=
        congrArg (Q.hom g * ·) hz
      _ = y := by simp [mul_assoc]

/-- Exact translated left-coset bijection induced by the
actual group quotient, assuming stability only on B.
The source and target points REMAIN tagged with their
chosen coset predicates. -/
noncomputable def stableAt_leftCosetEquiv
    (B : Finset ι) (hB : Q.StableAt B) (g : Γ) :
    {x : Γ // x ∈ generatedLeftCoset genΓ B g} ≃
      {y : Δ // y ∈ generatedLeftCoset genΔ B (Q.hom g)} := by
  apply Equiv.ofBijective
    (fun x : {x : Γ // x ∈ generatedLeftCoset genΓ B g} =>
      (⟨Q.hom x.1, Q.map_mem_generatedLeftCoset B g x.1 x.2⟩ :
        {y : Δ // y ∈ generatedLeftCoset genΔ B (Q.hom g)}))
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact Q.injective_on_generatedLeftCoset_of_stableAt
      B hB g x.2 y.2 (congrArg Subtype.val hxy)
  · intro y
    obtain ⟨x, hx, hxy⟩ :=
      Q.exists_generatedLeftCoset_preimage B g y.1 y.2
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- The translated-coset equivalence has EXACT group-coordinate
map Q, including the chosen old coset representative g. -/
@[simp] theorem stableAt_leftCosetEquiv_apply
    (B : Finset ι) (hB : Q.StableAt B) (g : Γ)
    (x : {x : Γ // x ∈ generatedLeftCoset genΓ B g}) :
    (Q.stableAt_leftCosetEquiv B hB g x).1 = Q.hom x.1 :=
  rfl

/-- The whole family of proper cosets of rank at most k
has the exact individual translated coset bijection
under a k-stable quotient. It DOES NOT give a
global injection across DIFFERENT constituent tags. -/
noncomputable def kStable_leftCosetEquiv
    (k : ℕ) (hk : Q.KStable k)
    (B : Finset ι) (hB : B.card ≤ k) (g : Γ) :
    {x : Γ // x ∈ generatedLeftCoset genΓ B g} ≃
      {y : Δ // y ∈ generatedLeftCoset genΔ B (Q.hom g)} :=
  Q.stableAt_leftCosetEquiv B (hk B hB) g

end LabelledGroupQuotient
end ABO
end PSTSEPPA
