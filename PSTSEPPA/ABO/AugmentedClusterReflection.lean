import PSTSEPPA.ABO.AugmentedCluster
import PSTSEPPA.ABO.Stability

/-!
# Reflection across attached cosets

This file isolates the algebraic core needed for ABO Lemma 3.14.

A stable labelled quotient is injective on every stable left subalphabet
coset.  More importantly, if a vertex of a cluster maps into the B-coset of
another cluster vertex, then it already lies in that B-coset upstairs,
provided the quotient is stable on the cluster constituents and the target
labelled group is retractable.

The latter statement is the cross-piece argument needed to prove that the
literal union defining an augmented cluster is transported injectively.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}

namespace LabelledGroupQuotient

variable (Q : LabelledGroupQuotient genΓ genΔ)

/-- Labelled quotients send left subalphabet cosets into the corresponding
left subalphabet cosets. -/
theorem hom_mem_generatedLeftCoset
    (B : Finset ι) {v x : Γ}
    (hx : x ∈ generatedLeftCoset genΓ B v) :
    Q.hom x ∈ generatedLeftCoset genΔ B (Q.hom v) := by
  change v⁻¹ * x ∈ generatedSubgroup genΓ B at hx
  change (Q.hom v)⁻¹ * Q.hom x ∈ generatedSubgroup genΔ B
  have himage :
      Q.hom (v⁻¹ * x) ∈ generatedSubgroup genΔ B :=
    Q.hom_mem_generatedSubgroup B hx
  simpa using himage

/-- Stability at B makes the ambient quotient injective on every left
B-coset. -/
theorem hom_injective_on_generatedLeftCoset
    (B : Finset ι) (hB : Q.StableAt B)
    {v x y : Γ}
    (hx : x ∈ generatedLeftCoset genΓ B v)
    (hy : y ∈ generatedLeftCoset genΓ B v)
    (hxy : Q.hom x = Q.hom y) :
    x = y := by
  have hxB :
      v⁻¹ * x ∈ generatedSubgroup genΓ B :=
    hx
  have hyB :
      v⁻¹ * y ∈ generatedSubgroup genΓ B :=
    hy
  have hsub :
      Q.subgroupHom B ⟨v⁻¹ * x, hxB⟩ =
        Q.subgroupHom B ⟨v⁻¹ * y, hyB⟩ := by
    apply Subtype.ext
    change Q.hom (v⁻¹ * x) = Q.hom (v⁻¹ * y)
    simp [hxy]
  have hstep :
      v⁻¹ * x = v⁻¹ * y :=
    congrArg Subtype.val (hB hsub)
  have hmul := congrArg (fun t : Γ => v * t) hstep
  simpa [mul_assoc] using hmul

/-- Cross-piece reflection for augmented clusters.

Suppose v and x are vertices of the same cluster and the image of x belongs
to the B-coset of the image of v.  If the target labelled group is
retractable and the quotient is stable on every constituent alphabet, then x
already belongs to v G[B] upstairs.

This is the only non-formal overlap argument needed when gluing the same
B-coset to corresponding clusters. -/
theorem hom_reflects_generatedLeftCoset_on_cluster
    {A : Finset ι} (P : ClusterSpec A)
    (hgenΔ : IsGenerated genΔ) (hretΔ : Retractable genΔ)
    (hstable :
      ∀ C ∈ P.pieces, Q.StableAt C)
    {B : Finset ι} {v x : Γ}
    (hv : v ∈ P.VertexSet genΓ)
    (hx : x ∈ P.VertexSet genΓ)
    (hxImage :
      Q.hom x ∈ generatedLeftCoset genΔ B (Q.hom v)) :
    x ∈ generatedLeftCoset genΓ B v := by
  rcases hv with ⟨D, hDP, hvD⟩
  rcases hx with ⟨C, hCP, hxC⟩

  let r : Δ :=
    cosetCoreProjection genΔ hgenΔ hretΔ B (Q.hom v)

  have hrB :
      r ∈ generatedLeftCoset genΔ B (Q.hom v) := by
    dsimp [r]
    exact
      cosetCoreProjection_mem_self_coset
        genΔ hgenΔ hretΔ B (Q.hom v)

  have hQvD :
      Q.hom v ∈ generatedSubgroup genΔ D :=
    Q.hom_mem_generatedSubgroup D hvD
  have hQxC :
      Q.hom x ∈ generatedSubgroup genΔ C :=
    Q.hom_mem_generatedSubgroup C hxC

  have hrD :
      r ∈ generatedSubgroup genΔ D := by
    dsimp [r]
    exact
      cosetCoreProjection_mem_generatedSubgroup
        genΔ hgenΔ hretΔ B D hQvD

  have hprojX :
      cosetCoreProjection genΔ hgenΔ hretΔ B (Q.hom x) ∈
        generatedSubgroup genΔ C :=
    cosetCoreProjection_mem_generatedSubgroup
      genΔ hgenΔ hretΔ B C hQxC

  have hprojEq :
      r =
        cosetCoreProjection genΔ hgenΔ hretΔ B (Q.hom x) := by
    dsimp [r]
    exact
      cosetCoreProjection_eq_of_mem_coset
        genΔ hgenΔ hretΔ B hxImage

  have hrC :
      r ∈ generatedSubgroup genΔ C := by
    rw [hprojEq]
    exact hprojX

  have hrCD :
      r ∈ generatedSubgroup genΔ (C ∩ D) := by
    rw [← generatedSubgroup_inf genΔ hgenΔ hretΔ C D]
    exact ⟨hrC, hrD⟩

  rcases Q.exists_subgroup_preimage (C ∩ D) hrCD with
    ⟨z, hzCD, hzMap⟩

  have hzC :
      z ∈ generatedSubgroup genΓ C :=
    generatedSubgroup_mono genΓ
      (by
        intro i hi
        exact (Finset.mem_inter.mp hi).1)
      hzCD
  have hzD :
      z ∈ generatedSubgroup genΓ D :=
    generatedSubgroup_mono genΓ
      (by
        intro i hi
        exact (Finset.mem_inter.mp hi).2)
      hzCD

  have hdB :
      (Q.hom v)⁻¹ * r ∈ generatedSubgroup genΔ B :=
    hrB
  have hdD :
      (Q.hom v)⁻¹ * r ∈ generatedSubgroup genΔ D :=
    (generatedSubgroup genΔ D).mul_mem
      ((generatedSubgroup genΔ D).inv_mem hQvD) hrD
  have hdBD :
      (Q.hom v)⁻¹ * r ∈ generatedSubgroup genΔ (B ∩ D) := by
    rw [← generatedSubgroup_inf genΔ hgenΔ hretΔ B D]
    exact ⟨hdB, hdD⟩

  rcases Q.exists_subgroup_preimage (B ∩ D) hdBD with
    ⟨b, hbBD, hbMap⟩

  have hbB :
      b ∈ generatedSubgroup genΓ B :=
    generatedSubgroup_mono genΓ
      (by
        intro i hi
        exact (Finset.mem_inter.mp hi).1)
      hbBD
  have hbD :
      b ∈ generatedSubgroup genΓ D :=
    generatedSubgroup_mono genΓ
      (by
        intro i hi
        exact (Finset.mem_inter.mp hi).2)
      hbBD
  have hvbD :
      v * b ∈ generatedSubgroup genΓ D :=
    (generatedSubgroup genΓ D).mul_mem hvD hbD
  have hvbMap :
      Q.hom (v * b) = r := by
    calc
      Q.hom (v * b) = Q.hom v * Q.hom b := by
        exact map_mul Q.hom v b
      _ = Q.hom v * ((Q.hom v)⁻¹ * r) := by
        rw [hbMap]
      _ = r := by simp [mul_assoc]

  have hzbSub :
      Q.subgroupHom D ⟨z, hzD⟩ =
        Q.subgroupHom D ⟨v * b, hvbD⟩ := by
    apply Subtype.ext
    change Q.hom z = Q.hom (v * b)
    exact hzMap.trans hvbMap.symm

  have hzb :
      z = v * b :=
    congrArg Subtype.val ((hstable D hDP) hzbSub)

  have hzBcoset :
      z ∈ generatedLeftCoset genΓ B v := by
    change v⁻¹ * z ∈ generatedSubgroup genΓ B
    rw [hzb]
    simpa [mul_assoc] using hbB

  have htargetCosetEq :
      generatedLeftCoset genΔ B (Q.hom v) =
        generatedLeftCoset genΔ B r :=
    generatedLeftCoset_eq_of_mem genΔ B hrB
  have hQxFromR :
      Q.hom x ∈ generatedLeftCoset genΔ B r := by
    rw [← htargetCosetEq]
    exact hxImage

  have heB :
      r⁻¹ * Q.hom x ∈ generatedSubgroup genΔ B :=
    hQxFromR
  have heC :
      r⁻¹ * Q.hom x ∈ generatedSubgroup genΔ C :=
    (generatedSubgroup genΔ C).mul_mem
      ((generatedSubgroup genΔ C).inv_mem hrC) hQxC
  have heBC :
      r⁻¹ * Q.hom x ∈ generatedSubgroup genΔ (B ∩ C) := by
    rw [← generatedSubgroup_inf genΔ hgenΔ hretΔ B C]
    exact ⟨heB, heC⟩

  rcases Q.exists_subgroup_preimage (B ∩ C) heBC with
    ⟨c, hcBC, hcMap⟩

  have hcB :
      c ∈ generatedSubgroup genΓ B :=
    generatedSubgroup_mono genΓ
      (by
        intro i hi
        exact (Finset.mem_inter.mp hi).1)
      hcBC
  have hcC :
      c ∈ generatedSubgroup genΓ C :=
    generatedSubgroup_mono genΓ
      (by
        intro i hi
        exact (Finset.mem_inter.mp hi).2)
      hcBC
  have hzcC :
      z * c ∈ generatedSubgroup genΓ C :=
    (generatedSubgroup genΓ C).mul_mem hzC hcC
  have hzcMap :
      Q.hom (z * c) = Q.hom x := by
    calc
      Q.hom (z * c) = Q.hom z * Q.hom c := by
        exact map_mul Q.hom z c
      _ = r * (r⁻¹ * Q.hom x) := by
        rw [hzMap, hcMap]
      _ = Q.hom x := by simp [mul_assoc]

  have hzcSub :
      Q.subgroupHom C ⟨z * c, hzcC⟩ =
        Q.subgroupHom C ⟨x, hxC⟩ := by
    apply Subtype.ext
    exact hzcMap

  have hzc :
      z * c = x :=
    congrArg Subtype.val ((hstable C hCP) hzcSub)

  change v⁻¹ * x ∈ generatedSubgroup genΓ B
  rw [← hzc]
  have hzStep :
      v⁻¹ * z ∈ generatedSubgroup genΓ B :=
    hzBcoset
  have hmul :=
    (generatedSubgroup genΓ B).mul_mem hzStep hcB
  simpa [mul_assoc] using hmul

end LabelledGroupQuotient

end ABO
end PSTSEPPA
