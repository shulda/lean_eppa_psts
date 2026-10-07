import PSTSEPPA.PSTS.DevelopmentBase

/-!
# The ambient group action on the quotient development

Right multiplication in the finite group descends to automorphisms of the
quotient PSTS.  The distinguished lifts of the selected generators extend the
original partial automorphisms on the closed base copy.
-/

namespace PSTSEPPA
namespace PSTS

variable {V ι : Type*} {A : PSTS V} {gen : ι → PartialAut A}

namespace MaxTransporterExtension

variable (X : MaxTransporterExtension A gen)

/-- Right multiplication by `t` is an equivalence of the quotient. -/
def developmentRightEquiv (t : X.H) :
    X.Development ≃ X.Development where
  toFun q := X.developmentRight q t
  invFun q := X.developmentRight q t⁻¹
  left_inv q := by
    change X.developmentRight (X.developmentRight q t) t⁻¹ = q
    rw [X.developmentRight_mul]
    simp
  right_inv q := by
    change X.developmentRight (X.developmentRight q t⁻¹) t = q
    rw [X.developmentRight_mul]
    simp

@[simp]
theorem developmentRightEquiv_apply (t : X.H) (q : X.Development) :
    X.developmentRightEquiv t q = X.developmentRight q t :=
  rfl

/-- Common chart triples are stable under the right group action. -/
theorem developmentOpRel_right
    {x y z : X.Development}
    (h : X.DevelopmentOpRel x y z) (t : X.H) :
    X.DevelopmentOpRel
      (X.developmentRight x t)
      (X.developmentRight y t)
      (X.developmentRight z t) := by
  rcases h with ⟨a, b, c, g, hx, hy, hz, habc⟩
  subst x
  subst y
  subst z
  refine ⟨a, b, c, g * t, ?_, ?_, ?_, habc⟩ <;> rfl

/-- Defined operation values are carried to defined operation values by right
multiplication. -/
theorem developmentOp_right_of_eq_some
    {x y z : X.Development}
    (h : X.developmentPSTS.op x y = some z) (t : X.H) :
    X.developmentPSTS.op
        (X.developmentRight x t)
        (X.developmentRight y t) =
      some (X.developmentRight z t) := by
  apply X.developmentOp_eq_some_iff.mpr
  exact X.developmentOpRel_right
    (X.developmentOp_eq_some_iff.mp h) t

/-- Undefinedness is preserved by right multiplication. -/
theorem developmentOp_right_eq_none
    {x y : X.Development}
    (h : X.developmentPSTS.op x y = none) (t : X.H) :
    X.developmentPSTS.op
        (X.developmentRight x t)
        (X.developmentRight y t) = none := by
  cases hright :
      X.developmentPSTS.op
        (X.developmentRight x t)
        (X.developmentRight y t) with
  | none =>
      rfl
  | some z =>
      have hback :=
        X.developmentOp_right_of_eq_some hright t⁻¹
      have hback' :
          X.developmentPSTS.op x y =
            some (X.developmentRight z t⁻¹) := by
        simpa [X.developmentRight_mul] using hback
      rw [h] at hback'
      cases hback'

/-- Operation preservation in the exact `Option.bind` form required by
`PartialAut`. -/
theorem developmentRight_map_op (x y : X.Development) (t : X.H) :
    (X.developmentPSTS.op x y).bind
        (X.developmentRightEquiv t).toPEquiv =
      X.developmentPSTS.op
        (X.developmentRight x t)
        (X.developmentRight y t) := by
  cases hxy : X.developmentPSTS.op x y with
  | none =>
      have hr := X.developmentOp_right_eq_none hxy t
      simpa using hr.symm
  | some z =>
      have hr := X.developmentOp_right_of_eq_some hxy t
      rw [hr]
      exact Equiv.toPEquiv_apply (X.developmentRightEquiv t) z

/-- Right multiplication by any group element is a total partial automorphism,
hence an automorphism of the quotient PSTS. -/
def developmentRightAut (t : X.H) :
    PartialAut X.developmentPSTS where
  toPEquiv := (X.developmentRightEquiv t).toPEquiv
  source_closed := by
    have hs :
        PEquivSource (X.developmentRightEquiv t).toPEquiv =
          (Set.univ : Set X.Development) := by
      ext q
      simp [PEquivSource, Equiv.toPEquiv_apply]
    rw [hs]
    exact X.developmentPSTS.closed_univ
  target_closed := by
    have ht :
        PEquivTarget (X.developmentRightEquiv t).toPEquiv =
          (Set.univ : Set X.Development) := by
      ext q
      simp [PEquivTarget, PEquivSource, ← Equiv.toPEquiv_symm]
    rw [ht]
    exact X.developmentPSTS.closed_univ
  map_op := by
    intro x y x' y' hx hy
    simp only [Equiv.toPEquiv_apply, Option.some.injEq] at hx hy
    subst x'
    subst y'
    exact X.developmentRight_map_op x y t

/-- A distinguished group lift acts on the base copy exactly as the selected
partial automorphism wherever that partial automorphism is defined. -/
theorem developmentRight_liftGen_base
    (i : ι) {a b : V}
    (hab : (gen i).toPEquiv a = some b) :
    X.developmentRight (X.baseMap a) (X.liftGen i) =
      X.baseMap b := by
  change X.developmentMk a (1 * X.liftGen i) =
    X.developmentMk b 1
  rw [one_mul]
  apply Quotient.sound
  change DevelopmentGlue X (a, X.liftGen i) (b, 1)
  simpa using X.glue_pos i hab (1 : X.H)

/-- The total quotient automorphism associated to `liftGen i` extends
`gen i` on the canonical base copy. -/
theorem developmentRightAut_extends
    (i : ι) {a b : V}
    (hab : (gen i).toPEquiv a = some b) :
    (X.developmentRightAut (X.liftGen i)).toPEquiv
        (X.baseMap a) =
      some (X.baseMap b) := by
  change
    (X.developmentRightEquiv (X.liftGen i)).toPEquiv
        (X.baseMap a) =
      some (X.baseMap b)
  rw [Equiv.toPEquiv_apply]
  exact congrArg some (X.developmentRight_liftGen_base i hab)

end MaxTransporterExtension

end PSTS
end PSTSEPPA
