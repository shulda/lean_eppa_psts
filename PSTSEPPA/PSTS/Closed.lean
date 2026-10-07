import PSTSEPPA.PSTS.Basic
import Mathlib.Data.Set.Lattice.Indexed

/-!
# Closed substructures of a partial Steiner triple system

Closedness is part of the category in which EPPA is proved: whenever two
vertices of the subset have a defined ambient operation value, that value must
also lie in the subset.
-/

namespace PSTSEPPA
namespace PSTS

variable {V : Type*}

/-- A subset is closed if it contains every ambient operation value of pairs of
its elements. -/
def Closed (A : PSTS V) (S : Set V) : Prop :=
  ∀ ⦃x y z⦄, x ∈ S → y ∈ S → A.op x y = some z → z ∈ S

@[simp]
theorem closed_empty (A : PSTS V) : A.Closed (∅ : Set V) := by
  intro x y z hx
  simp at hx

@[simp]
theorem closed_univ (A : PSTS V) : A.Closed (Set.univ : Set V) := by
  intro x y z hx hy hxy
  trivial

/-- Every singleton is a closed substructure. -/
@[simp]
theorem closed_singleton (A : PSTS V) (a : V) : A.Closed ({a} : Set V) := by
  intro x y z hx hy hxy
  simp only [Set.mem_singleton_iff] at hx hy ⊢
  subst x
  subst y
  exact (Option.some.inj ((A.diag a).symm.trans hxy)).symm

theorem Closed.inter {A : PSTS V} {S T : Set V} (hS : A.Closed S) (hT : A.Closed T) :
    A.Closed (S ∩ T) := by
  intro x y z hx hy hxy
  exact ⟨hS hx.1 hy.1 hxy, hT hx.2 hy.2 hxy⟩

theorem closed_iInter {A : PSTS V} {ι : Sort*} {S : ι → Set V}
    (hS : ∀ i, A.Closed (S i)) : A.Closed (⋂ i, S i) := by
  intro x y z hx hy hxy
  simp only [Set.mem_iInter] at hx hy ⊢
  intro i
  exact hS i (hx i) (hy i) hxy

/-- The partial operation induced on a closed subtype. -/
def restrictOp {A : PSTS V} {S : Set V} (hS : A.Closed S) (x y : S) : Option S :=
  match hxy : A.op x.1 y.1 with
  | none => none
  | some z => some ⟨z, hS x.2 y.2 hxy⟩

@[simp]
theorem restrictOp_eq_some_iff {A : PSTS V} {S : Set V} (hS : A.Closed S)
    (x y z : S) :
    restrictOp hS x y = some z ↔ A.op x.1 y.1 = some z.1 := by
  unfold restrictOp
  split
  · rename_i heq
    simp [heq]
  · rename_i z' heq
    constructor
    · intro h
      have hzsub : (⟨z', hS x.2 y.2 heq⟩ : S) = z := Option.some.inj h
      have hzval : z' = z.1 := congrArg Subtype.val hzsub
      exact heq.trans (congrArg some hzval)
    · intro h
      have hzval : z' = z.1 := Option.some.inj (heq.symm.trans h)
      have hzsub : (⟨z', hS x.2 y.2 heq⟩ : S) = z := Subtype.ext hzval
      exact congrArg some hzsub

@[simp]
theorem restrictOp_eq_none_iff {A : PSTS V} {S : Set V} (hS : A.Closed S)
    (x y : S) :
    restrictOp hS x y = none ↔ A.op x.1 y.1 = none := by
  unfold restrictOp
  split <;> simp_all

/-- The PSTS induced on a closed subset. -/
def induced (A : PSTS V) {S : Set V} (hS : A.Closed S) : PSTS S where
  op := restrictOp hS
  diag x := (restrictOp_eq_some_iff hS x x x).2 (A.diag x.1)
  symm x y := by
    apply Option.ext
    intro z
    rw [restrictOp_eq_some_iff, restrictOp_eq_some_iff, A.symm x.1 y.1]
  steiner_left := by
    intro x y z hxyz
    apply (restrictOp_eq_some_iff hS x z y).2
    apply A.steiner_left
    exact (restrictOp_eq_some_iff hS x y z).1 hxyz

end PSTS
end PSTSEPPA
