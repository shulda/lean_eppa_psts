import PSTSEPPA.PSTS.TotalPermutationLifts
import Mathlib.Logic.Equiv.Fintype

/-!
# Every finite partial permutation has a total permutation extension

The Cayley/MAX stage of the audited PSTS EPPA proof begins by choosing
a total permutation extending every selected partial PSTS automorphism.
This is an ELEMENTARY finite bijection extension and does not involve
ABO, F-inverse monoids or content-reduction.

We make this existence obligation explicit and discharge it:

* Regard the domain of a partial equivalence as a finite subtype.
* Map each domain point to itself and to its unique partial image.
* Both maps are injective, since a PEquiv has an inverse.
* Use mathlib's finite
  Equiv.Perm.exists_extending_pair
  on those two embeddings.

Consequently ANY selected alphabet of partial automorphisms of a
finite PSTS admits simultaneous chosen total permutation lifts.
Those lifts need not preserve the PSTS operation on all points:
their only purpose is to define the auxiliary finite Q and its
Cayley graph. Formal inverse letters are evaluated by inverse
permutations, as proved in TotalPermutationLifts.lean.
-/

namespace PSTSEPPA
namespace PSTS

variable {V ι : Type*}

/-- A value of a partial bijection at a point where it is defined,
chosen from the actual Option.some witness. -/
private noncomputable def partialImage
    (p : V ≃. V)
    (x : {x : V // ∃ y : V, p x = some y}) : V :=
  Classical.choose x.2

private theorem partialImage_spec
    (p : V ≃. V)
    (x : {x : V // ∃ y : V, p x = some y}) :
    p x.1 = some (partialImage p x) :=
  Classical.choose_spec x.2

/-- Every partial bijection of a finite carrier extends to an actual
total permutation. The extension is specified at EVERY point of
its domain, including empty and singleton domains. -/
theorem exists_total_permutation_extending
    [Finite V] (p : V ≃. V) :
    ∃ σ : Equiv.Perm V,
      ∀ {x y : V}, p x = some y → σ x = y := by
  classical
  let D := {x : V // ∃ y : V, p x = some y}
  let f : D → V := Subtype.val
  let g : D → V := fun x => partialImage p x
  have hf : Function.Injective f := Subtype.val_injective
  have hg : Function.Injective g := by
    intro a b hab
    have ha : p a.1 = some (g a) :=
      partialImage_spec p a
    have hb : p b.1 = some (g b) :=
      partialImage_spec p b
    have hsa : p.symm (g a) = some a.1 :=
      (p.eq_some_iff).mpr ha
    have hsb : p.symm (g b) = some b.1 :=
      (p.eq_some_iff).mpr hb
    rw [hab] at hsa
    have habval : a.1 = b.1 :=
      Option.some.inj (hsa.symm.trans hsb)
    exact Subtype.ext habval
  obtain ⟨σ, hσ⟩ :=
    Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_⟩
  intro x y hxy
  let dx : D := ⟨x, ⟨y, hxy⟩⟩
  have hd : p x = some (g dx) :=
    partialImage_spec p dx
  have heq : y = g dx :=
    Option.some.inj (hxy.symm.trans hd)
  exact (hσ dx).trans heq.symm

/-- Choose a concrete total permutation extending a finite partial
bijection. This is a choice in a finite nonempty set, not an axiom. -/
noncomputable def extendFinitePEquiv
    [Finite V] (p : V ≃. V) : Equiv.Perm V :=
  Classical.choose (exists_total_permutation_extending p)

theorem extendFinitePEquiv_agrees
    [Finite V] (p : V ≃. V) {x y : V}
    (hxy : p x = some y) :
    extendFinitePEquiv p x = y :=
  (Classical.choose_spec (exists_total_permutation_extending p)) hxy

/-- Simultaneously choose total permutation extensions of all
selected partial PSTS automorphisms, ready for the finite Cayley
group construction. No finite-generator or closedness assumption
beyond PartialAut itself is needed here. -/
noncomputable def finiteTotalPermutationLifts
    [Finite V] (A : PSTS V)
    (gen : ι → PartialAut A) :
    TotalPermutationLifts A gen where
  perm i := extendFinitePEquiv (gen i).toPEquiv
  agrees := by
    intro i x y hxy
    exact extendFinitePEquiv_agrees (gen i).toPEquiv hxy

end PSTS
end PSTSEPPA
