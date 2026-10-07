import PSTSEPPA.ABO.Transition

/-!
# Complete action graphs

Every family of permutations gives a complete ABO `E`-graph.  This is the
concrete model underlying transition groups and later Cayley graphs.

The construction deliberately makes no faithfulness assumption: two labels
may induce the same permutation and a generator may be the identity.
-/

namespace PSTSEPPA
namespace ABO

/-- Permutation attached to a signed label. -/
def signedPerm {V ι : Type*} (gen : ι → Equiv.Perm V) :
    SignedLabel ι → Equiv.Perm V
  | .pos i => gen i
  | .neg i => (gen i).symm

namespace signedPerm

variable {V ι : Type*} (gen : ι → Equiv.Perm V)

@[simp]
theorem pos (i : ι) :
    signedPerm gen (.pos i) = gen i :=
  rfl

@[simp]
theorem neg (i : ι) :
    signedPerm gen (.neg i) = (gen i).symm :=
  rfl

@[simp]
theorem inv (s : SignedLabel ι) :
    signedPerm gen (PSTS.SignedLetter.inv s) =
      (signedPerm gen s).symm := by
  cases s <;> rfl

end signedPerm

/-- Directed edge tokens of the action graph. -/
abbrev ActionEdge (V ι : Type*) :=
  V × SignedLabel ι

/-- Complete labelled action graph associated with a family of permutations. -/
noncomputable def actionGraph {V ι : Type*}
    (gen : ι → Equiv.Perm V) :
    CompleteEGraph V (ActionEdge V ι) ι where
  source e := e.1
  inv e :=
    (signedPerm gen e.2 e.1, PSTS.SignedLetter.inv e.2)
  inv_inv := by
    rintro ⟨u, s⟩
    cases s with
    | pos i =>
        simp [signedPerm, PSTS.SignedLetter.inv]
    | neg i =>
        simp [signedPerm, PSTS.SignedLetter.inv]
  inv_ne := by
    rintro ⟨u, s⟩
    cases s <;> simp [PSTS.SignedLetter.inv]
  label e := e.2
  label_inv := by
    rintro ⟨u, s⟩
    rfl
  deterministic := by
    rintro ⟨u, s⟩ ⟨v, t⟩ huv hst
    dsimp at huv hst
    subst v
    subst t
    rfl
  complete := by
    intro u s
    exact ⟨(u, s), rfl, rfl⟩

namespace actionGraph

variable {V ι : Type*} (gen : ι → Equiv.Perm V)

@[simp]
theorem source (u : V) (s : SignedLabel ι) :
    (actionGraph gen).source (u, s) = u :=
  rfl

@[simp]
theorem label (u : V) (s : SignedLabel ι) :
    (actionGraph gen).label (u, s) = s :=
  rfl

@[simp]
theorem edgeAt (u : V) (s : SignedLabel ι) :
    (actionGraph gen).edgeAt u s = (u, s) := by
  apply (actionGraph gen).edgeAt_eq
  · rfl
  · rfl

@[simp]
theorem target (u : V) (s : SignedLabel ι) :
    (actionGraph gen).target (u, s) = signedPerm gen s u :=
  rfl

@[simp]
theorem letterPerm (s : SignedLabel ι) :
    (actionGraph gen).letterPerm s = signedPerm gen s := by
  apply Equiv.ext
  intro u
  rw [CompleteEGraph.letterPerm_apply, edgeAt, target]

/-- The positive transition generator is exactly the supplied permutation,
viewed in the opposite permutation group. -/
@[simp]
theorem transitionGenerator (i : ι) :
    (actionGraph gen).transitionGenerator i =
      MulOpposite.op (gen i) := by
  unfold CompleteEGraph.transitionGenerator
  rw [letterPerm]

/-- The action graph remembers the supplied generators even when they are
non-faithful or trivial. -/
theorem transitionGroup_eq :
    (actionGraph gen).transitionGroup =
      Subgroup.closure (Set.range fun i => MulOpposite.op (gen i)) := by
  unfold CompleteEGraph.transitionGroup
  congr 1
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, transitionGenerator gen i⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, (transitionGenerator gen i).symm⟩

end actionGraph

end ABO
end PSTSEPPA
