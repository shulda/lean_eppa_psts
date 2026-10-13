import PSTSEPPA.ABO.StageStabilityWordKernel
import PSTSEPPA.ABO.TransitionGroupGenerated

/-!
# Complete signed-word congruence is exactly the identity-word kernel

A genuine complete signed EGraph represents each signed label as a
permutation and each chronological word as a right-permutation.
For a generated source labelled group Γ, an exact stage action
factors through the Γ group value precisely when every Γ-trivial
signed word fixes EVERY stage vertex.

This reduces equality of arbitrary two signed word actions to the
single-word kernel test used throughout repaired ABO Proposition 5.4.
The equivalence includes negative letters, repeated or identity
generators, disconnected stages, and legal fixed-point loops.

It is a *generic logical bridge*; checking the required kernel
for all source Definition-5.3 Z₁ stages is a separate geometric
obligation. No bounded-rank identity kernel is silently promoted
to an unrestricted one.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)

/-- Full equality of signed word actions as soon as the group
word values coincide is equivalent to having every Γ-identity
signed word act as the identity ON EVERY stage vertex. -/
theorem fullWordActionCongr_iff_identityWordKernel
    (gen : ι → Γ) :
    (∀ (p q : LabelWord ι),
      PSTS.SignedWord.evalGroup gen p =
        PSTS.SignedWord.evalGroup gen q →
        ∀ x : V, T.followWord x p = T.followWord x q) ↔
    (∀ (w : LabelWord ι),
      PSTS.SignedWord.evalGroup gen w = 1 →
        ∀ x : V, T.followWord x w = x) := by
  constructor
  · intro h w hw x
    have hval :
        PSTS.SignedWord.evalGroup gen w =
        PSTS.SignedWord.evalGroup gen ([] : LabelWord ι) := by
      simpa using hw
    simpa using h w ([] : LabelWord ι) hval x
  · intro h p q hpq x
    let w : LabelWord ι := PSTS.SignedWord.inv p ++ q
    have hwval :
        PSTS.SignedWord.evalGroup gen w = 1 := by
      dsimp [w]
      rw [PSTS.SignedWord.evalGroup_append,
        PSTS.SignedWord.evalGroup_inv, hpq]
      simp
    have htrivial : T.wordValue w = 1 := by
      apply (T.wordValue_eq_one_iff_all_vertices_fixed w).mpr
      exact h w hwval
    have heq : T.wordValue p = T.wordValue q := by
      dsimp [w] at htrivial
      rw [T.wordValue_append, T.wordValue_inv] at htrivial
      exact inv_mul_eq_one.mp htrivial
    calc
      T.followWord x p = T.rightApply (T.wordValue p) x :=
        (T.rightApply_wordValue p x).symm
      _ = T.rightApply (T.wordValue q) x := by rw [heq]
      _ = T.followWord x q := T.rightApply_wordValue q x

end CompleteEGraph
end ABO
end PSTSEPPA
