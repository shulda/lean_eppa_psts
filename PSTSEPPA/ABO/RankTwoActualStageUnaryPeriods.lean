import PSTSEPPA.ABO.RankTwoThreeFamilyStableCover
import PSTSEPPA.ABO.UnaryPeriodWordKernel

/-!
# True rank-two ABO completed stages preserve every singleton generator period

The human source audit proposes a bounded universal first-rank
permutation construction. Its crucial source-specific hypothesis is
that each generator of EVERY completed geometric stage has period
dividing its period in the original H1 group.

The existing Lean-certified rank-one kernel for the genuine
three-family rank-two augmented coset construction is actually
STRONGER than this period condition. This file proves the
connection on the real, tagged, completed graph, not on the
possibly noninjective ambient Cayley-coordinate map.

The result covers the assembled family consisting of:
* the true full proper-alphabet completed coset extension;
* all genuine anchored augmented type-(1) clusters;
* all genuine off-component singleton augmented type-(2) stages.

All positive and negative labelled paths are handled. Source
Definition-5.3 completeness (the full H1-cover family), an
explicit universal size bound and general higher ranks remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*} [Fintype ι] [DecidableEq ι]
variable [Group Γ]

namespace LabelWord

/-- A signed word consisting of n positive copies of the single
generator i. -/
def repeatPositive (i : ι) (n : ℕ) : LabelWord ι :=
  List.replicate n (.pos i)

/-- Its support is literally the singleton alphabet {i}. -/
theorem repeatPositive_uses (i : ι) (n : ℕ) :
    Uses ({i} : Finset ι) (repeatPositive i n) := by
  induction n with
  | zero =>
      trivial
  | succ n ih =>
      change i ∈ ({i} : Finset ι) ∧
        Uses ({i} : Finset ι) (repeatPositive i n)
      exact ⟨by simp, ih⟩

/-- Its group value is the actual nth power of i, with no
commutativity hypotheses on the ambient group. -/
theorem evalGroup_repeatPositive
    (gen : ι → Γ) (i : ι) (n : ℕ) :
    PSTS.SignedWord.evalGroup gen (repeatPositive i n) =
      (gen i) ^ n := by
  induction n with
  | zero =>
      simp [repeatPositive, PSTS.SignedWord.evalGroup]
  | succ n ih =>
      change gen i *
        PSTS.SignedWord.evalGroup gen (repeatPositive i n) =
        (gen i) ^ (n + 1)
      rw [ih, pow_succ']
end LabelWord

/-- Kernel control for every one-letter signed word implies the
exact generator period inequality for a complete stage:
if (gen i)^m=1 downstairs, then its ACTUAL completed-stage
transition subgroup generator also has mth power 1.

This works with m=0 and m=1 and does not need the ambient
group to be finite, generated, retractable or involutive. -/
theorem completeStage_generator_pow_of_rankOneKernel
    (gen : ι → Γ) (T : CompleteEGraph V Edge ι)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ 1 →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1)
    (i : ι) (m : ℕ)
    (hm : (gen i) ^ m = 1) :
    T.transitionSubgroupGenerator i ^ m = 1 := by
  let w : LabelWord ι := LabelWord.repeatPositive i m
  have hw : LabelWord.Uses ({i} : Finset ι) w :=
    LabelWord.repeatPositive_uses i m
  have heval : PSTS.SignedWord.evalGroup gen w = 1 := by
    change PSTS.SignedWord.evalGroup gen
      (LabelWord.repeatPositive i m) = 1
    rw [LabelWord.evalGroup_repeatPositive]
    exact hm
  have hstage : T.wordValue w = 1 :=
    hkernel ({i} : Finset ι) (by simp) w hw heval
  have hstageval :
      PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator w =
        T.transitionSubgroupGenerator i ^ m := by
    exact LabelWord.evalGroup_repeatPositive
      T.transitionSubgroupGenerator i m
  apply Subtype.ext
  calc
    ((T.transitionSubgroupGenerator i ^ m :
        T.transitionGroup) : RightPerm V) =
      ((PSTS.SignedWord.evalGroup
        T.transitionSubgroupGenerator w :
          T.transitionGroup) : RightPerm V) := by
          exact congrArg
            (fun g : T.transitionGroup => (g : RightPerm V))
            hstageval.symm
    _ = T.wordValue w := T.evalGroup_transitionSubgroupGenerator_val w
    _ = 1 := hstage

variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- SOURCE-GEOMETRIC APPLICATION. In the actual assembled
rank-two three-family completed coset stage, each generator i
has order dividing ANY prescribed period m_i already valid
in the ambient group.

Unlike the abstract universal catalogue's definition, the
period of this completed stage is derived from its checked
rank-two cluster/augmentation geometry, including all labels
outside the parent rank-two alphabet. -/
theorem rankTwoThreeFamilyStage_preserves_periods
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (m : ι → ℕ)
    (hperiod : ∀ i, (gen i) ^ (m i) = 1)
    (i : ι) :
    (K.rankTwoThreeFamilyStage hcard hgen hret).transitionSubgroupGenerator i ^ (m i) = 1 := by
  apply completeStage_generator_pow_of_rankOneKernel
    gen (K.rankTwoThreeFamilyStage hcard hgen hret)
    (by
      intro C hC w hw hval
      exact K.rankTwoThreeFamilyStage_rankOne_wordValue_eq_one
        hcard hgen hret C hC w hw hval)
    i (m i) (hperiod i)

/-- In particular, for the original-source first stage H1,
whose labelled generators are loops or involutions, EVERY
positive transition in the genuine rank-two three-family
completed stage is an involution or an identity, including
the true type-(2) B-augmentations. -/
theorem rankTwoThreeFamilyStage_involutive
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hinvolutive : ∀ i, (gen i) ^ 2 = 1)
    (i : ι) :
    (K.rankTwoThreeFamilyStage hcard hgen hret).transitionSubgroupGenerator i ^ 2 = 1 := by
  exact K.rankTwoThreeFamilyStage_preserves_periods
    hcard hgen hret (fun _ => 2) hinvolutive i

end CayleySubgraphSpec

end ABO
end PSTSEPPA
