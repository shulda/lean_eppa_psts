import PSTSEPPA.ABO.UniversalKernelPermutationCatalogue
import Mathlib.GroupTheory.OrderOfElement

/-!
# The exact unary-period criterion for rank-one stable ABO stages

For any signed word using at most ONE distinguished generator, its value
in an arbitrary group is an integral power of that generator. Hence
the rank-one word-kernel property of a completed finite stage is
equivalent to the familiar divisibility of generator orders.

This removes the quantified-over-all-words predicate from the proposed
universal rank-one catalogue: it suffices to bound the order of each
completed stage's actual transition permutation by the order of the
corresponding ambient H1 generator. In the corrected source first stage
the latter orders are 1 (loop label) or 2 (non-loop label).

The theorem is formalized for arbitrary groups, including infinite-order
generators, inverse letters, empty alphabets, repeated generators and
genuine loops. It does NOT assert the geometric order bounds for all
source Definition-5.3 stages; those must be established separately.
-/

namespace PSTSEPPA
namespace ABO

namespace LabelWord

variable {ι : Type*}

/-- Signed exponent sum of a word when it uses a singleton alphabet.
The value depends only on the signs, not on the names of the letters. -/
def signedExponent : LabelWord ι → ℤ
  | [] => 0
  | .pos _ :: w => 1 + signedExponent w
  | .neg _ :: w => -1 + signedExponent w

/-- A word supported on the empty alphabet has no letters at all. -/
theorem eq_nil_of_uses_empty (w : LabelWord ι)
    (hw : Uses (∅ : Finset ι) w) : w = [] := by
  cases w with
  | nil => rfl
  | cons s w =>
      have h : signedBase s ∈ (∅ : Finset ι) := hw.1
      simp at h

/-- An arbitrary signed singleton word, with any combination of positive
and negative letters, evaluates to exactly the corresponding integer power.
This identity is true in any noncommutative ambient group. -/
theorem evalGroup_singleton_zpow
    {Γ : Type*} [Group Γ] [DecidableEq ι]
    (gen : ι → Γ) (a : ι) :
    ∀ (w : LabelWord ι), Uses ({a} : Finset ι) w →
      PSTS.SignedWord.evalGroup gen w = (gen a) ^ signedExponent w := by
  intro w
  induction w with
  | nil =>
      intro _
      simp [signedExponent]
  | cons s w ih =>
      intro hw
      have hs : signedBase s = a :=
        Finset.mem_singleton.mp hw.1
      cases s with
      | pos i =>
          change i = a at hs
          subst i
          change gen a * PSTS.SignedWord.evalGroup gen w =
            (gen a) ^ (1 + signedExponent w)
          rw [ih hw.2, zpow_add]
          simp
      | neg i =>
          change i = a at hs
          subst i
          change (gen a)⁻¹ * PSTS.SignedWord.evalGroup gen w =
            (gen a) ^ (-1 + signedExponent w)
          rw [ih hw.2, zpow_add]
          simp

end LabelWord

variable {ι Γ Δ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]

/-- Exact rank-one kernel transfer by generator orders: if each upstairs
generator's order divides its downstairs counterpart's order, no one-letter
word can be a new nontrivial relation upstairs. This includes infinite
orders, encoded by `orderOf = 0`, without falsely assuming finiteness. -/
theorem rankOne_wordKernel_of_orders_dvd
    (genDown : ι → Γ) (genUp : ι → Δ)
    (hdiv : ∀ i, orderOf (genUp i) ∣ orderOf (genDown i))
    (C : Finset ι) (hC : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup genDown w = 1) :
    PSTS.SignedWord.evalGroup genUp w = 1 := by
  by_cases hEmpty : C = ∅
  · have hnil : w = [] :=
      LabelWord.eq_nil_of_uses_empty w (by simpa [hEmpty] using hw)
    subst w
    simp
  · have hNonempty : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨i, hi⟩ := hNonempty
    have hSubset : C ⊆ ({i} : Finset ι) := by
      intro j hj
      have hjEq : j = i :=
        (Finset.card_le_one.mp hC) j hj i hi
      simp [hjEq]
    have hwi : LabelWord.Uses ({i} : Finset ι) w := hw.mono hSubset
    have hDown := LabelWord.evalGroup_singleton_zpow genDown i w hwi
    have hUp := LabelWord.evalGroup_singleton_zpow genUp i w hwi
    rw [hDown] at hval
    rw [hUp]
    have hord : (orderOf (genUp i) : ℤ) ∣
        (orderOf (genDown i) : ℤ) := by
      exact_mod_cast hdiv i
    have hExp : (orderOf (genDown i) : ℤ) ∣
        LabelWord.signedExponent w :=
      (orderOf_dvd_iff_zpow_eq_one).mpr hval
    exact (orderOf_dvd_iff_zpow_eq_one).mp (hord.trans hExp)

/-- The period/order criterion on ACTUAL transition-group generators
is sufficient for every required rank-one completed-stage word kernel.
It deliberately concerns the completed stage, not a Cayley-coordinate
approximation of that stage. -/
theorem completeStage_rankOneKernel_of_orders_dvd
    (gen : ι → Γ) (T : CompleteEGraph V Edge ι)
    (hdiv : ∀ i,
      orderOf (T.transitionSubgroupGenerator i) ∣ orderOf (gen i))
    (C : Finset ι) (hC : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    T.wordValue w = 1 := by
  have hgroup :
      PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator w = 1 :=
    rankOne_wordKernel_of_orders_dvd gen
      T.transitionSubgroupGenerator hdiv C hC w hw hval
  have hcoe := congrArg
    (fun x : T.transitionGroup => (x : RightPerm V)) hgroup
  exact (T.evalGroup_transitionSubgroupGenerator_val w).symm.trans hcoe

/-- Source-friendly version: exact ambient generator periods m_i and
stage period bounds by the very same m_i imply the required word kernel.
This is the precise abstract bridge needed for the proposed H1 to G2
universal-rank-one substitution. -/
theorem completeStage_rankOneKernel_of_periods
    (gen : ι → Γ) (T : CompleteEGraph V Edge ι)
    (m : ι → ℕ)
    (hExact : ∀ i, orderOf (gen i) = m i)
    (hPeriod : ∀ i, T.transitionSubgroupGenerator i ^ (m i) = 1)
    (C : Finset ι) (hC : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    T.wordValue w = 1 := by
  apply completeStage_rankOneKernel_of_orders_dvd gen T
    (fun i => by
      rw [hExact i]
      exact orderOf_dvd_of_pow_eq_one (hPeriod i))
    C hC w hw hval

/-- Every rank-one period-correct labelled permutation action on Fin M
belongs to the universal kernel-correct action catalogue, without
checking infinitely many words. -/
noncomputable def boundedKernelAction_of_periods
    (gen : ι → Γ) (M : ℕ)
    (ρ : ι → Equiv.Perm (Fin M))
    (m : ι → ℕ)
    (hExact : ∀ i, orderOf (gen i) = m i)
    (hPeriod : ∀ i,
      (actionGraph ρ).transitionSubgroupGenerator i ^ (m i) = 1) :
    boundedKernelAction gen 1 M :=
  ⟨ρ, by
    intro C hC w hw hval
    exact completeStage_rankOneKernel_of_periods
      gen (actionGraph ρ) m hExact hPeriod C hC w hw hval⟩

end ABO
end PSTSEPPA
