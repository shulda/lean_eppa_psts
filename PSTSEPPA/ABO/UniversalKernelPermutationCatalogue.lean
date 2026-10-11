import PSTSEPPA.ABO.DependentDisjointStages
import PSTSEPPA.ABO.SynchronizedStageStableCover

/-!
# Universal finite permutation catalogue for rank-stable ABO stages

A fixed finite alphabet and a finite permutation carrier have only finitely
many labelled permutation actions. We retain *all* actions satisfying the
precise ambient rank-k signed-word kernel implication, rather than choosing
representatives of geometric stages. Their actual tagged disjoint action
has the same kernel implication, hence synchronizing it with a generated
ambient group gives a concrete k-stable labelled quotient.

This is the algebraic and finite-indexing part of the proposed rank-one
universal-stage replacement. It is valid at any rank, but it DOES NOT prove
that the actual completed geometric ABO stages satisfy the requisite kernel
condition. For ranks k >= 2 that condition is the historical-action content
of the still-missing Section 5 argument; universal enumeration is not a
substitute for it.

The universal action is based on *all* kernel-correct permutations, without
an arbitrary choice of representatives. It works with duplicate/identity
labels, inverse words, empty alphabets, and even a zero-point carrier.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Every labelled permutation action on the fixed carrier `Fin M` whose
rank-k signed-word kernel contains the ambient labelled group kernel.
This is an actual subtype of the FINITE type of all labelled permutations;
membership does not require a decidable finite list of words. -/
abbrev boundedKernelAction (gen : ι → Γ) (k M : ℕ) :=
  {ρ : ι → Equiv.Perm (Fin M) //
    ∀ (C : Finset ι), C.card ≤ k →
      ∀ (w : LabelWord ι), LabelWord.Uses C w →
        PSTS.SignedWord.evalGroup gen w = 1 →
          (actionGraph ρ).wordValue w = 1}

/-- There are finitely many kernel-correct permutation actions on any
fixed finite carrier, even though the membership predicate quantifies
over all signed words. -/
noncomputable instance (gen : ι → Γ) (k M : ℕ) :
    Fintype (boundedKernelAction gen k M) := by
  classical
  infer_instance

/-- The actual complete stage with one distinctly tagged `Fin M` copy
for EACH kernel-correct action, with its original signed transitions.
The tagged index is retained even when two actions happen to coincide. -/
noncomputable def boundedKernelStage
    (gen : ι → Γ) (k M : ℕ) :
    CompleteEGraph
      (Σ _ : boundedKernelAction gen k M, Fin M)
      (ActionEdge (Σ _ : boundedKernelAction gen k M, Fin M) ι) ι :=
  dependentDisjointStage
    (fun ρ : boundedKernelAction gen k M => actionGraph ρ.1)

/-- Every member of the entire universal catalogue fixes every
ambient-trivial signed word supported on at most k letters. The proof
uses the true componentwise word-kernel equivalence, not any
assumption about the transition group of the disjoint union. -/
theorem boundedKernelStage_wordValue_eq_one
    (gen : ι → Γ) (k M : ℕ)
    (C : Finset ι) (hC : C.card ≤ k)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (boundedKernelStage gen k M).wordValue w = 1 := by
  apply (dependentDisjointStage_wordValue_eq_one_iff
    (fun ρ : boundedKernelAction gen k M => actionGraph ρ.1) w).mpr
  intro ρ
  exact ρ.2 C hC w hw hval

/-- The embedding of any catalogue entry as its own tagged stage
preserves the EXACT signed word path, including both inverses.
In particular the universal stage never identifies distinct stage
tags or replaces genuine actions by ambient group coordinates. -/
theorem boundedKernelStage_followWord
    (gen : ι → Γ) (k M : ℕ)
    (ρ : boundedKernelAction gen k M)
    (x : Fin M) (w : LabelWord ι) :
    (boundedKernelStage gen k M).followWord
        (⟨ρ, x⟩ : Σ _ : boundedKernelAction gen k M, Fin M) w =
      ⟨ρ, (actionGraph ρ.1).followWord x w⟩ := by
  exact dependentDisjointStage_followWord
    (fun j : boundedKernelAction gen k M => actionGraph j.1)
    ρ x w

/-- The whole sigma-tagged universal stage is genuinely finite.
No finiteness or generatedness assumption on the ambient group is
needed to establish the finite catalogue or the finite stage. -/
theorem finite_boundedKernelStageVertex
    (gen : ι → Γ) (k M : ℕ) :
    Finite (Σ _ : boundedKernelAction gen k M, Fin M) := by
  classical
  infer_instance

/-- The actual generator-preserving SURJECTIVE group quotient
arising by synchronizing the ambient group with the complete
universal stage's generated transition subgroup. -/
noncomputable def boundedKernelCoverQuotient
    (gen : ι → Γ) (k M : ℕ) (hgen : IsGenerated gen) :
    LabelledGroupQuotient
      (SynchronizedProduct.generator gen
        (boundedKernelStage gen k M).transitionSubgroupGenerator)
      gen :=
  SynchronizedProduct.stageCoverQuotient gen
    (boundedKernelStage gen k M) hgen

/-- The concrete universal synchronized cover is k-STABLE for
every k, not just k=1. This is an actual labelled quotient,
not a group merely assumed to act on the stages. -/
theorem boundedKernelCoverQuotient_kStable
    (gen : ι → Γ) (k M : ℕ) (hgen : IsGenerated gen) :
    (boundedKernelCoverQuotient gen k M hgen).KStable k := by
  exact SynchronizedProduct.stageCoverQuotient_kStable_of_stageKernel
    gen (boundedKernelStage gen k M) hgen k
    (by
      intro C hC w hw hval
      exact boundedKernelStage_wordValue_eq_one
        gen k M C hC w hw hval)

/-- If the ambient group is finite, the actual synchronized
universal group is finite. Its finite action catalogue does not
need a computable enumeration of the infinitely quantified
membership predicate. -/
theorem finite_boundedKernelCover
    (gen : ι → Γ) (k M : ℕ) [Finite Γ] :
    Finite (SynchronizedProduct.stageCover gen
      (boundedKernelStage gen k M)) := by
  classical
  letI : Finite (Σ _ : boundedKernelAction gen k M, Fin M) :=
    finite_boundedKernelStageVertex gen k M
  exact SynchronizedProduct.finite_stageCover gen
    (boundedKernelStage gen k M)

/-- Necessity of the ambient rank-k kernel condition: if an
actual labelled group G admits both a k-stable quotient onto
the ambient H and a generator-preserving quotient onto a stage's
TRUE transition subgroup, then every H-trivial rank-k word
must act trivially on that completed stage.

This is independent of stage finiteness and is the obstruction
tested by the source geometric induction at ranks >= 2. -/
theorem stageKernel_of_commonQuotients
    {G H V Edge : Type*} [Group G] [Group H]
    (genG : ι → G) (genH : ι → H)
    (T : CompleteEGraph V Edge ι)
    (Q : LabelledGroupQuotient genG genH)
    (R : LabelledGroupQuotient genG T.transitionSubgroupGenerator)
    (k : ℕ) (hstable : Q.KStable k)
    (C : Finset ι) (hC : C.card ≤ k)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup genH w = 1) :
    T.wordValue w = 1 := by
  have hG : PSTS.SignedWord.evalGroup genG w = 1 :=
    ((Q.kStable_iff_word_kernel k).mp hstable) C hC w hw hval
  have hT :
      PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator w = 1 := by
    calc
      PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator w =
          R.hom (PSTS.SignedWord.evalGroup genG w) :=
        (R.map_evalGroup w).symm
      _ = 1 := by simp [hG]
  have heval := T.evalGroup_transitionSubgroupGenerator_val w
  rw [hT] at heval
  exact heval.symm

end ABO
end PSTSEPPA
