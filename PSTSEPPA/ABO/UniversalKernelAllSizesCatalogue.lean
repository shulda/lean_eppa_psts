import PSTSEPPA.ABO.UniversalKernelPermutationCatalogue

/-!
# The bounded-size universal ABO stage without padding

The first universal permutation catalogue used copies of one fixed
carrier Fin M. An actual completed source stage may have ANY
cardinality n <= M; padding its vertex permutations by fixed points
is mathematically correct but requires an extra equivariant extension
construction.

Here we implement a cleaner equivalent variant: index ALL finite
kernel-correct labelled actions on Fin n, simultaneously for
0 <= n <= M. Every exact-size finite labelled action already occurs
as a literal coordinate after a change of names by a finite equivalence.
No extension by artificial fixed points is required.

The dependent Sigma carrier has a tag containing BOTH the stage size
and the labelled action, and preserves every genuine signed trajectory.
Its generated synchronized group is finite (for finite ambient group)
and k-stable. This is the algebraic universal-indexing theorem; it
does not establish that the source Definition-5.3 completed geometric
stages have the necessary k-word kernel, nor that their size <= M.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Finite index of every kernel-correct labelled permutation action
of EVERY cardinality n at most M. An n=0 stage is allowed and
harmless; the stage size is part of the retained index. -/
abbrev boundedKernelAllSizesIndex
    (gen : ι → Γ) (k M : ℕ) :=
  Σ n : Fin (M + 1), boundedKernelAction gen k n.val

noncomputable instance (gen : ι → Γ) (k M : ℕ) :
    Fintype (boundedKernelAllSizesIndex gen k M) := by
  classical
  infer_instance

/-- Its exact dependent tagged vertex type; every catalogue
coordinate preserves its own Fin n carrier and its own stage label. -/
abbrev boundedKernelAllSizesVertex
    (gen : ι → Γ) (k M : ℕ) :=
  Σ j : boundedKernelAllSizesIndex gen k M, Fin j.1.val

/-- The actual complete signed E-graph of all <= M cardinality
kernel-correct actions. Distinct entries remain genuinely distinct,
even if their permutations have identical ambient group coordinates. -/
noncomputable def boundedKernelAllSizesStage
    (gen : ι → Γ) (k M : ℕ) :
    CompleteEGraph
      (boundedKernelAllSizesVertex gen k M)
      (ActionEdge (boundedKernelAllSizesVertex gen k M) ι) ι :=
  dependentDisjointStage
    (fun j : boundedKernelAllSizesIndex gen k M => actionGraph j.2.1)

/-- Every ambient identity word on at most k letters fixes ALL
vertices in this bounded-size universal stage, including the
zero-size fibre and all inverse-labelled paths. -/
theorem boundedKernelAllSizesStage_wordValue_eq_one
    (gen : ι → Γ) (k M : ℕ)
    (C : Finset ι) (hC : C.card ≤ k)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (boundedKernelAllSizesStage gen k M).wordValue w = 1 := by
  apply (dependentDisjointStage_wordValue_eq_one_iff
    (fun j : boundedKernelAllSizesIndex gen k M => actionGraph j.2.1) w).mpr
  intro j
  exact j.2.2 C hC w hw hval

/-- Exact inclusion of any genuine Fin n labelled action that meets
the required kernel predicate, whenever n<=M. Crucially, this
requires NO padding, prescribed representative set, or choice of a
bijection to a subset of Fin M. -/
def boundedKernelAllSizesEntry
    (gen : ι → Γ) (k M n : ℕ) (hn : n ≤ M)
    (ρ : ι → Equiv.Perm (Fin n))
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            (actionGraph ρ).wordValue w = 1) :
    boundedKernelAllSizesIndex gen k M :=
  ⟨⟨n, Nat.lt_succ_of_le hn⟩, ⟨ρ, hkernel⟩⟩

/-- A source entry's actual signed paths coincide literally with
paths in the universal stage's own tagged coordinate. -/
theorem boundedKernelAllSizesEntry_followWord
    (gen : ι → Γ) (k M n : ℕ) (hn : n ≤ M)
    (ρ : ι → Equiv.Perm (Fin n))
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            (actionGraph ρ).wordValue w = 1)
    (x : Fin n) (w : LabelWord ι) :
    (boundedKernelAllSizesStage gen k M).followWord
      (⟨boundedKernelAllSizesEntry gen k M n hn ρ hkernel, x⟩ :
        boundedKernelAllSizesVertex gen k M) w =
      ⟨boundedKernelAllSizesEntry gen k M n hn ρ hkernel,
        (actionGraph ρ).followWord x w⟩ := by
  exact dependentDisjointStage_followWord
    (fun j : boundedKernelAllSizesIndex gen k M => actionGraph j.2.1)
    (boundedKernelAllSizesEntry gen k M n hn ρ hkernel) x w

/-- The full dependent tagged carrier is finite, even when the
ambient labelled group is infinite: both the possible sizes and
all the permutation-label choices at each size are finite. -/
theorem finite_boundedKernelAllSizesVertex
    (gen : ι → Γ) (k M : ℕ) :
    Finite (boundedKernelAllSizesVertex gen k M) := by
  classical
  infer_instance

/-- Genuine synchronized generated group with a surjective
label-preserving first projection to the original ambient group. -/
noncomputable def boundedKernelAllSizesCoverQuotient
    (gen : ι → Γ) (k M : ℕ) (hgen : IsGenerated gen) :
    LabelledGroupQuotient
      (SynchronizedProduct.generator gen
        (boundedKernelAllSizesStage gen k M).transitionSubgroupGenerator)
      gen :=
  SynchronizedProduct.stageCoverQuotient gen
    (boundedKernelAllSizesStage gen k M) hgen

/-- This one concrete finite-stage assembly admits a full k-STABLE
surjective labelled quotient, not an assumed action or an
unconstructed group cover. -/
theorem boundedKernelAllSizesCoverQuotient_kStable
    (gen : ι → Γ) (k M : ℕ) (hgen : IsGenerated gen) :
    (boundedKernelAllSizesCoverQuotient gen k M hgen).KStable k := by
  exact SynchronizedProduct.stageCoverQuotient_kStable_of_stageKernel
    gen (boundedKernelAllSizesStage gen k M) hgen k
    (by
      intro C hC w hw hval
      exact boundedKernelAllSizesStage_wordValue_eq_one
        gen k M C hC w hw hval)

/-- If the original ambient group is finite, so is the actual
generated synchronous covering group of ALL sizes <= M. -/
theorem finite_boundedKernelAllSizesCover
    (gen : ι → Γ) (k M : ℕ) [Finite Γ] :
    Finite (SynchronizedProduct.stageCover gen
      (boundedKernelAllSizesStage gen k M)) := by
  classical
  letI : Finite (boundedKernelAllSizesVertex gen k M) :=
    finite_boundedKernelAllSizesVertex gen k M
  exact SynchronizedProduct.finite_stageCover gen
    (boundedKernelAllSizesStage gen k M)

end ABO
end PSTSEPPA
