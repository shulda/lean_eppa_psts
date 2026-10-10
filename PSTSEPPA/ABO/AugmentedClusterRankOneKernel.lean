import PSTSEPPA.ABO.AugmentedClusterSingletonKernel
import PSTSEPPA.ABO.StageStabilityWordKernel

/-!
# Full rank-one transition-group kernel for genuine augmented clusters

The previously certified type-(1) augmented-cluster theorem handles
signed words over a specified singleton {i}. A rank-one stability
condition in corrected ABO Proposition 5.4 is instead quantified
over every subalphabet C of cardinality at most one, including
the EMPTY alphabet and singleton labels outside the parent A.

For a nonempty word its first signed letter has an underlying
generator i∈C. Cardinality ≤1 forces C={i}, so the genuine
geometric singleton-kernel theorem applies. An empty word acts
trivially. Via the exact complete-graph transition-group criterion
we obtain identity word values in the ACTUAL permutation subgroup.

The result holds for ANY augmented cluster (any finite family of
proper constituent alphabets, any attached D⊆A and basepoint v),
without additional assumptions on Γ, its generator map or
nonempty pieces. It is the correct all-singleton type-(1)
counterpart of the type-(2) rank-two result.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace ClusterSpec

variable (P : ClusterSpec A)

/-- Every ambient identity-valued signed C-word with |C|≤1
fixes EVERY vertex of a genuinely completed augmented
cluster, including C empty and labels outside A. -/
theorem augmentedTrivialStage_rankOne_identity_word_fixes
    (D : Finset ι) (hDA : D ⊆ A) (v : Γ)
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι)
    (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1)
    (x : (P.augmentedCayleySubgraph gen D hDA v).Vertex) :
    (P.augmentedTrivialStage (gen := gen) D hDA v).followWord x w = x := by
  classical
  cases w with
  | nil =>
      rfl
  | cons s w =>
      have hsC : signedBase s ∈ C := hw.1
      have hC : C = {signedBase s} := by
        apply Finset.Subset.antisymm
        · intro j hj
          have hji := (Finset.card_le_one.mp hCcard)
            j hj (signedBase s) hsC
          simpa only [Finset.mem_singleton] using hji
        · exact Finset.singleton_subset_iff.mpr hsC
      have hw' :
          LabelWord.Uses ({signedBase s} : Finset ι) (s :: w) := by
        rwa [hC] at hw
      exact P.augmentedTrivialStage_singleton_identity_word_fixes
        D hDA v (signedBase s) (s :: w) hw' hval x

/-- Source-facing group form: the ACTUAL transition-group word
value of any ambient identity-valued ≤1-label signed word is
the identity of the completed augmented-cluster stage. -/
theorem augmentedTrivialStage_rankOne_wordValue_eq_one
    (D : Finset ι) (hDA : D ⊆ A) (v : Γ)
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι)
    (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (P.augmentedTrivialStage (gen := gen) D hDA v).wordValue w = 1 := by
  apply ((P.augmentedTrivialStage
    (gen := gen) D hDA v).wordValue_eq_one_iff_all_vertices_fixed w).mpr
  intro x
  exact P.augmentedTrivialStage_rankOne_identity_word_fixes
    D hDA v C hCcard w hw hval x

end ClusterSpec
end ABO
end PSTSEPPA
