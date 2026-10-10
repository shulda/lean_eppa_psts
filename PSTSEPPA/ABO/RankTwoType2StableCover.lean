import PSTSEPPA.ABO.RankTwoType2IndexedFamily
import PSTSEPPA.ABO.SynchronizedStageStableCover

/-!
# A genuine finite 1-stable group cover from ALL type-(2) singleton stages

This is the first actual finite-group covering step assembled
from a whole, concretely indexed family of corrected ABO
Definition-5.3 rank-two type-(2) singleton augmentations.

For a rank-two A-labelled skeleton inside a generated retractable
ambient group Γ, form the dependent disjoint complete EGraph T of
ALL selected proper-B/off-B-singleton full coset augmentations.
Use the ACTUAL transition group of T, synchronize its labelled
generators with the ambient Γ generators, and take the generated
subgroup of Γ × Transition(T).

The first-coordinate projection from this concrete synchronized
group is a generator-preserving SURJECTIVE group quotient onto Γ.
By the complete per-fibre signed-word kernel, T kills every word
supported by ≤1 labels which is trivial in Γ. Consequently the
new group's quotient onto Γ is genuinely 1-STABLE.

If Γ is finite, the fibre roots, quotient carriers, disjoint
family action and transition group are all finite, hence the
new synchronized group is FINITE as well.

This covers ONLY the entire type-(2) off-component singleton
SUBFAMILY of Z₁. It is not the whole source H₁-cover/Z₁ catalogue,
does not build the augmented-cluster family nor the full
G₂→H₁ step, and does not prove higher-rank reflection or EPPA.
In particular its stability is not misrepresented as stability
of the unconstructed full source quotient.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The actual generated synchronous group formed from
the ambient Γ and the transition subgroup of the entire
dependent disjoint family of genuine type-(2) stages. -/
abbrev rankTwoType2SingletonCover
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  SynchronizedProduct.stageCover gen
    (K.rankTwoType2SingletonFamilyStage hcard hgen hret)

/-- The canonical, explicit, generator-preserving surjective
quotient of the actual synchronized cover onto Γ. -/
noncomputable def rankTwoType2SingletonCoverQuotient
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    LabelledGroupQuotient
      (SynchronizedProduct.generator gen
        (K.rankTwoType2SingletonFamilyStage
          hcard hgen hret).transitionSubgroupGenerator) gen :=
  SynchronizedProduct.stageCoverQuotient gen
    (K.rankTwoType2SingletonFamilyStage hcard hgen hret) hgen

/-- The concrete synchronized group quotient Γ is
1-STABLE: it reflects equality of all words on any
single generator, including inverse letters and labels
outside the rank-two parent alphabet A. -/
theorem rankTwoType2SingletonCoverQuotient_oneStable
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    (K.rankTwoType2SingletonCoverQuotient
      hcard hgen hret).KStable 1 := by
  exact SynchronizedProduct.stageCoverQuotient_kStable_of_stageKernel
    gen
    (K.rankTwoType2SingletonFamilyStage hcard hgen hret)
    hgen 1
    (by
      intro C hC w hw hval
      exact K.rankTwoType2SingletonFamily_rankOne_wordValue_eq_one
        hcard hgen hret C hC w hw hval)

variable [Finite Γ]

/-- This is an ACTUAL finite group cover, rather than only
a conditional assertion about a hypothetical finite stage.
The index family may be empty without spoiling finiteness,
surjectivity or rank-one stability. -/
theorem finite_rankTwoType2SingletonCover
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Finite (K.rankTwoType2SingletonCover hcard hgen hret) := by
  classical
  letI : Finite
      (Σ j : K.rankTwoType2SingletonIndex hcard hgen hret,
        K.rankTwoType2SingletonVertex hcard hgen hret j) :=
    K.finite_rankTwoType2SingletonFamilyCarrier hcard hgen hret
  exact SynchronizedProduct.finite_stageCover gen
    (K.rankTwoType2SingletonFamilyStage hcard hgen hret)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
