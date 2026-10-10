import PSTSEPPA.ABO.RankTwoAllAmbientCosetSliceCover
import PSTSEPPA.ABO.AmbientSkeletonAlphabetRestriction

/-!
# One globally synchronized rank-two stage family from ONE ambient Cayley skeleton

Corrected ABO starts from an actual ambient incomplete Cayley skeleton,
not a separately chosen array of skeletons indexed by every rank-two
alphabet. We now eliminate that artificial extra input.

Given one S-labelled ambient skeleton K in a finite group Γ, form
the LITERAL edge restriction K|A to EVERY two-letter alphabet A;
then restrict each such skeleton to EVERY translated left coset
g·Γ[A], preserving actual old signed edges and real vertices.
Finally attach the previously certified complete three-family
rank-two stages over each genuine local Γ[A] and form their single
dependent disjoint union. Synchronize the latter directly with Γ.

Provided Γ is generated and only 2-retractable, this constructs an
ACTUAL surjective 1-stable labelled quotient onto Γ whose concrete
domain is 2-retractable, and FINITE when Γ is finite.

There is no global retractability assumption and no existential
hypothesis supplying the rank-two skeletons. However source H₁'s
specific cover geometry, exact Definition-5.3 catalogue Z₁, and
higher-rank bridge-free induction remain open; this is an
independently checked robust algebraic/geometric assembly step.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

/-- The family of ALL genuine B-edge restrictions of ONE
original ambient S-labelled Cayley skeleton, for each rank-two B.
Even for B not contained in S this is a well-defined literal
subgraph (with no old edges carrying absent labels). -/
noncomputable abbrev rankTwoGlobalSkeletonFamily
    (K : CayleySubgraphSpec gen S) :
    ∀ B : {B : Finset ι // B.card = 2},
      CayleySubgraphSpec gen B.1 :=
  fun B => K.restrictAlphabet B.1

/-- One actual dependent-disjoint complete stage consisting of
ALL two-letter local coset slices of the literal old-edge
restrictions of K, with genuine augmented CE stage geometry. -/
noncomputable abbrev rankTwoGlobalSkeletonStage
    (K : CayleySubgraphSpec gen S)
    (hret : KRetractable gen 2) :=
  rankTwoAllAmbientCosetsStage (rankTwoGlobalSkeletonFamily K) hret

/-- The full singleton-label word kernel, with group values
computed in the ORIGINAL ambient Γ. -/
theorem rankTwoGlobalSkeletonStage_rankOne_wordValue_eq_one
    (K : CayleySubgraphSpec gen S)
    (hret : KRetractable gen 2)
    (C : Finset ι) (hC : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (rankTwoGlobalSkeletonStage K hret).wordValue w = 1 :=
  rankTwoAllAmbientCosetsStage_rankOne_wordValue_eq_one
    (rankTwoGlobalSkeletonFamily K) hret C hC w hw hval

/-- The true surjective generator-preserving quotient to Γ,
from the ACTUAL synchronized group of every rank-two slice
generated from ONE incomplete ambient skeleton. -/
noncomputable def rankTwoGlobalSkeletonCoverQuotient
    (K : CayleySubgraphSpec gen S)
    (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    LabelledGroupQuotient
      (SynchronizedProduct.generator gen
        (rankTwoGlobalSkeletonStage K hret).transitionSubgroupGenerator)
      gen :=
  rankTwoAllAmbientCosetsCoverQuotient
    (rankTwoGlobalSkeletonFamily K) hret hgen

/-- This concrete global synchronized quotient is 1-stable. -/
theorem rankTwoGlobalSkeletonCoverQuotient_oneStable
    (K : CayleySubgraphSpec gen S)
    (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    (rankTwoGlobalSkeletonCoverQuotient K hret hgen).KStable 1 :=
  rankTwoAllAmbientCosetsCoverQuotient_oneStable
    (rankTwoGlobalSkeletonFamily K) hret hgen

/-- Corrected ABO rank descent gives 2-retractability of
the generated global cover, not postulated as an extra input. -/
theorem rankTwoGlobalSkeletonCover_twoRetractable
    (K : CayleySubgraphSpec gen S)
    (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    KRetractable
      (SynchronizedProduct.generator gen
        (rankTwoGlobalSkeletonStage K hret).transitionSubgroupGenerator)
      2 :=
  rankTwoAllAmbientCosetsCover_twoRetractable
    (rankTwoGlobalSkeletonFamily K) hret hgen

/-- The two-letter B-restriction of K has EXACTLY the
B-supported signed paths of the original K, not merely
paths inside its ambient group cosets. -/
theorem rankTwoGlobalSkeleton_restrictedFollows_iff
    (K : CayleySubgraphSpec gen S)
    (B : {B : Finset ι // B.card = 2})
    (u v : K.Vertex) (w : LabelWord ι)
    (hw : LabelWord.Uses B.1 w) :
    ((K.restrictAlphabet B.1).toEGraph).Follows u w v ↔
      (K.toEGraph).Follows u w v :=
  K.restrictAlphabet_follows_iff B.1 u v w hw

variable [Finite Γ]

/-- Even though all coset representatives and all 2-letter
alphabets are retained (no transversal), the true global
synchronized covering group is FINITE whenever Γ is finite. -/
theorem finite_rankTwoGlobalSkeletonCover
    (K : CayleySubgraphSpec gen S)
    (hret : KRetractable gen 2) :
    Finite (SynchronizedProduct.stageCover gen
      (rankTwoGlobalSkeletonStage K hret)) :=
  finite_rankTwoAllAmbientCosetsCover
    (rankTwoGlobalSkeletonFamily K) hret

/-- Every old vertex remains represented in the translated
rank-two local slice anchored at that vertex (for each B),
before taking the true augmented stage family. -/
theorem rankTwoGlobalSkeleton_oldVertex_in_localSlice
    (K : CayleySubgraphSpec gen S)
    (B : {B : Finset ι // B.card = 2})
    (y : K.Vertex) :
    ∃ x : ((K.restrictAlphabet B.1).leftCosetSlice y.1).Vertex,
      ((K.restrictAlphabet B.1).leftCosetSliceHom y.1).onVertex x = y :=
  rankTwoAllAmbientCosets_root_vertex_realized
    (rankTwoGlobalSkeletonFamily K) B y

end ABO
end PSTSEPPA
