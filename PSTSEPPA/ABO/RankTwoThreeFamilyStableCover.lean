import PSTSEPPA.ABO.RankTwoType2IndexedFamily
import PSTSEPPA.ABO.AugmentedClusterIndexedFamily
import PSTSEPPA.ABO.RankTwoPlainFullCEKernel
import PSTSEPPA.ABO.SynchronizedStageStableCover

/-!
# One finite 1-stable synchronized cover of THREE genuine rank-two stage families

For a fixed rank-two A-labelled Cayley skeleton K over a generated
retractable Γ, we now have actual, independently audited completed
stages of three kinds relevant to corrected ABO Section 5:

(0) the ordinary completed full proper-coset extension of K;
(1) a finite dependent family of genuine anchored augmented clusters
    P ∪ vG[D], indexed over every allowed P,D,v in Γ;
(2) a finite dependent family of genuine off-B-singleton augmented
    full coset extensions of K, indexed by actual B and quotient roots z.

Each stage family has the FULL rank-one word kernel, including
signed labels outside its parent A. We take the literal oriented
CompleteEGraph DISJOINT UNION of all three completed families;
no arbitrary quotient identifications or new paths are introduced.

The resulting single complete action has the rank-one kernel.
By synchronizing its actual transition group with Γ, we construct
a concrete generator-preserving SURJECTIVE labelled group quotient
onto Γ which is 1-STABLE. For finite Γ, all of its stages, the
disjoint action carrier and the synchronized cover are finite.

The finite type-(1) family here is a conservative SUPERFAMILY,
not an assertion that it is source Definition 5.3's exact Z₁.
The chosen K has not yet been constructed as an H₁-cover.
The actual full Section-5 Z₁, H₁, G₂→H₁ and later induction
therefore remain OPEN even after this genuine three-family cover.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- One genuinely finite (for finite Γ) tagged carrier:
old full-CE quotient points, all anchored augmented
cluster stage points, and all singleton-augmented
full-CE stage points. The three cases are DISJOINT. -/
abbrev rankTwoThreeFamilyVertex
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  (K.MultiCosetVertex (allProperCosetFamily A)
    (K.admissible_of_card_le_two hcard.le) hgen hret) ⊕
  ((Σ j : ClusterSpec.augmentedType1Index gen A,
      ClusterSpec.augmentedType1Vertex j) ⊕
   (Σ j : K.rankTwoType2SingletonIndex hcard hgen hret,
      K.rankTwoType2SingletonVertex hcard hgen hret j))

/-- Literal complete EGraph for the union of ALL THREE
source-related rank-two stage subfamilies. Formal inverse
edge tokens are correctly tagged by both union levels,
and each original signed word acts in its own summand. -/
noncomputable def rankTwoThreeFamilyStage
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  (K.allProperCompletedStage
    (K.admissible_of_card_le_two hcard.le)
    hgen hret hcard.ge).disjointUnion
    ((ClusterSpec.augmentedType1FamilyStage gen A).disjointUnion
      (K.rankTwoType2SingletonFamilyStage hcard hgen hret))

/-- On the LITERAL three-summand complete action,
every signed word on ≤1 letters with ambient group
value 1 acts as the identity permutation. No extra
condition on chosen components or injective labels. -/
theorem rankTwoThreeFamilyStage_rankOne_wordValue_eq_one
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (K.rankTwoThreeFamilyStage hcard hgen hret).wordValue w = 1 := by
  let T₀ := K.allProperCompletedStage
    (K.admissible_of_card_le_two hcard.le) hgen hret hcard.ge
  let T₁ := ClusterSpec.augmentedType1FamilyStage gen A
  let T₂ := K.rankTwoType2SingletonFamilyStage hcard hgen hret
  change (T₀.disjointUnion (T₁.disjointUnion T₂)).wordValue w = 1
  apply (T₀.disjointUnion_wordValue_eq_one_iff
    (T₁.disjointUnion T₂) w).mpr
  constructor
  · exact K.rankTwo_completedStage_rankOne_wordValue_eq_one
      hcard hgen hret C hCcard w hw hval
  · apply (T₁.disjointUnion_wordValue_eq_one_iff T₂ w).mpr
    exact ⟨ClusterSpec.augmentedType1Family_rankOne_wordValue_eq_one
      gen A C hCcard w hw hval,
      K.rankTwoType2SingletonFamily_rankOne_wordValue_eq_one
        hcard hgen hret C hCcard w hw hval⟩

/-- A concrete generated synchronized group with ambient
Γ as its first coordinate and the literal three-family
transition subgroup as its second coordinate. -/
noncomputable abbrev rankTwoThreeFamilyCover
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  SynchronizedProduct.stageCover gen
    (K.rankTwoThreeFamilyStage hcard hgen hret)

/-- The ACTUAL surjective, generator-preserving quotient
to ambient Γ, constructed from the synchronized subgroup
rather than postulated as the desired G₂→H₁ map. -/
noncomputable def rankTwoThreeFamilyCoverQuotient
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  SynchronizedProduct.stageCoverQuotient gen
    (K.rankTwoThreeFamilyStage hcard hgen hret) hgen

/-- Rank-one stability of the true finite-stage candidate
group onto Γ, from the three checked component kernels.
This is an actual KStable 1 proof about the concrete
labelled quotient, NOT a hypothetical stage interface. -/
theorem rankTwoThreeFamilyCoverQuotient_oneStable
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    (K.rankTwoThreeFamilyCoverQuotient hcard hgen hret).KStable 1 := by
  exact SynchronizedProduct.stageCoverQuotient_kStable_of_stageKernel
    gen (K.rankTwoThreeFamilyStage hcard hgen hret)
    hgen 1
    (by
      intro C hC w hw hval
      exact K.rankTwoThreeFamilyStage_rankOne_wordValue_eq_one
        hcard hgen hret C hC w hw hval)

variable [Finite Γ]

/-- The entire true three-summand carrier is finite when
ambient Γ is finite, retaining all old component and
new full-coset tags rather than relying on ambient
coordinate projection injectivity. -/
theorem finite_rankTwoThreeFamilyVertex
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Finite (K.rankTwoThreeFamilyVertex hcard hgen hret) := by
  classical
  letI : Finite
      (K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret) :=
    K.finite_allProperMultiCosetVertex
      (K.admissible_of_card_le_two hcard.le) hgen hret
  letI : Finite
      (Σ j : ClusterSpec.augmentedType1Index gen A,
        ClusterSpec.augmentedType1Vertex j) :=
    ClusterSpec.finite_augmentedType1FamilyCarrier gen A
  letI : Finite
      (Σ j : K.rankTwoType2SingletonIndex hcard hgen hret,
        K.rankTwoType2SingletonVertex hcard hgen hret j) :=
    K.finite_rankTwoType2SingletonFamilyCarrier hcard hgen hret
  infer_instance

/-- Its actual generated synchronized group is FINITE,
as a concrete subgroup of the product Γ × Transition(T).
Both projections are canonically defined and the first
is certified rank-one stable above. -/
theorem finite_rankTwoThreeFamilyCover
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Finite (K.rankTwoThreeFamilyCover hcard hgen hret) := by
  classical
  letI : Finite (K.rankTwoThreeFamilyVertex hcard hgen hret) :=
    K.finite_rankTwoThreeFamilyVertex hcard hgen hret
  exact SynchronizedProduct.finite_stageCover gen
    (K.rankTwoThreeFamilyStage hcard hgen hret)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
