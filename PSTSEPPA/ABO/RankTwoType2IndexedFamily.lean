import PSTSEPPA.ABO.FiniteRankTwoType2Stages
import PSTSEPPA.ABO.RankTwoType2RankOneKernel
import PSTSEPPA.ABO.DependentDisjointStages

/-!
# A genuine finite family of rank-two type-(2) completed stages

Corrected ABO Definition 5.3 requires a FINITE family of complete
EGraphs. The preceding work constructed and verified the individual
rank-two type-(2) singleton-augmented full-coset stages and established
the complete rank-one word-kernel test for EACH one.

Here we construct the finite indexed family of ALL such stages
arising from one rank-two Cayley skeleton K:

* an index is a genuinely selected proper alphabet B ⊂ A,
  together with an actual tagged multi-coset vertex z which
  does NOT lie in a selected tagged full B-coset;
* at each index we use the literal, already-certified complete
  EGraph formed by attaching the ambient full B-coset to z;
* when Γ is finite, the index type, every fibre, their sigma
  disjoint union and its actual labelled transition group
  are all finite;
* all identity-valued ambient signed words using ≤1 letters
  act trivially on the assembled EGraph, by the componentwise
  action/kernel theorems applied to the real stages.

This is the precise TYPE-(2) singleton subfamily, not a claim to
have constructed all of source Z₁ (which also contains augmented
clusters, unaugmented full cosets and additional H₁-cover data).
The group quotient to H₁ and the higher-rank induction remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An actual selected proper B together with a tagged vertex z
outside ALL complete B-coset constituent images. The type may
be empty; no artificial nonemptiness assumption is imposed. -/
abbrev rankTwoType2SingletonIndex
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  Σ B : {B : Finset ι // B ∈ (allProperCosetFamily A).alphabets},
    {z : K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret //
      ¬ ∃ q : K.AttachedCosetVertex B.1,
        K.multiCosetInclude (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard.le)
          hgen hret B.1 B.2 q = z}

/-- The exact tagged vertex carrier of one actual singleton
type-(2) augmentation. Its root is an old multi-CE point
and the additional points are a freshly tagged B-coset. -/
abbrev rankTwoType2SingletonVertex
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (j : K.rankTwoType2SingletonIndex hcard hgen hret) :=
  IsolatedCosetGluing.Vertex
    (K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret)
    gen j.1.1
    (K.multiCosetAmbientValue (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le)
      hgen hret j.2.1)

/-- The completed EGraph for each genuine type-(2) index,
using the exact old quotient, attaching coset, and canonical
loop-only completion from the checked rank-two construction. -/
noncomputable def rankTwoType2SingletonStage
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (j : K.rankTwoType2SingletonIndex hcard hgen hret) :
    CompleteEGraph
      (K.rankTwoType2SingletonVertex hcard hgen hret j)
      (ActionEdge (K.rankTwoType2SingletonVertex hcard hgen hret j) ι) ι :=
  K.rankTwoOffComponentCompletedStage
    hcard hgen hret j.1.1 j.1.2 j.2.1 j.2.2

/-- Literal dependent disjoint complete ACTION of all actual
off-component type-(2) singleton stages. The stage tag is
retained in the sigma carrier; this action re-encodes edges
as signed action tokens but changes no componentwise steps. -/
noncomputable def rankTwoType2SingletonFamilyStage
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    CompleteEGraph
      (Σ j : K.rankTwoType2SingletonIndex hcard hgen hret,
        K.rankTwoType2SingletonVertex hcard hgen hret j)
      (ActionEdge
        (Σ j : K.rankTwoType2SingletonIndex hcard hgen hret,
          K.rankTwoType2SingletonVertex hcard hgen hret j) ι) ι :=
  dependentDisjointStage
    (fun j => K.rankTwoType2SingletonStage hcard hgen hret j)

/-- A genuine rank-one word-kernel statement for the WHOLE
dependent family, not merely its separate fibres. It remains
valid if the family has no off-component singleton stages. -/
theorem rankTwoType2SingletonFamily_rankOne_wordValue_eq_one
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι)
    (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (K.rankTwoType2SingletonFamilyStage hcard hgen hret).wordValue w = 1 := by
  apply (dependentDisjointStage_wordValue_eq_one_iff
    (fun j => K.rankTwoType2SingletonStage hcard hgen hret j) w).mpr
  intro j
  exact K.rankTwoOffComponentCompletedStage_rankOne_wordValue_eq_one
    hcard hgen hret j.1.1 j.1.2 j.2.1 j.2.2
    C hCcard w hw hval

variable [Finite Γ]

/-- There are FINITELY many actual choices of selected
proper alphabet and off-component singleton root, when
the ambient ABO group Γ is finite. -/
theorem finite_rankTwoType2SingletonIndex
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Finite (K.rankTwoType2SingletonIndex hcard hgen hret) := by
  classical
  letI : Finite
      (K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret) :=
    K.finite_allProperMultiCosetVertex
      (K.admissible_of_card_le_two hcard.le) hgen hret
  change Finite
    (Σ B : {B : Finset ι // B ∈ (allProperCosetFamily A).alphabets},
      {z : K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret //
        ¬ ∃ q : K.AttachedCosetVertex B.1,
          K.multiCosetInclude (allProperCosetFamily A)
            (K.admissible_of_card_le_two hcard.le)
            hgen hret B.1 B.2 q = z})
  exact @Finite.instSigma _ _
    (inferInstance : Finite
      {B : Finset ι // B ∈ (allProperCosetFamily A).alphabets})
    (fun _ => inferInstance)

/-- Every fibre of the genuine type-(2) family is finite
as a tagged carrier; neither old quotient nor new coset
is replaced by its ambient coordinate set. -/
theorem finite_rankTwoType2SingletonVertex
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (j : K.rankTwoType2SingletonIndex hcard hgen hret) :
    Finite (K.rankTwoType2SingletonVertex hcard hgen hret j) :=
  K.finite_rankTwoOffComponentCarrier
    hcard hgen hret j.1.1 j.2.1

/-- The full finite dependent disjoint carrier of actual
type-(2) singleton augmented rank-two stages. -/
theorem finite_rankTwoType2SingletonFamilyCarrier
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Finite
      (Σ j : K.rankTwoType2SingletonIndex hcard hgen hret,
        K.rankTwoType2SingletonVertex hcard hgen hret j) := by
  classical
  exact @Finite.instSigma _ _
    (K.finite_rankTwoType2SingletonIndex hcard hgen hret)
    (fun j => K.finite_rankTwoType2SingletonVertex hcard hgen hret j)

/-- The assembled family has an actual FINITE transition
group, regardless of whether some generators are trivial
or different singleton stages share ambient Γ-coordinates. -/
theorem finite_rankTwoType2SingletonFamilyTransitionGroup
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Finite (K.rankTwoType2SingletonFamilyStage
      hcard hgen hret).transitionGroup := by
  classical
  letI : Finite
      (Σ j : K.rankTwoType2SingletonIndex hcard hgen hret,
        K.rankTwoType2SingletonVertex hcard hgen hret j) :=
    K.finite_rankTwoType2SingletonFamilyCarrier hcard hgen hret
  letI : Fintype
      (Σ j : K.rankTwoType2SingletonIndex hcard hgen hret,
        K.rankTwoType2SingletonVertex hcard hgen hret j) :=
    Fintype.ofFinite _
  exact (K.rankTwoType2SingletonFamilyStage
    hcard hgen hret).finite_transitionGroup

end CayleySubgraphSpec
end ABO
end PSTSEPPA
