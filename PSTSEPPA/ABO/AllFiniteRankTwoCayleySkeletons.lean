import PSTSEPPA.ABO.RankTwoThreeFamilyStableCover
import PSTSEPPA.ABO.UniversalStageRealCayleyCover
import PSTSEPPA.ABO.StabilityRetractability

/-!
# Enumerate ALL genuine finite rank-two Cayley skeletons, not just chosen covers

For a finite labelled group Γ and a two-letter alphabet A, there
are only finitely many literal incomplete A-labelled Cayley
subgraphs K: each is determined by finite vertex and signed
edge subsets, satisfying propositional source/inverse/label
closure conditions.

Rather than attempting to select the exact H1-cover graphs
from source Definition 5.3, build a REDUNDANT family consisting
of EVERY such genuine K and all three Lean-certified completed
rank-two stage types for that K. The resulting dependent Sigma
action retains the actual K-tag and full internal quotient tags.
Each stage has already passed its rank-one signed-word kernel,
so the entire all-K group is a genuine 1-stable synchronized
group; it is 2-retractable if Γ is retractable, and finite
when Γ is finite.

Every admissible source H1-cover that is already a genuine
Cayley-embedded K is thereby represented among these indices.
Showing every source Z1 cover has the required local Cayley-K
presentation and matching augmented completions remains a
separate geometric obligation, as does extending the argument
to all cosets and all two-letter alphabets in a non-globally
retractable H1.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι]
variable [Group Γ]

/-- A Cayley skeleton is completely determined by its LITERAL
vertex and signed-edge subsets. All its compatibility axioms
are propositions, hence proof-irrelevant. -/
theorem CayleySubgraphSpec.ext_vertices_edges
    {gen : ι → Γ} {A : Finset ι}
    {K L : CayleySubgraphSpec gen A}
    (hv : K.vertices = L.vertices)
    (he : K.edges = L.edges) : K = L := by
  cases K with
  | mk kv ke ks ki kl =>
      cases L with
      | mk lv le ls li ll =>
          cases hv
          cases he
          rfl

variable [Finite Γ]

/-- The type of ALL legal incomplete A-labelled Cayley skeletons
over the finite group Γ is FINITE. Crucially this includes
disconnected skeletons, actual inverse edge tokens, loops and
all possibilities of missing edges; no chosen representatives
or completeness hypotheses are imposed. -/
theorem finite_allCayleySubgraphSpec
    (gen : ι → Γ) (A : Finset ι) :
    Finite (CayleySubgraphSpec gen A) := by
  classical
  letI : Fintype Γ := Fintype.ofFinite _
  letI : Fintype (ActionEdge Γ ι) := inferInstance
  apply Finite.of_injective
    (fun K : CayleySubgraphSpec gen A => (K.vertices, K.edges))
  intro K L h
  exact CayleySubgraphSpec.ext_vertices_edges
    (congrArg Prod.fst h) (congrArg Prod.snd h)

variable {gen : ι → Γ} {A : Finset ι}

/-- The full tagged vertex carrier of the source-related
three-family completed actions of EVERY real A-Cayley skeleton.
Its outer tag remembers K itself; the inner tags remember
which genuine geometric completion is being used. -/
abbrev allRankTwoSkeletonsVertex
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  Σ K : CayleySubgraphSpec gen A,
    K.rankTwoThreeFamilyVertex hcard hgen hret

/-- The actual signed complete graph assembled from all K,
preserving every raw and completed stage's true transitions.
The (potentially disconnected) K indices are not merged just
because they happen to represent equal elements of Γ. -/
noncomputable def allRankTwoSkeletonsStage
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    CompleteEGraph
      (allRankTwoSkeletonsVertex hcard hgen hret)
      (ActionEdge (allRankTwoSkeletonsVertex hcard hgen hret) ι) ι :=
  dependentDisjointStage
    (fun K : CayleySubgraphSpec gen A =>
      K.rankTwoThreeFamilyStage hcard hgen hret)

/-- Exact preservation of arbitrary signed paths from any
selected old vertex of an individual, genuine K completion
to the corresponding outer-tagged copy in the universal
all-K complete action. -/
theorem allRankTwoSkeletonsStage_followWord
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (K : CayleySubgraphSpec gen A)
    (x : K.rankTwoThreeFamilyVertex hcard hgen hret)
    (w : LabelWord ι) :
    (allRankTwoSkeletonsStage hcard hgen hret).followWord
      (⟨K, x⟩ : allRankTwoSkeletonsVertex hcard hgen hret) w =
      ⟨K, (K.rankTwoThreeFamilyStage hcard hgen hret).followWord x w⟩ := by
  exact dependentDisjointStage_followWord
    (fun K : CayleySubgraphSpec gen A =>
      K.rankTwoThreeFamilyStage hcard hgen hret) K x w

/-- Every ambient-identity word supported on at most one
letter acts trivially on EVERY actual completed stage of
EVERY admissible A-Cayley skeleton, including all three
geometric type families. -/
theorem allRankTwoSkeletonsStage_rankOneKernel
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hC : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hvalue : PSTS.SignedWord.evalGroup gen w = 1) :
    (allRankTwoSkeletonsStage hcard hgen hret).wordValue w = 1 := by
  apply (dependentDisjointStage_wordValue_eq_one_iff
    (fun K : CayleySubgraphSpec gen A =>
      K.rankTwoThreeFamilyStage hcard hgen hret) w).mpr
  intro K
  exact K.rankTwoThreeFamilyStage_rankOne_wordValue_eq_one
    hcard hgen hret C hC w hw hvalue

/-- ACTUAL finite synchronized group of Γ with the transition
subgroup generated by the all-K disjoint completed action. -/
noncomputable abbrev allRankTwoSkeletonsGroup
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  SynchronizedProduct.stageCover gen
    (allRankTwoSkeletonsStage hcard hgen hret)

/-- Its genuine generator-preserving surjective quotient onto Γ. -/
noncomputable def allRankTwoSkeletonsQuotient
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  SynchronizedProduct.stageCoverQuotient gen
    (allRankTwoSkeletonsStage hcard hgen hret) hgen

/-- The all-K synchronized quotient is 1-STABLE, independently
of the number of skeletons or their connectivity. -/
theorem allRankTwoSkeletonsQuotient_oneStable
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    (allRankTwoSkeletonsQuotient hcard hgen hret).KStable 1 := by
  apply SynchronizedProduct.stageCoverQuotient_kStable_of_stageKernel
    gen (allRankTwoSkeletonsStage hcard hgen hret) hgen 1
  intro C hC w hw hvalue
  exact allRankTwoSkeletonsStage_rankOneKernel
    hcard hgen hret C hC w hw hvalue

/-- The same genuinely constructed group is TWO-retractable by
the corrected rank-descent theorem, not by an assumed global
retractability property of its construction. -/
theorem allRankTwoSkeletonsGroup_twoRetractable
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    KRetractable
      (SynchronizedProduct.generator gen
        (allRankTwoSkeletonsStage hcard hgen hret).transitionSubgroupGenerator)
      2 := by
  exact (allRankTwoSkeletonsQuotient hcard hgen hret).
    kRetractable_of_retractable_target 1
      (allRankTwoSkeletonsQuotient_oneStable hcard hgen hret) hret

/-- The entire true outer-indexed carrier is finite. This is
stronger than finiteness of any one K stage, and uses the
actual finiteness of all vertex/edge subset choices. -/
theorem finite_allRankTwoSkeletonsVertex
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Finite (allRankTwoSkeletonsVertex hcard hgen hret) := by
  classical
  letI : Finite (CayleySubgraphSpec gen A) :=
    finite_allCayleySubgraphSpec gen A
  exact @Finite.instSigma _ _
    (inferInstance : Finite (CayleySubgraphSpec gen A))
    (fun K => K.finite_rankTwoThreeFamilyVertex hcard hgen hret)

/-- The all-K group is actually FINITE for every finite
generated retractable Γ; no list of source H1-covers
or classifying transversals is needed to construct it. -/
theorem finite_allRankTwoSkeletonsGroup
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Finite (allRankTwoSkeletonsGroup hcard hgen hret) := by
  classical
  letI : Finite (allRankTwoSkeletonsVertex hcard hgen hret) :=
    finite_allRankTwoSkeletonsVertex hcard hgen hret
  exact SynchronizedProduct.finite_stageCover gen
    (allRankTwoSkeletonsStage hcard hgen hret)

end ABO
end PSTSEPPA
