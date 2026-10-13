import PSTSEPPA.ABO.AllLocalRankTwoCayleySkeletons
import PSTSEPPA.ABO.RankTwoThreeFamilyStableCover
import PSTSEPPA.ABO.DependentDisjointStages

/-!
# Every local rank-two type-(1) augmented-cluster stage occurs in G₂'s actual catalogue

The corrected ABO Definition-5.3 stage family Z₁ includes
type-(1) augmented A-clusters. The finite all-local G₂
catalogue indexes *every* pair (A,K), where |A|=2 and K
is an actual potentially incomplete Γ[A]-Cayley skeleton.
For each such K, its three-family complete action includes
the SAME type-(1) augmented-cluster family, independent of K.

Rather than assuming an arbitrary Cayley skeleton exists,
we construct a literal edgeless full-vertex skeleton K₀ at
each two-letter A. This is a genuine CayleySubgraphSpec:
it retains every group vertex, has NO old signed edges,
and satisfies all closure/label axioms vacuously.

Consequently every genuine type-(1) augmented-cluster
stage over Γ[A] occurs at the explicit (A,K₀) index of
the finite all-local G₂ supercatalogue. No choice of
coset representatives, restriction on generators, or
source-dependent extra stage is needed.

The naturality lemma below is at the level of the ACTUAL
signed complete action, not merely a set-theoretic label:
following any signed word inside an anchored type-(1)
augmented cluster gives exactly the corresponding endpoint
in the complete disjoint catalogue. This includes inverse
letters and loops; all distinct outer/inner tags remain.
This does NOT by itself prove that every original H₁
source Definition-5.3 type-(1) augmentation has been
identified with this Γ[A] model; that source translation
and general corrected Condition 5.2 remain separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- A canonical, literal Γ[A]-Cayley skeleton with ALL group
vertices and NO signed edges. This is valid even for
trivial/repeated generators and arbitrary finite A. -/
def edgelessFullVertexLocalSkeleton
    (gen : ι → Γ) (A : Finset ι) :
    CayleySubgraphSpec (trivialCompletionGenerator gen A) A where
  vertices := Set.univ
  edges := ∅
  source_mem := by
    intro e he
    cases he
  inv_mem := by
    intro e he
    cases he
  label_mem := by
    intro e he
    cases he

/-- A completely EXPLICIT pair (A,K₀) of the exact finite
all-local rank-two Cayley skeleton catalogue used by
the original-source G₂, for each |A|=2. -/
def type1LocalG2CatalogueSkeletonIndex
    (gen : ι → Γ) (A : Finset ι) (hcard : A.card = 2) :
    AllLocalRankTwoSkeletonIndex gen :=
  ⟨⟨A, hcard⟩, edgelessFullVertexLocalSkeleton gen A⟩

/-- The actual dependent disjoint vertex carrier of the
all-local rank-two THREE-family action defining G₂. -/
abbrev type1LocalG2CatalogueVertex
    (gen : ι → Γ) (hret : KRetractable gen 2) :=
  rankTwoIndexedAmbientVertex
    (gen := gen)
    (fun j : AllLocalRankTwoSkeletonIndex gen =>
      allLocalRankTwoAlphabet j)
    (fun j => allLocalRankTwoAlphabet_card j)
    (fun j => allLocalRankTwoSkeleton j)
    hret

/-- Embed every old/new vertex of an actual completed
type-(1) augmented-cluster stage, tagged by its original
(P,D,v), into the precise three-family completed stage
at the chosen local skeleton index (A,K₀).

The two internal sum constructors select the type-(1)
stage family rather than the plain CE or type-(2) one. -/
noncomputable def type1StageVertexIntoAllLocalG2
    (gen : ι → Γ) (hret : KRetractable gen 2)
    (A : Finset ι) (hcard : A.card = 2)
    (x : Σ j : ClusterSpec.augmentedType1Index
      (trivialCompletionGenerator gen A) A,
        ClusterSpec.augmentedType1Vertex j) :
    type1LocalG2CatalogueVertex gen hret :=
  ⟨type1LocalG2CatalogueSkeletonIndex gen A hcard,
    Sum.inr (Sum.inl x)⟩

/-- The type-(1) augmented cluster source has EXACTLY
the same signed-word action in the genuine finite all-local
G₂ stage catalogue, including negative generators,
rooted coset edges and legal fixed-point loops. -/
theorem type1StageVertexIntoAllLocalG2_followWord
    (gen : ι → Γ) (hret : KRetractable gen 2)
    (A : Finset ι) (hcard : A.card = 2)
    (x : Σ j : ClusterSpec.augmentedType1Index
      (trivialCompletionGenerator gen A) A,
        ClusterSpec.augmentedType1Vertex j)
    (w : LabelWord ι) :
    (allLocalRankTwoStage (gen := gen) hret).followWord
      (type1StageVertexIntoAllLocalG2 gen hret A hcard x) w =
    type1StageVertexIntoAllLocalG2 gen hret A hcard
      ((ClusterSpec.augmentedType1FamilyStage
          (trivialCompletionGenerator gen A) A).followWord x w) := by
  let K0 := edgelessFullVertexLocalSkeleton gen A
  let j0 := type1LocalG2CatalogueSkeletonIndex gen A hcard
  let hgen := isGenerated_trivialCompletionGenerator gen A
  let hretL := retractable_trivialCompletionGenerator_of_kRetractable
    gen 2 hret A hcard.le
  let T0 := K0.allProperCompletedStage
    (K0.admissible_of_card_le_two hcard.le)
    hgen hretL hcard.ge
  let T1 := ClusterSpec.augmentedType1FamilyStage
    (trivialCompletionGenerator gen A) A
  let T2 := K0.rankTwoType2SingletonFamilyStage
    hcard hgen hretL
  change
    (dependentDisjointStage (fun j : AllLocalRankTwoSkeletonIndex gen =>
      (allLocalRankTwoSkeleton j).rankTwoAmbientLocalStage
        (allLocalRankTwoAlphabet_card j) hret)).followWord
      (⟨j0, Sum.inr (Sum.inl x)⟩ : type1LocalG2CatalogueVertex gen hret) w =
    (⟨j0, Sum.inr (Sum.inl (T1.followWord x w))⟩ :
      type1LocalG2CatalogueVertex gen hret)
  rw [dependentDisjointStage_followWord]
  change
    (⟨j0, (T0.disjointUnion (T1.disjointUnion T2)).followWord
      (Sum.inr (Sum.inl x)) w⟩ :
      type1LocalG2CatalogueVertex gen hret) =
    (⟨j0, Sum.inr (Sum.inl (T1.followWord x w))⟩ :
      type1LocalG2CatalogueVertex gen hret)
  rw [CompleteEGraph.disjointUnion_followWord_inr,
      CompleteEGraph.disjointUnion_followWord_inl]

end ABO
end PSTSEPPA
