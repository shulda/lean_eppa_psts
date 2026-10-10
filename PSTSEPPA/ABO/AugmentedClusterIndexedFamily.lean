import PSTSEPPA.ABO.AugmentedClusterRankOneKernel
import PSTSEPPA.ABO.DependentDisjointStages
import PSTSEPPA.ABO.FiniteRankTwoType2Stages

/-!
# The finite indexed family of genuine augmented-cluster type-(1) stages

ABO Section 5 / Definition 5.3 includes type-(1) augmented clusters.
The completed augmented-cluster graph and its singleton word kernel
are certified individually, but the finite family and its
componentwise synchronized action must be explicitly constructed.

We take a conservative finite superfamily of actual type-(1)
objects inside ONE labelled ambient group Γ:
* all finite ClusterSpec P of proper subalphabets of A;
* all proper augmentation alphabets D⊂A;
* each selected attachment basepoint v in the REAL cluster P.

Every index gives the literal complete action on the genuine
augmented Cayley subgraph P∪vG[D]. Assemble these stages on a
tagged dependent sigma carrier via the certified
dependentDisjointStage construction. All rank-one ambient
identity words act trivially on this ENTIRE assembled action.

For finite ambient Γ both the index set and every stage carrier
are finite, so the dependent union and its transition group
are finite. We retain literal old cluster membership and
do not identify distinct stages sharing ambient coordinates.

This superfamily need not coincide with source Z₁'s restricted
selection for the H₁-cover; no finite H₁-cover, G₂→H₁ quotient
or higher-rank reflection is claimed here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

/-- The entire type of finite families of proper subalphabets
of a finite alphabet A is itself finite. The property proof
does not count as additional data. -/
theorem finite_clusterSpec (A : Finset ι) :
    Finite (ClusterSpec A) := by
  classical
  apply Finite.of_injective (fun P : ClusterSpec A => P.pieces)
  intro P Q hpq
  cases P with
  | mk pieces hproper =>
    cases Q with
    | mk qpieces qproper =>
      dsimp at hpq
      cases hpq
      rfl

namespace ClusterSpec

/-- Actual augmented-cluster stage choices. We retain the
cluster P, a proper attached alphabet D⊂A, and an OLD
cluster vertex v witnessing that the augmentation is based
inside P. No arbitrary ambient vertex is silently called
an anchored stage. -/
abbrev augmentedType1Index (gen : ι → Γ) (A : Finset ι) :=
  Σ P : ClusterSpec A,
    Σ D : {D : Finset ι // D ⊂ A},
      {v : Γ // v ∈ P.VertexSet gen}

/-- Literal stage carrier for one anchored augmented cluster.
It is the old cluster plus the entire ambient D-coset,
without replacing the graph by abstract permutations. -/
abbrev augmentedType1Vertex
    (j : augmentedType1Index gen A) :=
  (j.1.augmentedCayleySubgraph
    gen j.2.1.1 j.2.1.2.subset j.2.2.1).Vertex

/-- Every index corresponds to the true complete
trivial-loop completion of its augmented-cluster graph. -/
noncomputable def augmentedType1Stage
    (j : augmentedType1Index gen A) :
    CompleteEGraph
      (augmentedType1Vertex j)
      (ActionEdge (augmentedType1Vertex j) ι) ι :=
  j.1.augmentedTrivialStage
    (gen := gen) j.2.1.1 j.2.1.2.subset j.2.2.1

/-- A single complete dependent ACTION graph for all
anchored augmented type-(1) clusters, retaining the
actual P,D,v stage tag of every vertex. -/
noncomputable def augmentedType1FamilyStage
    (gen : ι → Γ) (A : Finset ι) :
    CompleteEGraph
      (Σ j : augmentedType1Index gen A, augmentedType1Vertex j)
      (ActionEdge
        (Σ j : augmentedType1Index gen A, augmentedType1Vertex j) ι) ι :=
  dependentDisjointStage (fun j => augmentedType1Stage j)

/-- All ambient identity-valued ≤1-letter words are trivial
on the WHOLE dependent type-(1) family action, even when
there are no anchored cluster stages at all. -/
theorem augmentedType1Family_rankOne_wordValue_eq_one
    (gen : ι → Γ) (A : Finset ι)
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (augmentedType1FamilyStage gen A).wordValue w = 1 := by
  apply (dependentDisjointStage_wordValue_eq_one_iff
    (fun j => augmentedType1Stage j) w).mpr
  intro j
  exact j.1.augmentedTrivialStage_rankOne_wordValue_eq_one
    (gen := gen) j.2.1.1 j.2.1.2.subset j.2.2.1
    C hCcard w hw hval

variable [Finite Γ]

/-- The concrete family of all P,D and old anchored v is
FINITE when ambient Γ is finite. This includes the finite
universe of allowed ClusterSpec objects and their old vertices. -/
theorem finite_augmentedType1Index
    (gen : ι → Γ) (A : Finset ι) :
    Finite (augmentedType1Index gen A) := by
  classical
  change Finite
    (Σ P : ClusterSpec A,
      Σ D : {D : Finset ι // D ⊂ A},
        {v : Γ // v ∈ P.VertexSet gen})
  exact @Finite.instSigma _ _ (finite_clusterSpec A)
    (fun _ => @Finite.instSigma _ _
      (inferInstance : Finite {D : Finset ι // D ⊂ A})
      (fun _ => inferInstance))

/-- Every actual augmented-cluster vertex carrier is finite
as a subtype of the ambient Γ, without needing an effective
enumeration of its algebraically defined union of cosets. -/
theorem finite_augmentedType1Vertex
    (j : augmentedType1Index gen A) :
    Finite (augmentedType1Vertex j) := by
  classical
  apply Finite.of_injective
    (fun x : augmentedType1Vertex j => x.1)
  intro x y hxy
  exact Subtype.ext hxy

/-- All type-(1) completed stages form a FINITE dependent
disjoint action carrier, with actual stage tags preserved. -/
theorem finite_augmentedType1FamilyCarrier
    (gen : ι → Γ) (A : Finset ι) :
    Finite (Σ j : augmentedType1Index gen A,
      augmentedType1Vertex j) := by
  classical
  exact @Finite.instSigma _ _
    (finite_augmentedType1Index gen A)
    (fun j => finite_augmentedType1Vertex j)

/-- Therefore the true generated transition group of the
assembled finite family of augmented clusters is finite,
with no assumption of faithful or distinct generators. -/
theorem finite_augmentedType1FamilyTransitionGroup
    (gen : ι → Γ) (A : Finset ι) :
    Finite (augmentedType1FamilyStage gen A).transitionGroup := by
  classical
  letI : Finite (Σ j : augmentedType1Index gen A,
      augmentedType1Vertex j) :=
    finite_augmentedType1FamilyCarrier gen A
  letI : Fintype (Σ j : augmentedType1Index gen A,
      augmentedType1Vertex j) := Fintype.ofFinite _
  exact (augmentedType1FamilyStage gen A).finite_transitionGroup

end ClusterSpec
end ABO
end PSTSEPPA
