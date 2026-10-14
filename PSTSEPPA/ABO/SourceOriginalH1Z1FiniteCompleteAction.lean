import PSTSEPPA.ABO.SourceOriginalH1Z1ThreeFamilyAction
import PSTSEPPA.ABO.FiniteRankTwoType2Stages
import PSTSEPPA.ABO.FiniteActionStages

/-!
# Finiteness of the literal original H₁ Z₁ three-family complete signed action

The exact source rank-one complete stage assembly is indexed by every
original rooted H₁-cover component's plain full-proper-coset
extension, all original anchored type-(1) augmented clusters,
and all actual (B,z) type-(2) augmented full-coset extensions.

The source's actual H₁ is finite. Each old Cayley skeleton and
full tagged coset quotient has finitely many vertices; adding a
full B-coset creates only finitely many fresh points. All type-(1)
cluster carrier subtypes are likewise finite. Since the genuine
three-family index is finite, its dependent disjoint union
has a finite vertex carrier, and hence its complete signed
transition group is finite as a subgroup of the permutation group.

No arbitrary representatives of quotient coset tags are selected;
no ambient-coordinate collapse occurs. The result strengthens the
source-first-rank finite-G₂ action certificate; it is not a
claim about the original paper's full higher-rank induction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Every INDIVIDUAL genuine original H₁ completed source
stage has finitely many old/fresh tagged vertices. Includes
all three source-stage kinds and B=∅. -/
theorem finite_sourceOriginalH1Z1StageVertex
    (src dst : ι → V)
    (j : sourceOriginalH1Z1ThreeFamilyIndex src dst) :
    Finite (sourceOriginalH1Z1StageVertex src dst j) := by
  classical
  letI : Finite (SourceH1 src dst) := finite_sourceH1 src dst
  cases j with
  | inl j =>
      change Finite
        (sourceOriginalH1PlainActionDatum src dst j).Carrier
      infer_instance
  | inr j =>
      cases j with
      | inl j =>
          change Finite (ClusterSpec.augmentedType1Vertex j.2)
          exact ClusterSpec.finite_augmentedType1Vertex j.2
      | inr j =>
          change Finite
            (sourceOriginalH1Type2ActionDatum src dst j).Carrier
          infer_instance

/-- The entire actual dependent disjoint ORIGINAL rank-one
H₁ source Z₁ three-kind complete action has a FINITE
vertex carrier, regardless of empty or repeated source indices. -/
theorem finite_sourceOriginalH1Z1ThreeFamilyVertex
    (src dst : ι → V) :
    Finite (SourceOriginalH1Z1Vertex src dst) := by
  classical
  letI : Finite (sourceOriginalH1Z1ThreeFamilyIndex src dst) :=
    finite_sourceOriginalH1Z1ThreeFamilyIndex src dst
  exact @Finite.instSigma _ _
    (finite_sourceOriginalH1Z1ThreeFamilyIndex src dst)
    (fun j => finite_sourceOriginalH1Z1StageVertex src dst j)

/-- The transition group of the ACTUAL original source Z₁
three-kind finite signed complete action is itself FINITE,
with no need for faithful or distinct generator labels. -/
theorem finite_sourceOriginalH1Z1ThreeFamilyTransitionGroup
    (src dst : ι → V) :
    Finite (sourceOriginalH1Z1ThreeFamilyStage src dst).transitionGroup := by
  classical
  letI : Finite (SourceOriginalH1Z1Vertex src dst) :=
    finite_sourceOriginalH1Z1ThreeFamilyVertex src dst
  letI : Fintype (SourceOriginalH1Z1Vertex src dst) :=
    Fintype.ofFinite _
  exact (sourceOriginalH1Z1ThreeFamilyStage src dst).finite_transitionGroup

end ABO
end PSTSEPPA
