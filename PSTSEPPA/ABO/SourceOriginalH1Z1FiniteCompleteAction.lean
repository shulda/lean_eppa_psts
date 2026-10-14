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

/-- The exact dependent-Sigma carrier of the true original
three-kind source stage family, independently of any later
Cayley-cover shorthand or representative choice. -/
abbrev sourceOriginalH1Z1ThreeFamilyCarrier
    (src dst : ι → V) :=
  Σ j : sourceOriginalH1Z1ThreeFamilyIndex src dst,
    sourceOriginalH1Z1StageVertex src dst j

/-- The TRUE rooted ambient full proper-coset quotient is finite
when its ambient group is finite and only two-letter retractability
is known. Transfer finiteness from the local subgroup multi-coset
quotient across the certified exact component-tagged equivalence;
do NOT identify source coset vertices by ambient coordinates. -/
theorem finite_rootedAmbientAllProperSourceVertex
    {Γ : Type*} [Group Γ] [Finite Γ]
    {gen : ι → Γ} {S : Finset ι}
    (K : CayleySubgraphSpec gen S)
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex) :
    Finite (Quotient
      (K.rootedAmbientMultiCosetSetoid A hcard hret root
        (allProperCosetFamily A))) := by
  classical
  letI : Finite (generatedSubgroup gen A) := inferInstance
  let L := K.intrinsicComponentLocalSlice A root
  letI : Finite
      (L.MultiCosetVertex (allProperCosetFamily A)
        (L.admissible_of_card_le_two hcard.le)
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le)) :=
    L.finite_allProperMultiCosetVertex
      (L.admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le)
  exact Finite.of_surjective
    (K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret root
      (allProperCosetFamily A))
    (K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret root
      (allProperCosetFamily A)).surjective

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
      exact finite_rootedAmbientAllProperSourceVertex
        ((sourceCoverIndexSkeleton src dst j).restrictAlphabet j.2.1.1)
        j.2.1.1 j.2.1.2
        (sourceH1_twoRetractable src dst)
        (sourceCoverIndexRoot src dst j)
  | inr j =>
      cases j with
      | inl j =>
          change Finite (ClusterSpec.augmentedType1Vertex j.2)
          exact ClusterSpec.finite_augmentedType1Vertex j.2
      | inr j =>
          change Finite
            (sourceOriginalH1Type2ActionDatum src dst j).Carrier
          let t := j.1
          let A := t.2.1.1
          let K := (sourceCoverIndexSkeleton src dst t).restrictAlphabet A
          let root := sourceCoverIndexRoot src dst t
          let hret := sourceH1_twoRetractable src dst
          letI : Finite
              (Quotient (K.rootedAmbientMultiCosetSetoid
                A t.2.1.2 hret root (allProperCosetFamily A))) :=
            finite_rootedAmbientAllProperSourceVertex
              K A t.2.1.2 hret root
          -- Expose the *actual* old/fresh disjoint carrier of the
          -- rooted, translated source augmentation. The ambient
          -- group and the tagged old quotient are both finite.
          change Finite (IsolatedCosetGluing.Vertex
            (Quotient (K.rootedAmbientMultiCosetSetoid
              A t.2.1.2 hret root (allProperCosetFamily A)))
            (sourceH1Generator src dst) j.2.1.1 _)
          dsimp only [IsolatedCosetGluing.Vertex,
            IsolatedCosetGluing.FreshPoint]
          infer_instance

/-- The entire actual dependent disjoint ORIGINAL rank-one
H₁ source Z₁ three-kind complete action has a FINITE
vertex carrier, regardless of empty or repeated source indices. -/
theorem finite_sourceOriginalH1Z1ThreeFamilyVertex
    (src dst : ι → V) :
    Finite (sourceOriginalH1Z1ThreeFamilyCarrier src dst) := by
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
  letI : Finite (sourceOriginalH1Z1ThreeFamilyCarrier src dst) :=
    finite_sourceOriginalH1Z1ThreeFamilyVertex src dst
  letI : Fintype (sourceOriginalH1Z1ThreeFamilyCarrier src dst) :=
    Fintype.ofFinite _
  exact (sourceOriginalH1Z1ThreeFamilyStage src dst).finite_transitionGroup

end ABO
end PSTSEPPA
