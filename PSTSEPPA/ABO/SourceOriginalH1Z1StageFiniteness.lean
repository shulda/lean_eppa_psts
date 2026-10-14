import PSTSEPPA.ABO.SourceH1Type2StageCatalogueIndex
import PSTSEPPA.ABO.AugmentedClusterIndexedFamily
import PSTSEPPA.ABO.SourceOriginalH1LocalCoverIndex

/-!
# Finiteness of all literal original H₁ rank-one Z₁ stage indices

The corrected first nontrivial source Z₁ stage family has two
augmented types: anchored proper-subalphabet clusters (P,D,v)
and completed H₁-cover full-coset B-augmentations (base,A,root,B,z).
The plain B=∅ (or unaugmented extension) cases are included in
the appropriate source-cover index family.

Finiteness is not assumed as a global axiom. It follows from
the REAL finite original-input dependent H₁ group, exact
finite original cover components, locally finite H₁[A] rank-two
type-(2) stage indices, and the canonical original/local
type-(2) (B,z) dependent index EQUIVALENCE.

This packages the genuine original-source index census used in
the first source Section-5 stage assembly. No stage is identified
merely by equal ambient H₁ group coordinates; all basepoints,
parent alphabets, roots, coset choices, and cluster tags remain
literal. General ranks and the content-reflecting group are not
addressed here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Every original type-(1) anchored augmentation index (A,P,D,v),
for an actual two-letter A and an old cluster anchor v in H₁[A],
is retained in a finite dependent index family. -/
abbrev sourceOriginalH1Type1Index (src dst : ι → V) :=
  Σ A : {A : Finset ι // A.card = 2},
    ClusterSpec.augmentedType1Index
      (sourceH1Generator src dst) A.1

/-- The actual original H₁ anchored augmented cluster index
universe is FINITE, including the stage and anchoring tags. -/
theorem finite_sourceOriginalH1Type1Index
    (src dst : ι → V) :
    Finite (sourceOriginalH1Type1Index src dst) := by
  classical
  letI : Finite (SourceH1 src dst) := finite_sourceH1 src dst
  exact @Finite.instSigma _ _ inferInstance
    (fun A => ClusterSpec.finite_augmentedType1Index
      (sourceH1Generator src dst) A.1)

/-- Every exact normalised local (B,z)-augmentation associated
with an ORIGINAL source H₁-cover component has a finite index
carrier. There are finitely many literal (base,A,root) triples,
and finitely many type-(2) B,z tags above each one. -/
theorem finite_sourceOriginalH1LocalG2Type2Index
    (src dst : ι → V) :
    Finite (sourceOriginalH1LocalG2Type2Index src dst) := by
  classical
  letI : Finite (SourceH1 src dst) := finite_sourceH1 src dst
  letI : Finite (SourceOriginalH1CoverIndex src dst) :=
    finite_SourceOriginalH1CoverIndex src dst
  exact @Finite.instSigma _ _
    (finite_SourceOriginalH1CoverIndex src dst)
    (fun j => by
      letI : Finite
          (generatedSubgroup
            (sourceH1Generator src dst) j.2.1.1) := inferInstance
      exact (sourceCoverIndexLocalSkeleton src dst j).finite_rankTwoType2SingletonIndex
        j.2.1.2
        (isGenerated_trivialCompletionGenerator
          (sourceH1Generator src dst) j.2.1.1)
        (retractable_trivialCompletionGenerator_of_kRetractable
          (sourceH1Generator src dst) 2
          (sourceH1_twoRetractable src dst)
          j.2.1.1 j.2.1.2.le))

/-- FINITENESS of the TRUE ORIGINAL H₁ type-(2) B-augmented
coset-extension index family, obtained via the exact previously
certified source/local bijection, not chosen coset representatives.
In particular no special B=∅ case is discarded. -/
theorem finite_sourceOriginalH1Type2AugmentationIndex
    (src dst : ι → V) :
    Finite (sourceOriginalH1Type2AugmentationIndex src dst) := by
  classical
  letI : Finite (sourceOriginalH1LocalG2Type2Index src dst) :=
    finite_sourceOriginalH1LocalG2Type2Index src dst
  exact Finite.of_injective
    (sourceOriginalH1Type2CatalogueIndexEquiv src dst)
    (sourceOriginalH1Type2CatalogueIndexEquiv src dst).injective

end ABO
end PSTSEPPA
