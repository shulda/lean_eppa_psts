import PSTSEPPA.ABO.SourceLiteralY1ThreeKindG2Action
import PSTSEPPA.ABO.SourceLiteralY1SelectedOffBFinite
import PSTSEPPA.ABO.FiniteActionStages
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum

/-!
# Genuine printed T(Y₁) three-kind first-rank finite stage census

The ACTUAL redundant all-choice first-rank family has exactly
three geometrically defined index summands: original-input rooted
plain P_A coset completions; genuine anchored augmented clusters;
and proper-B augmentations at OLD, component-tagged off-B quotient
vertices. Every index is finite, including the difficult third
kind, without discarding B=∅ or collapsing equal ambient coordinates.

We also prove that every genuine complete old/fresh stage carrier,
and the whole disjoint family carrier, is finite. The proofs use
the EXACT intersection-support quotient and its finite raw
component-tagged coset representatives, not an invalid ambient
coordinate injection. The signed formal edge carrier is finite.

This is the all-choice three-kind superfamily. Equivariant
selection of the exact corrected Definition-5.3 Z₁, higher-rank
Condition 5.2 and Theorem 4.7, the reflecting group and PSTS
EPPA remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Every true original input-rooted plain P_A stage index
(base, two-letter A, paper T(Y₁) root) occurs in a finite family. -/
theorem finite_sourceLiteralY1PlainStageIndex
    (src dst : ι → V) :
    Finite (sourceLiteralY1PlainStageIndex src dst) := by
  classical
  letI : Finite (sourceLiteralY1 src dst).transitionGroup :=
    finite_sourceLiteralY1TransitionGroup src dst
  infer_instance

/-- The ENTIRE genuine type-(2) indexed original printed family
is finite, retaining base, A, root, B, and the exact OLD off-B
tagged quotient root, including B=∅. -/
theorem finite_sourceLiteralY1Type2Index
    (src dst : ι → V) :
    Finite (sourceLiteralY1Type2Index src dst) := by
  classical
  change Finite
    (Σ base : V,
      Σ a : {A : Finset ι // A.card = 2},
        Σ root : (sourceLiteralY1 src dst).transitionGroup,
          Σ b : {B : Finset ι //
            B ∈ (allProperCosetFamily a.1).alphabets},
            LiteralPaperSelectedOffBPoint
              src dst base a.1 a.2 root b.1 b.2)
  exact @Finite.instSigma _ _ inferInstance
    (fun base => @Finite.instSigma _ _ inferInstance
      (fun a => @Finite.instSigma _ _
        (finite_sourceLiteralY1TransitionGroup src dst)
        (fun root => @Finite.instSigma _ _ inferInstance
          (fun b => finite_LiteralPaperSelectedOffBPoint
            src dst base a.1 a.2 root b.1 b.2))))

/-- One FINITE dependent index for the authentic printed
three-kind redundant first-rank action: plain, anchored
type-(1), and component-tagged off-B type-(2). -/
theorem finite_sourceLiteralY1ThreeKindIndex
    (src dst : ι → V) :
    Finite (sourceLiteralY1ThreeKindIndex src dst) := by
  classical
  letI : Finite (sourceLiteralY1PlainStageIndex src dst) :=
    finite_sourceLiteralY1PlainStageIndex src dst
  letI : Finite (sourceLiteralY1Type1Index src dst) :=
    finite_sourceLiteralY1Type1Index src dst
  letI : Finite (sourceLiteralY1Type2Index src dst) :=
    finite_sourceLiteralY1Type2Index src dst
  infer_instance

/-- Every ACTUAL original printed legally completed stage
is finite on its full old/fresh carrier, not only on its
ambient group-valued image. -/
theorem finite_sourceLiteralY1ThreeKindStageVertex
    (src dst : ι → V)
    (j : sourceLiteralY1ThreeKindIndex src dst) :
    Finite (sourceLiteralY1ThreeKindStageVertex src dst j) := by
  classical
  letI : Finite (sourceLiteralY1 src dst).transitionGroup :=
    finite_sourceLiteralY1TransitionGroup src dst
  cases j with
  | inl j =>
      change Finite (Quotient
        (sourceLiteralY1DirectRootMultiCosetSetoid
          src dst j.1 j.2.1.1 j.2.1.2 j.2.2
          (allProperCosetFamily j.2.1.1)))
      exact finite_literalPaperSelectedRoot_quotientVertices
        src dst j.1 j.2.1.1 j.2.1.2 j.2.2
  | inr j =>
      cases j with
      | inl j =>
          change Finite (ClusterSpec.augmentedType1Vertex j.2)
          exact ClusterSpec.finite_augmentedType1Vertex j.2
      | inr j =>
          letI : Finite (Quotient
              (sourceLiteralY1DirectRootMultiCosetSetoid
                src dst j.1 j.2.1.1 j.2.1.2 j.2.2.1
                (allProperCosetFamily j.2.1.1))) :=
            finite_literalPaperSelectedRoot_quotientVertices
              src dst j.1 j.2.1.1 j.2.1.2 j.2.2.1
          change Finite (sourceLiteralY1Type2StageVertex src dst j)
          dsimp only [sourceLiteralY1Type2StageVertex,
            IsolatedCosetGluing.Vertex, IsolatedCosetGluing.FreshPoint]
          infer_instance

/-- The true tagged vertex carrier of the complete three-kind
printed first-rank action, including every redundant index. -/
abbrev SourceLiteralY1ThreeKindVertex
    (src dst : ι → V) :=
  Σ j : sourceLiteralY1ThreeKindIndex src dst,
    sourceLiteralY1ThreeKindStageVertex src dst j

/-- Finite whole three-kind genuine printed completed stage
carrier: no assumption of ambient-coordinate injectivity. -/
theorem finite_sourceLiteralY1ThreeKindVertex
    (src dst : ι → V) :
    Finite (SourceLiteralY1ThreeKindVertex src dst) := by
  classical
  exact @Finite.instSigma _ _
    (finite_sourceLiteralY1ThreeKindIndex src dst)
    (fun j => finite_sourceLiteralY1ThreeKindStageVertex src dst j)

/-- The formal directed signed action-edge tokens of the
actual combined original printed complete three-kind stage
form a finite type, including inverse and fixed-loop tokens. -/
theorem finite_sourceLiteralY1ThreeKindActionEdge
    (src dst : ι → V) :
    Finite (ActionEdge (SourceLiteralY1ThreeKindVertex src dst) ι) := by
  classical
  letI : Finite (SourceLiteralY1ThreeKindVertex src dst) :=
    finite_sourceLiteralY1ThreeKindVertex src dst
  letI : Fintype (SourceLiteralY1ThreeKindVertex src dst) :=
    Fintype.ofFinite _
  exact finite_actionEdge

end ABO
end PSTSEPPA
