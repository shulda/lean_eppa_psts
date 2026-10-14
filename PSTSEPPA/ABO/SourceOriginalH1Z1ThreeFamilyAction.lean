import PSTSEPPA.ABO.SourceH1AllType1G2WordAction
import PSTSEPPA.ABO.SourceH1Type2ActualG2WordAction
import PSTSEPPA.ABO.SourceH1PlainActualG2WordAction
import PSTSEPPA.ABO.SourceOriginalH1Z1StageFiniteness
import PSTSEPPA.ABO.DependentDisjointWordCongruence

/-!
# One literal dependent source H₁ rank-one Z₁ three-family complete action

At the first nontrivial corrected ABO rank, the true original source
stages occur in three geometric kinds:
0. the genuine rooted original H₁ full proper-coset completion;
1. an anchored original ambient augmented proper-alphabet cluster;
2. a rooted original B-augmentation at a component-tagged off-B
   quotient point of an actual original H₁ preimage component.

Here we retain every original index, old/new coset-quotient vertex
and completed signed edge, and assemble their original COMPLETE
actions into a SINGLE dependent disjoint graph. This does not
quotient distinct old vertices with equal ambient H₁ group values.

The already independently Lean-audited source-specific theorems
imply that equality of group-word values in the ACTUAL finite
input-dependent second group G₂ forces equality of complete
signed-word endpoints at ALL VERTICES of this entire assembled
three-family action. This is stronger than separate local stage
inclusions: it packages a genuinely source-indexed G₂-action
certificate for the entire stated three-family supercatalogue.

The source's exact Definition-5.3 Z₁ selection and subsequent
Condition 5.2 / Theorem 4.7 geometry are separate scope gates.
No general higher-rank stage induction or PSTS EPPA is asserted.
-/

namespace PSTSEPPA
namespace ABO

universe uι uV

/-- An actual complete SIGNED action with explicit carrier, whose
directed edge tokens are exactly vertex-and-signed-label pairs,
including distinct positive/negative tokens at fixed loops. -/
structure SourceCompleteActionDatum (ι : Type uι) where
  Carrier : Type (max uι uV)
  stage : CompleteEGraph Carrier (ActionEdge Carrier ι) ι

variable {ι : Type uι} {V : Type uV}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The exact three-way tagged original source rank-one
stage index, including all (base,A,root,B,z) and (A,P,D,v)
tags. It is a finite superfamily even when some kinds are empty. -/
abbrev sourceOriginalH1Z1ThreeFamilyIndex (src dst : ι → V) :=
  (SourceOriginalH1CoverIndex src dst) ⊕
    ((sourceOriginalH1Type1Index src dst) ⊕
      (sourceOriginalH1LocalG2Type2Index src dst))

/-- There are only finitely many REAL source stage indices in
the entire three-way family; no unproved representative system
or external source-cover enumeration is postulated. -/
theorem finite_sourceOriginalH1Z1ThreeFamilyIndex
    (src dst : ι → V) :
    Finite (sourceOriginalH1Z1ThreeFamilyIndex src dst) := by
  classical
  letI : Finite (SourceOriginalH1CoverIndex src dst) :=
    finite_SourceOriginalH1CoverIndex src dst
  letI : Finite (sourceOriginalH1Type1Index src dst) :=
    finite_sourceOriginalH1Type1Index src dst
  letI : Finite (sourceOriginalH1LocalG2Type2Index src dst) :=
    finite_sourceOriginalH1LocalG2Type2Index src dst
  infer_instance

/-- The true original source-rooted UN-AUGMENTED complete P_A
stage, not merely its generated-subgroup catalogue model. -/
noncomputable def sourceOriginalH1PlainActionDatum
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :
    SourceCompleteActionDatum.{uι, uV} ι :=
  { Carrier := _
    stage :=
      ((sourceCoverIndexSkeleton src dst j).restrictAlphabet
        j.2.1.1).rootedAmbientAllProperCompletedStage
        j.2.1.1 j.2.1.2
        (sourceH1_twoRetractable src dst)
        (sourceCoverIndexRoot src dst j) }

/-- One literal anchored ambient H₁ augmented-cluster source
action, with original (P,D,v) index and old/new vertices. -/
noncomputable def sourceOriginalH1Type1ActionDatum
    (src dst : ι → V)
    (j : sourceOriginalH1Type1Index src dst) :
    SourceCompleteActionDatum.{uι, uV} ι :=
  { Carrier := ClusterSpec.augmentedType1Vertex j.2
    stage := ClusterSpec.augmentedType1Stage j.2 }

/-- One genuine root-TRANSLATED original H₁ B-augmented
complete full-coset source action at its exact tagged (B,z)
stage index. The separately main-certified named/source
dependent HEq identifies this translated action with the
source's original named ambient-anchor presentation. -/
noncomputable def sourceOriginalH1Type2ActionDatum
    (src dst : ι → V)
    (j : sourceOriginalH1LocalG2Type2Index src dst) :
    SourceCompleteActionDatum.{uι, uV} ι := by
  let t := j.1
  let k := j.2
  let A := t.2.1.1
  let hcard := t.2.1.2
  let K := (sourceCoverIndexSkeleton src dst t).restrictAlphabet A
  let hret := sourceH1_twoRetractable src dst
  let root := sourceCoverIndexRoot src dst t
  let hOff := (K.rootedLocalMultiCosetOffCoset_iff
    A hcard hret root (allProperCosetFamily A)
    k.1.1 k.1.2 k.2.1).mp k.2.2
  exact
    { Carrier := _
      stage := K.rootedTranslatedSourceOffCosetCompletedStage
        A hcard hret root k.1.1 k.1.2 k.2.1 hOff }

/-- All three genuine ORIGINAL source stage kinds share
the same exact complete signed graph interface. No action
fibre is replaced by ambient H₁ coordinates. -/
noncomputable def sourceOriginalH1Z1ActionDatum
    (src dst : ι → V) :
    sourceOriginalH1Z1ThreeFamilyIndex src dst →
      SourceCompleteActionDatum.{uι, uV} ι
  | .inl j => sourceOriginalH1PlainActionDatum src dst j
  | .inr (.inl j) => sourceOriginalH1Type1ActionDatum src dst j
  | .inr (.inr j) => sourceOriginalH1Type2ActionDatum src dst j

/-- The exact original source completed vertex carrier in
one fixed original stage index. -/
abbrev sourceOriginalH1Z1StageVertex
    (src dst : ι → V)
    (j : sourceOriginalH1Z1ThreeFamilyIndex src dst) :=
  (sourceOriginalH1Z1ActionDatum src dst j).Carrier

/-- A SINGLE dependent disjoint complete SIGNED EGraph built
from every actual original plain, anchored type-(1) and
rooted type-(2) source stage, with exact original tags. -/
noncomputable def sourceOriginalH1Z1ThreeFamilyStage
    (src dst : ι → V) :
    CompleteEGraph
      (Σ j : sourceOriginalH1Z1ThreeFamilyIndex src dst,
        sourceOriginalH1Z1StageVertex src dst j)
      (ActionEdge
        (Σ j : sourceOriginalH1Z1ThreeFamilyIndex src dst,
          sourceOriginalH1Z1StageVertex src dst j) ι) ι :=
  dependentDisjointStage
    (fun j : sourceOriginalH1Z1ThreeFamilyIndex src dst =>
      (sourceOriginalH1Z1ActionDatum src dst j).stage)

/-- The actual finite group G₂ from the input controls
signed actions on ALL tagged vertices of ALL THREE families
of true original H₁ completed source stages simultaneously.
The group-value congruence holds on the complete action, not
only separately for each selected old B-component. -/
theorem sourceOriginalH1Z1ThreeFamily_wordValue_congr
    (src dst : ι → V)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ x : Σ j : sourceOriginalH1Z1ThreeFamilyIndex src dst,
      sourceOriginalH1Z1StageVertex src dst j,
      (sourceOriginalH1Z1ThreeFamilyStage src dst).followWord x p =
        (sourceOriginalH1Z1ThreeFamilyStage src dst).followWord x q := by
  apply (dependentDisjointStage_wordEquality_all_iff
    (fun j : sourceOriginalH1Z1ThreeFamilyIndex src dst =>
      (sourceOriginalH1Z1ActionDatum src dst j).stage) p q).mpr
  intro j x
  cases j with
  | inl t =>
      exact sourceG2OriginalH1Plain_wordValue_congr
        src dst t p q hpq x
  | inr k =>
      cases k with
      | inl t =>
          exact sourceG2OriginalH1AllType1_fibre_wordValue_congr
            src dst t.1.1 t.1.2 p q hpq t.2 x
      | inr t =>
          exact sourceG2OriginalH1Type2Translated_wordValue_congr
            src dst t.1 t.2 p q hpq x

end ABO
end PSTSEPPA
