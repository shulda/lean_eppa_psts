import PSTSEPPA.ABO.SourceLiteralY1PaperStageSynchronousGroup
import PSTSEPPA.ABO.SourceLiteralY1ThreeKindFinite
import PSTSEPPA.ABO.DisjointCompleteTransitionQuotients
import PSTSEPPA.ABO.LabelledWordKernelMulEquiv
import PSTSEPPA.ABO.SourceLiteralY1H1GroupEquiv
import PSTSEPPA.ABO.CayleyStageProjection

/-!
# Literal PRINTED X₂ first-rank transition group: repaired base stability

This file now uses the exact graph-object definition
  X₂^all = Y₁ ⊔ completed-actual-original-T(Y₁)-three-kind stages,
not just an abstract synchronized product. The right summand
contains the true original-incomplete-edge coset extensions,
anchored augmented clusters and off-B original tagged
quotient-root B-augmentations, with formal inverse edge tokens
and LEGAL fixed-loop completion.

The transition group T(X₂^all) maps surjectively, generator for
generator, to the actual printed T(Y₁) AND to the actual printed
three-kind completed-stage transition group.

The corrected Proposition 5.4 BASE CASE is established
DIRECTLY for the literal group quotient T(X₂^all) -> T(Y₁):
every signed singleton-supported relation vanishing in T(Y₁)
acts trivially in the complete X₂^all action. Hence the
quotient is 1-stable. The target T(Y₁) is genuinely
2-retractable by its already-certified labelled isomorphism to
the original source-shaped H₁. Thus T(X₂^all) is
2-retractable, with no phantom H₀ or rank-zero induction.

We also give an ACTUAL generator-preserving based Cayley
projection from T(X₂^all) to any chosen printed stage vertex,
including exact chronological signed-word endpoints.

X₂^all is still an all-choice redundant superfamily.
Finiteness of its literal disjoint vertex carrier and the
equivariant exact Definition-5.3 representative selection
are separate. Higher-rank Condition 5.2, Theorem 4.7,
the reflecting group and ordinary PSTS EPPA remain OPEN.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The actual PRINTED first next-stage complete signed graph:
the original literal Y₁ (not just isomorphic H₁) disjoint
from ALL genuinely printed full/augmented first-rank stages. -/
noncomputable abbrev sourceLiteralY1X2AllStage
    (src dst : ι → V) :=
  (sourceLiteralY1 src dst).disjointUnion
    (sourceLiteralY1ThreeKindStage src dst)

/-- Exact literal generated second transition-group letters
from actual X₂^all, retaining positive and inverse edge actions. -/
noncomputable abbrev sourceLiteralY1X2AllGenerator
    (src dst : ι → V) :=
  (sourceLiteralY1X2AllStage src dst).transitionSubgroupGenerator

/-- Direct restriction of T(X₂^all) onto the paper's literal
H₁=T(Y₁), surjectively and with every edge generator fixed. -/
noncomputable def sourceLiteralY1X2AllToY1
    (src dst : ι → V) :
    LabelledGroupQuotient
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1 src dst).transitionSubgroupGenerator :=
  (sourceLiteralY1 src dst).disjointUnionLeftQuotient
    (sourceLiteralY1ThreeKindStage src dst)

/-- Direct restriction onto the actual three-kind completed
stage-transition group, including old/fresh stage tags. -/
noncomputable def sourceLiteralY1X2AllToThreeKind
    (src dst : ι → V) :
    LabelledGroupQuotient
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1ThreeKindStage src dst).transitionSubgroupGenerator :=
  (sourceLiteralY1 src dst).disjointUnionRightQuotient
    (sourceLiteralY1ThreeKindStage src dst)

/-- The literal FIRST transition group T(Y₁), not merely
the source model H₁, is 2-retractable. Transfer the
verified SourceH₁ property via exact agreement of ALL
signed identity-word kernels, rather than asserting a
global retraction for the wrong presentation. -/
theorem sourceLiteralY1_transitionTwoRetractable
    (src dst : ι → V) :
    KRetractable
      (sourceLiteralY1 src dst).transitionSubgroupGenerator 2 := by
  intro C hC a p q hp hq hpq
  have hSource :
      PSTS.SignedWord.evalGroup (sourceH1Generator src dst) p =
        PSTS.SignedWord.evalGroup (sourceH1Generator src dst) q :=
    labelled_evalGroup_eq_of_kernel_iff
      (sourceLiteralY1 src dst).transitionSubgroupGenerator
      (sourceH1Generator src dst)
      (fun w => (sourceH1_literalY1_transition_kernel_iff src dst w).symm)
      hpq
  have hEraseSource :=
    sourceH1_twoRetractable src dst C hC a p q hp hq hSource
  exact labelled_evalGroup_eq_of_kernel_iff
    (sourceH1Generator src dst)
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1_literalY1_transition_kernel_iff src dst)
    hEraseSource

/-- Direct corrected rank-one stability of the LITERAL
T(Y₁ ⊔ Z₁^all) -> T(Y₁) labelled quotient.
This needs no source-rank-zero induction: the verified
entire printed-stage 1-letter word kernel suffices. -/
theorem sourceLiteralY1X2AllToY1_oneStable
    (src dst : ι → V) :
    (sourceLiteralY1X2AllToY1 src dst).KStable 1 := by
  apply (sourceLiteralY1X2AllToY1 src dst).kStable_of_word_kernel 1
  intro C hC w hw hDown
  have hSource :
      PSTS.SignedWord.evalGroup (sourceH1Generator src dst) w = 1 :=
    (sourceH1_literalY1_transition_kernel_iff src dst w).mpr hDown
  have hStage :
      (sourceLiteralY1ThreeKindStage src dst).wordValue w = 1 :=
    sourceLiteralY1ThreeKind_rankOne_stageKernel src dst
      C hC w hw hSource
  have hY1 :
      (sourceLiteralY1 src dst).wordValue w = 1 := by
    have hv := congrArg Subtype.val hDown
    exact ((sourceLiteralY1 src dst).evalGroup_transitionSubgroupGenerator_val w).symm.trans hv
  have hSum :
      (sourceLiteralY1X2AllStage src dst).wordValue w = 1 :=
    ((sourceLiteralY1 src dst).disjointUnion_wordValue_eq_one_iff
      (sourceLiteralY1ThreeKindStage src dst) w).mpr
      ⟨hY1, hStage⟩
  apply Subtype.ext
  exact ((sourceLiteralY1X2AllStage src dst).evalGroup_transitionSubgroupGenerator_val w).trans
    hSum

/-- Repaired retractability descent FOR THE LITERAL PRINTED
first next-group: its 1-stable projection onto the
2-retractable T(Y₁) makes T(X₂^all) 2-retractable. -/
theorem sourceLiteralY1X2All_twoRetractable
    (src dst : ι → V) :
    KRetractable (sourceLiteralY1X2AllGenerator src dst) 2 := by
  exact (sourceLiteralY1X2AllToY1 src dst).kRetractable_of_kStable
    1 (sourceLiteralY1X2AllToY1_oneStable src dst)
      (sourceLiteralY1_transitionTwoRetractable src dst)

/-- The ACTUAL literal paper-style complete disjoint action
X₂^all = Y₁ ⊔ Z₁^all has a FINITE transition group.
Both vertex carriers are independently finite, including all
genuine B=∅ and component-tagged off-B augmentation roots.
This argument never quotients by ambient group values. -/
theorem finite_sourceLiteralY1X2AllTransitionGroup
    (src dst : ι → V) :
    Finite (sourceLiteralY1X2AllStage src dst).transitionGroup := by
  classical
  letI : Finite
      (V ⊕ (Σ i : ι,
        generatedSubgroup (sourceG1Generator src dst)
          ({i} : Finset ι))) :=
    finite_sourceLiteralY1Vertex src dst
  letI : Finite (SourceLiteralY1ThreeKindVertex src dst) :=
    finite_sourceLiteralY1ThreeKindVertex src dst
  letI : Fintype
      (V ⊕ (Σ i : ι,
        generatedSubgroup (sourceG1Generator src dst)
          ({i} : Finset ι))) := Fintype.ofFinite _
  letI : Fintype (SourceLiteralY1ThreeKindVertex src dst) :=
    Fintype.ofFinite _
  exact (sourceLiteralY1X2AllStage src dst).finite_transitionGroup

/-- Actual based labelled Cayley(T(X₂^all)) map into the
ACTUAL printed full three-kind completed graph, not
an abstract action surrogate. -/
noncomputable def sourceLiteralY1X2AllCayleyToThreeKind
    (src dst : ι → V)
    (u : Σ j : sourceLiteralY1ThreeKindIndex src dst,
      sourceLiteralY1ThreeKindStageVertex src dst j) :
    LabelledGraphHom
      (cayleyGraph (sourceLiteralY1X2AllGenerator src dst)).toEGraph.toLabelledGraph
      (sourceLiteralY1ThreeKindStage src dst).toEGraph.toLabelledGraph :=
  (sourceLiteralY1ThreeKindStage src dst).cayleyProjectionFromGroup
    (sourceLiteralY1X2AllGenerator src dst)
    (sourceLiteralY1X2AllToThreeKind src dst).hom
    (sourceLiteralY1X2AllToThreeKind src dst).map_gen
    u

/-- Its identity maps to the EXACT selected old/fresh
component-tagged stage point, with no coordinate collapse. -/
theorem sourceLiteralY1X2AllCayleyToThreeKind_one
    (src dst : ι → V)
    (u : Σ j : sourceLiteralY1ThreeKindIndex src dst,
      sourceLiteralY1ThreeKindStageVertex src dst j) :
    (sourceLiteralY1X2AllCayleyToThreeKind src dst u).onVertex 1 = u :=
  (sourceLiteralY1ThreeKindStage src dst).cayleyProjectionFromGroup_one
    (sourceLiteralY1X2AllGenerator src dst)
    (sourceLiteralY1X2AllToThreeKind src dst).hom
    (sourceLiteralY1X2AllToThreeKind src dst).map_gen
    u

/-- Following an arbitrary chronological signed input word
agrees EXACTLY with projecting its value in the literal
second transition group. Distinct oriented inverse tokens
and legally stationary loop edges are respected. -/
theorem sourceLiteralY1X2AllCayleyToThreeKind_word
    (src dst : ι → V)
    (u : Σ j : sourceLiteralY1ThreeKindIndex src dst,
      sourceLiteralY1ThreeKindStageVertex src dst j)
    (w : LabelWord ι) :
    (sourceLiteralY1X2AllCayleyToThreeKind src dst u).onVertex
      (PSTS.SignedWord.evalGroup
        (sourceLiteralY1X2AllGenerator src dst) w) =
      (sourceLiteralY1ThreeKindStage src dst).followWord u w :=
  (sourceLiteralY1ThreeKindStage src dst).cayleyProjectionFromGroup_evalGroup
    (sourceLiteralY1X2AllGenerator src dst)
    (sourceLiteralY1X2AllToThreeKind src dst).hom
    (sourceLiteralY1X2AllToThreeKind src dst).map_gen
    u w

end ABO
end PSTSEPPA
