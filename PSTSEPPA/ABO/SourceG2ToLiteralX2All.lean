import PSTSEPPA.ABO.SourceLiteralY1X2AllRankOne
import PSTSEPPA.ABO.SourceLiteralY1H1GroupEquiv
import PSTSEPPA.ABO.SourceLiteralY1ThreeKindTransitionQuotient
import PSTSEPPA.ABO.CompleteStageWordCongruenceCayleyCover

/-!
# The finite input-derived source G₂ quotients onto actual printed T(X₂^all)

Both existing constructions are REAL:
* sourceAllLocalG₂, generated synchronously from every local
  rank-two signed stage and the source H₁;
* the actual transition subgroup of the complete literal
  printed X₂^all = Y₁ ⊔ Z₁^all original-three-kind action.

We already proved that G₂ acts on EVERY genuine printed
plain/type-(1)/type-(2) legally completed stage. In addition
its projection to source H₁, and the labelled group isomorphism
source H₁ ≃ T(Y₁), control all signed words on the old Y₁
summand itself. Thus equality of G₂ chronological signed
word values forces equality of the ENTIRE literal X₂^all
permutation action, not merely equality in each abstract
synchronous coordinate.

This gives a genuine generator-preserving SURJECTIVE group
quotient from source G₂ onto the actual literal T(X₂^all),
with exact signed-word evaluation. More strongly, this
quotient is 1-STABLE, since the old H₁ factor already
detects all rank-one G₂ word relations. All inverses,
loops, old source tags and new coset-component tags remain
present. It is the all-choice family, NOT an exact
equivariant Definition-5.3 stage selection; later Theorem
4.7 geometry, higher-rank induction and PSTS EPPA are open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Equality in the concrete finite source G₂ implies
identical word actions on the ENTIRE actual literal Y₁,
including both its X₁ summand and all regularly completed
unary Cayley summands. -/
theorem sourceG2_literalY1_wordValue_congr
    (src dst : ι → V)
    (p q : LabelWord ι)
    (hpq :
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ x,
      (sourceLiteralY1 src dst).followWord x p =
      (sourceLiteralY1 src dst).followWord x q := by
  let Q := sourceAllLocalG2ToH1 src dst
  let E := sourceH1EquivLiteralY1Transition src dst
  let T := sourceLiteralY1 src dst
  have hH1 :
      PSTS.SignedWord.evalGroup (sourceH1Generator src dst) p =
      PSTS.SignedWord.evalGroup (sourceH1Generator src dst) q := by
    calc
      PSTS.SignedWord.evalGroup (sourceH1Generator src dst) p =
          Q.hom (PSTS.SignedWord.evalGroup
            (sourceAllLocalG2Generator src dst) p) :=
          (Q.map_evalGroup p).symm
      _ = Q.hom (PSTS.SignedWord.evalGroup
            (sourceAllLocalG2Generator src dst) q) :=
          congrArg Q.hom hpq
      _ = PSTS.SignedWord.evalGroup (sourceH1Generator src dst) q :=
          Q.map_evalGroup q
  have hY1 :
      PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator p =
      PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator q := by
    calc
      PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator p =
          E (PSTS.SignedWord.evalGroup
            (sourceH1Generator src dst) p) :=
          (sourceH1EquivLiteralY1Transition_evalGroup src dst p).symm
      _ = E (PSTS.SignedWord.evalGroup
            (sourceH1Generator src dst) q) :=
          congrArg E hH1
      _ = PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator q :=
          sourceH1EquivLiteralY1Transition_evalGroup src dst q
  have hPerm : T.wordValue p = T.wordValue q := by
    calc
      T.wordValue p =
          ((PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator p :
              T.transitionGroup) : RightPerm _) :=
          (T.evalGroup_transitionSubgroupGenerator_val p).symm
      _ = ((PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator q :
              T.transitionGroup) : RightPerm _) :=
          congrArg Subtype.val hY1
      _ = T.wordValue q :=
          T.evalGroup_transitionSubgroupGenerator_val q
  intro x
  calc
    T.followWord x p = rightApply (T.wordValue p) x :=
      (T.rightApply_wordValue p x).symm
    _ = rightApply (T.wordValue q) x :=
      congrArg (fun g : RightPerm _ => rightApply g x) hPerm
    _ = T.followWord x q :=
      T.rightApply_wordValue q x

/-- The finite source G₂ controls the WHOLE LITERAL printed
Y₁ ⊔ all-choice-Z₁ signed action, not only its completed Z₁
factor. This is an unrestricted chronological signed-word
congruence for BOTH disjoint summands together. -/
theorem sourceG2_literalX2All_wordValue_congr
    (src dst : ι → V)
    (p q : LabelWord ι)
    (hpq :
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ x,
      (sourceLiteralY1X2AllStage src dst).followWord x p =
      (sourceLiteralY1X2AllStage src dst).followWord x q := by
  intro x
  cases x with
  | inl y =>
      change
        ((sourceLiteralY1 src dst).disjointUnion
          (sourceLiteralY1ThreeKindStage src dst)).followWord
            (.inl y) p =
        ((sourceLiteralY1 src dst).disjointUnion
          (sourceLiteralY1ThreeKindStage src dst)).followWord
            (.inl y) q
      rw [
        (sourceLiteralY1 src dst).disjointUnion_followWord_inl
          (sourceLiteralY1ThreeKindStage src dst) y p,
        (sourceLiteralY1 src dst).disjointUnion_followWord_inl
          (sourceLiteralY1ThreeKindStage src dst) y q]
      exact congrArg Sum.inl
        (sourceG2_literalY1_wordValue_congr src dst p q hpq y)
  | inr y =>
      change
        ((sourceLiteralY1 src dst).disjointUnion
          (sourceLiteralY1ThreeKindStage src dst)).followWord
            (.inr y) p =
        ((sourceLiteralY1 src dst).disjointUnion
          (sourceLiteralY1ThreeKindStage src dst)).followWord
            (.inr y) q
      rw [
        (sourceLiteralY1 src dst).disjointUnion_followWord_inr
          (sourceLiteralY1ThreeKindStage src dst) y p,
        (sourceLiteralY1 src dst).disjointUnion_followWord_inr
          (sourceLiteralY1ThreeKindStage src dst) y q]
      exact congrArg Sum.inr
        (sourceG2LiteralY1ThreeKind_wordValue_congr
          src dst p q hpq y)

/-- ACTUAL SURJECTIVE labelled group quotient from the finite
source G₂ onto the true transition subgroup T(X₂^all)
of the whole printed original-edge-and-completed-stage graph.
It is derived from the complete disjoint-action WORD congruence,
not from separate surjectivity of the two factor projections. -/
noncomputable def sourceG2ToLiteralX2All
    (src dst : ι → V) :
    LabelledGroupQuotient
      (sourceAllLocalG2Generator src dst)
      (sourceLiteralY1X2AllGenerator src dst) where
  hom :=
    (sourceLiteralY1X2AllStage src dst).groupWordActionHom
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceG2_literalX2All_wordValue_congr src dst)
  map_gen := by
    intro i
    exact
      (sourceLiteralY1X2AllStage src dst).groupWordActionHom_generator
        (sourceAllLocalG2Generator src dst)
        (sourceAllLocalG2Generator_isGenerated src dst)
        (sourceG2_literalX2All_wordValue_congr src dst) i
  surjective :=
    (sourceLiteralY1X2AllStage src dst).groupWordActionHom_surjective
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceG2_literalX2All_wordValue_congr src dst)

/-- Exact signed word-value compatibility for the new concrete
quotient onto the WHOLE original printed second transition group. -/
theorem sourceG2ToLiteralX2All_evalGroup
    (src dst : ι → V) (w : LabelWord ι) :
    (sourceG2ToLiteralX2All src dst).hom
      (PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) w) =
      PSTS.SignedWord.evalGroup
        (sourceLiteralY1X2AllGenerator src dst) w :=
  (sourceLiteralY1X2AllStage src dst).groupWordActionHom_evalGroup
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2_literalX2All_wordValue_congr src dst) w

/-- The direct source-G₂ onto literal-X₂-all quotient is itself
1-STABLE. If a single-generator signed word becomes trivial in
T(X₂^all), it is already trivial in printed T(Y₁), then source
H₁, and source G₂ by the certified old 1-stable quotient.
This gives a second independent labelled rank-one comparison,
not just plain surjectivity onto two factors. -/
theorem sourceG2ToLiteralX2All_oneStable
    (src dst : ι → V) :
    (sourceG2ToLiteralX2All src dst).KStable 1 := by
  apply (sourceG2ToLiteralX2All src dst).kStable_of_word_kernel 1
  intro C hC w hw hval
  have hY1 :
      PSTS.SignedWord.evalGroup
        (sourceLiteralY1 src dst).transitionSubgroupGenerator w = 1 := by
    calc
      PSTS.SignedWord.evalGroup
          (sourceLiteralY1 src dst).transitionSubgroupGenerator w =
        (sourceLiteralY1X2AllToY1 src dst).hom
          (PSTS.SignedWord.evalGroup
            (sourceLiteralY1X2AllGenerator src dst) w) :=
        ((sourceLiteralY1X2AllToY1 src dst).map_evalGroup w).symm
      _ = (sourceLiteralY1X2AllToY1 src dst).hom 1 :=
        congrArg (sourceLiteralY1X2AllToY1 src dst).hom hval
      _ = 1 := map_one _
  have hH1 :
      PSTS.SignedWord.evalGroup (sourceH1Generator src dst) w = 1 :=
    (sourceH1_literalY1_transition_kernel_iff src dst w).mpr hY1
  exact ((sourceAllLocalG2ToH1 src dst).kStable_iff_word_kernel 1).mp
    (sourceAllLocalG2ToH1_oneStable src dst)
      C hC w hw hH1

end ABO
end PSTSEPPA
