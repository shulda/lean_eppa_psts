import PSTSEPPA.ABO.DependentDisjointWordCongruence
import PSTSEPPA.ABO.CompleteStageWordCongruenceReachableCover
import PSTSEPPA.ABO.TransitionGroupGenerated

/-!
# Every genuine dependent stage is a labelled quotient of its disjoint action

The corrected ABO finite Section-5 action is a dependent disjoint
union of complete, independently tagged signed stages. It is
NOT merely an unlabelled product of their permutation groups.

Here we prove the actual transition subgroup of this genuine
dependent union has a generator-preserving SURJECTIVE quotient
onto the transition subgroup of EACH chosen fibre. This is
deduced from equality of the full chronological signed-word
permutations and the exact indexed word-following theorem.

Even if the index type is empty, no arbitrary representatives
or ambient group coordinate equalities are postulated; each
individual map is a finite-word/action construction.

This generic component restriction is the missing bridge from
the existing literal T(Y₁ ⊔ Z₁^all) projection to the true
one-fibre rank-two old P_A completed action needed for geometric
B-path/bridge lifting. It does not prove the geometric
embedding or bridge-freeness induction.
-/

namespace PSTSEPPA
namespace ABO

universe uJ uι uV uE

variable {J : Type uJ} {ι : Type uι}
variable {V : J → Type uV} {Edge : J → Type uE}
variable [Fintype ι] [DecidableEq ι]

/-- Equality of two arbitrary signed-word values in the
ACTUAL dependent disjoint transition group implies equality
of their actions at every vertex of ANY specified genuine
completed fibre, including both formal inverse labels. -/
theorem dependentDisjointStage_fibre_wordActionCongr
    (T : ∀ j : J, CompleteEGraph (V j) (Edge j) ι)
    (j : J)
    (p q : LabelWord ι)
    (hpq :
      PSTS.SignedWord.evalGroup
        (dependentDisjointStage T).transitionSubgroupGenerator p =
      PSTS.SignedWord.evalGroup
        (dependentDisjointStage T).transitionSubgroupGenerator q) :
    ∀ x : V j, (T j).followWord x p = (T j).followWord x q := by
  have hPerm :
      (dependentDisjointStage T).wordValue p =
      (dependentDisjointStage T).wordValue q := by
    calc
      (dependentDisjointStage T).wordValue p =
          ((PSTS.SignedWord.evalGroup
            (dependentDisjointStage T).transitionSubgroupGenerator p :
            (dependentDisjointStage T).transitionGroup) : RightPerm (Sigma V)) :=
        ((dependentDisjointStage T).evalGroup_transitionSubgroupGenerator_val p).symm
      _ = ((PSTS.SignedWord.evalGroup
            (dependentDisjointStage T).transitionSubgroupGenerator q :
            (dependentDisjointStage T).transitionGroup) : RightPerm (Sigma V)) :=
        congrArg Subtype.val hpq
      _ = (dependentDisjointStage T).wordValue q :=
        (dependentDisjointStage T).evalGroup_transitionSubgroupGenerator_val q
  have hAll :
      ∀ y : Sigma V,
        (dependentDisjointStage T).followWord y p =
        (dependentDisjointStage T).followWord y q := by
    intro y
    calc
      (dependentDisjointStage T).followWord y p =
          CompleteEGraph.rightApply
            ((dependentDisjointStage T).wordValue p) y :=
        ((dependentDisjointStage T).rightApply_wordValue p y).symm
      _ = CompleteEGraph.rightApply
            ((dependentDisjointStage T).wordValue q) y :=
        congrArg (fun g : RightPerm (Sigma V) =>
          CompleteEGraph.rightApply g y) hPerm
      _ = (dependentDisjointStage T).followWord y q :=
        (dependentDisjointStage T).rightApply_wordValue q y
  exact ((dependentDisjointStage_wordEquality_all_iff T p q).mp hAll) j

/-- The literal signed dependent disjoint action's generated
transition GROUP quotients surjectively, preserving every
original positive generator, onto the genuine chosen stage's
complete signed transition group. No coordinate or index
identification is used. -/
noncomputable def dependentDisjointStage_fibreTransitionQuotient
    (T : ∀ j : J, CompleteEGraph (V j) (Edge j) ι)
    (j : J) :
    LabelledGroupQuotient
      (dependentDisjointStage T).transitionSubgroupGenerator
      (T j).transitionSubgroupGenerator where
  hom :=
    (T j).groupWordActionHom
      (dependentDisjointStage T).transitionSubgroupGenerator
      (dependentDisjointStage T).transitionSubgroupGenerator_isGenerated
      (dependentDisjointStage_fibre_wordActionCongr T j)
  map_gen := by
    intro i
    exact
      (T j).groupWordActionHom_generator
        (dependentDisjointStage T).transitionSubgroupGenerator
        (dependentDisjointStage T).transitionSubgroupGenerator_isGenerated
        (dependentDisjointStage_fibre_wordActionCongr T j) i
  surjective :=
    (T j).groupWordActionHom_surjective
      (dependentDisjointStage T).transitionSubgroupGenerator
      (dependentDisjointStage T).transitionSubgroupGenerator_isGenerated
      (dependentDisjointStage_fibre_wordActionCongr T j)

end ABO
end PSTSEPPA
