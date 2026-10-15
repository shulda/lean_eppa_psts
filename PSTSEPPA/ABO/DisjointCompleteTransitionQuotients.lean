import PSTSEPPA.ABO.CompleteStageWordCongruenceReachableCover
import PSTSEPPA.ABO.DisjointStageWordKernel
import PSTSEPPA.ABO.TransitionGroupGenerated

/-!
# The transition group of a literal disjoint action quotients onto both factors

The printed ABO source defines each next finite group as the ACTUAL
transition subgroup T(X ⊔ Y), where X and Y are complete labelled
EGraphs. Their disjoint union preserves original vertex and oriented
edge tags, so its signed word action is exactly componentwise.

We construct the two GENUINE surjective group homomorphisms

    T(X ⊔ Y) ↠ T(X),       T(X ⊔ Y) ↠ T(Y)

that preserve EVERY positive original label. Their existence is
derived directly from equality of the full signed word actions,
not from any unchecked abstract product-group presentation. In
particular an equality of words in the larger transition group
forces equality of their signed paths on each actual summand.

The construction handles empty vertex carriers, loops, nonfaithful
generators and repeated/identity edge labels. It is not a claim
that either coordinate projection is injective.

This supplies the literal X₁-projection T(Y₁) ↠ T(X₁) in the
printed rank-one construction, as distinct from merely transporting
a quotient from an algebraically isomorphic synchronized model.
-/

namespace PSTSEPPA
namespace ABO

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable [Fintype ι] [DecidableEq ι]

namespace CompleteEGraph

/-- If two signed words have equal ACTUAL transition-group values
in a literal disjoint complete action, their paths agree at EVERY
vertex of the left summand. This is an unrestricted signed-word
congruence, not a bounded-rank kernel property. -/
theorem disjointUnion_left_wordActionCongr
    (G : CompleteEGraph V₁ E₁ ι)
    (H : CompleteEGraph V₂ E₂ ι)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (G.disjointUnion H).transitionSubgroupGenerator p =
      PSTS.SignedWord.evalGroup
        (G.disjointUnion H).transitionSubgroupGenerator q) :
    ∀ x : V₁, G.followWord x p = G.followWord x q := by
  have hsum : (G.disjointUnion H).wordValue p =
      (G.disjointUnion H).wordValue q := by
    calc
      (G.disjointUnion H).wordValue p =
        ((PSTS.SignedWord.evalGroup
          (G.disjointUnion H).transitionSubgroupGenerator p :
          (G.disjointUnion H).transitionGroup) : RightPerm (V₁ ⊕ V₂)) :=
        ((G.disjointUnion H).evalGroup_transitionSubgroupGenerator_val p).symm
      _ = ((PSTS.SignedWord.evalGroup
          (G.disjointUnion H).transitionSubgroupGenerator q :
          (G.disjointUnion H).transitionGroup) : RightPerm (V₁ ⊕ V₂)) :=
        congrArg Subtype.val hpq
      _ = (G.disjointUnion H).wordValue q :=
        (G.disjointUnion H).evalGroup_transitionSubgroupGenerator_val q
  intro x
  have hleft :
      (G.disjointUnion H).followWord (Sum.inl x) p =
        (G.disjointUnion H).followWord (Sum.inl x) q := by
    calc
      (G.disjointUnion H).followWord (Sum.inl x) p =
        rightApply ((G.disjointUnion H).wordValue p) (Sum.inl x) :=
        ((G.disjointUnion H).rightApply_wordValue p (Sum.inl x)).symm
      _ = rightApply ((G.disjointUnion H).wordValue q) (Sum.inl x) := by
        rw [hsum]
      _ = (G.disjointUnion H).followWord (Sum.inl x) q :=
        (G.disjointUnion H).rightApply_wordValue q (Sum.inl x)
  rw [G.disjointUnion_followWord_inl H x p,
    G.disjointUnion_followWord_inl H x q] at hleft
  exact Sum.inl.inj hleft

/-- Symmetric projection: equality of signed word values in
T(G ⊔ H) forces equality of their actions at each right-summand
vertex, preserving formal inverse edge labels. -/
theorem disjointUnion_right_wordActionCongr
    (G : CompleteEGraph V₁ E₁ ι)
    (H : CompleteEGraph V₂ E₂ ι)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (G.disjointUnion H).transitionSubgroupGenerator p =
      PSTS.SignedWord.evalGroup
        (G.disjointUnion H).transitionSubgroupGenerator q) :
    ∀ x : V₂, H.followWord x p = H.followWord x q := by
  have hsum : (G.disjointUnion H).wordValue p =
      (G.disjointUnion H).wordValue q := by
    calc
      (G.disjointUnion H).wordValue p =
        ((PSTS.SignedWord.evalGroup
          (G.disjointUnion H).transitionSubgroupGenerator p :
          (G.disjointUnion H).transitionGroup) : RightPerm (V₁ ⊕ V₂)) :=
        ((G.disjointUnion H).evalGroup_transitionSubgroupGenerator_val p).symm
      _ = ((PSTS.SignedWord.evalGroup
          (G.disjointUnion H).transitionSubgroupGenerator q :
          (G.disjointUnion H).transitionGroup) : RightPerm (V₁ ⊕ V₂)) :=
        congrArg Subtype.val hpq
      _ = (G.disjointUnion H).wordValue q :=
        (G.disjointUnion H).evalGroup_transitionSubgroupGenerator_val q
  intro x
  have hright :
      (G.disjointUnion H).followWord (Sum.inr x) p =
        (G.disjointUnion H).followWord (Sum.inr x) q := by
    calc
      (G.disjointUnion H).followWord (Sum.inr x) p =
        rightApply ((G.disjointUnion H).wordValue p) (Sum.inr x) :=
        ((G.disjointUnion H).rightApply_wordValue p (Sum.inr x)).symm
      _ = rightApply ((G.disjointUnion H).wordValue q) (Sum.inr x) := by
        rw [hsum]
      _ = (G.disjointUnion H).followWord (Sum.inr x) q :=
        (G.disjointUnion H).rightApply_wordValue q (Sum.inr x)
  rw [G.disjointUnion_followWord_inr H x p,
    G.disjointUnion_followWord_inr H x q] at hright
  exact Sum.inr.inj hright

/-- The LITERAL left-factor restriction of the complete
disjoint transition action is a surjective group homomorphism
preserving exactly the original labelled transition generators.
No abstract synchronized-product isomorphism is required. -/
noncomputable def disjointUnionLeftQuotient
    (G : CompleteEGraph V₁ E₁ ι)
    (H : CompleteEGraph V₂ E₂ ι) :
    LabelledGroupQuotient
      (G.disjointUnion H).transitionSubgroupGenerator
      G.transitionSubgroupGenerator where
  hom :=
    G.groupWordActionHom
      (G.disjointUnion H).transitionSubgroupGenerator
      (G.disjointUnion H).transitionSubgroupGenerator_isGenerated
      (G.disjointUnion_left_wordActionCongr H)
  map_gen := by
    intro i
    exact G.groupWordActionHom_generator
      (G.disjointUnion H).transitionSubgroupGenerator
      (G.disjointUnion H).transitionSubgroupGenerator_isGenerated
      (G.disjointUnion_left_wordActionCongr H) i
  surjective :=
    G.groupWordActionHom_surjective
      (G.disjointUnion H).transitionSubgroupGenerator
      (G.disjointUnion H).transitionSubgroupGenerator_isGenerated
      (G.disjointUnion_left_wordActionCongr H)

/-- Equally, the complete disjoint transition group has a
surjective same-labelled restriction to its second summand.
Both maps are defined even if a summand has an empty carrier. -/
noncomputable def disjointUnionRightQuotient
    (G : CompleteEGraph V₁ E₁ ι)
    (H : CompleteEGraph V₂ E₂ ι) :
    LabelledGroupQuotient
      (G.disjointUnion H).transitionSubgroupGenerator
      H.transitionSubgroupGenerator where
  hom :=
    H.groupWordActionHom
      (G.disjointUnion H).transitionSubgroupGenerator
      (G.disjointUnion H).transitionSubgroupGenerator_isGenerated
      (G.disjointUnion_right_wordActionCongr H)
  map_gen := by
    intro i
    exact H.groupWordActionHom_generator
      (G.disjointUnion H).transitionSubgroupGenerator
      (G.disjointUnion H).transitionSubgroupGenerator_isGenerated
      (G.disjointUnion_right_wordActionCongr H) i
  surjective :=
    H.groupWordActionHom_surjective
      (G.disjointUnion H).transitionSubgroupGenerator
      (G.disjointUnion H).transitionSubgroupGenerator_isGenerated
      (G.disjointUnion_right_wordActionCongr H)

end CompleteEGraph
end ABO
end PSTSEPPA
