import PSTSEPPA.ABO.DisjointStageWordKernel

/-!
# Finite and dependent families of complete ABO stages

Section 5 assembles not merely two but whole finite indexed
families Z_k of complete labelled E-graphs. The vertex sets of
these stages need not be the same type. A dependent disjoint
union must retain the stage tag of every vertex, and every
signed transition must stay in its own stage.

We realize the dependent disjoint stage directly as an
actionGraph on the sigma-type of tagged vertices, with one
genuine total permutation per unsigned generator. Its signed
word action is exactly componentwise, including negative
letters. Thus the transition-word kernel of the whole
assembly is the INTERSECTION of the kernels of all stages.

This handles empty index types, empty carriers, arbitrary
nonfaithful generator families and arbitrary signed words.
The proposition is completely algebraic; the construction
and kernel analysis of the individual ABO augmented stages
remain separate.
-/

namespace PSTSEPPA
namespace ABO

variable {J ι : Type*}
variable {V Edge : J → Type*}

/-- The complete signed action on the dependent disjoint
union of all stage vertex types. A positive letter preserves
its index and acts by its original stage permutation. -/
noncomputable def dependentStagePerm
    (T : ∀ j : J, CompleteEGraph (V j) (Edge j) ι)
    (i : ι) : Equiv.Perm (Sigma V) where
  toFun := fun x =>
    ⟨x.1, (T x.1).letterPerm (.pos i) x.2⟩
  invFun := fun x =>
    ⟨x.1, ((T x.1).letterPerm (.pos i)).symm x.2⟩
  left_inv := by
    rintro ⟨j, x⟩
    change (⟨j, ((T j).letterPerm (.pos i)).symm
      ((T j).letterPerm (.pos i) x)⟩ : Sigma V) = ⟨j, x⟩
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨j, x⟩
    change (⟨j, (T j).letterPerm (.pos i)
      (((T j).letterPerm (.pos i)).symm x)⟩ : Sigma V) = ⟨j, x⟩
    rw [Equiv.apply_symm_apply]

/-- A single genuine complete E-graph on the sigma-type of
tagged vertices, with signed transitions acting in each
corresponding stage. This avoids any assumption that the
individual vertex carriers are disjoint as raw sets. -/
noncomputable def dependentDisjointStage
    (T : ∀ j : J, CompleteEGraph (V j) (Edge j) ι) :
    CompleteEGraph (Sigma V) (ActionEdge (Sigma V) ι) ι :=
  actionGraph (dependentStagePerm T)

/-- Signed letters, including inverse labels, act without
changing the stage index. -/
theorem dependentDisjointStage_letterPerm
    (T : ∀ j : J, CompleteEGraph (V j) (Edge j) ι)
    (j : J) (x : V j) (s : SignedLabel ι) :
    (dependentDisjointStage T).letterPerm s
        (⟨j, x⟩ : Sigma V) =
      ⟨j, (T j).letterPerm s x⟩ := by
  cases s with
  | pos i =>
      rfl
  | neg i =>
      change
        (⟨j, ((T j).letterPerm (.pos i)).symm x⟩ : Sigma V) =
          ⟨j, (T j).letterPerm (.neg i) x⟩
      rw [(T j).letterPerm_inv (.pos i)]

/-- Exactly the same signed word is followed in the selected
stage as in the whole dependent assembly, with the same
component tag at the endpoint. -/
theorem dependentDisjointStage_followWord
    (T : ∀ j : J, CompleteEGraph (V j) (Edge j) ι)
    (j : J) (x : V j) (w : LabelWord ι) :
    (dependentDisjointStage T).followWord (⟨j, x⟩ : Sigma V) w =
      ⟨j, (T j).followWord x w⟩ := by
  induction w generalizing x with
  | nil => rfl
  | cons s w ih =>
      rw [CompleteEGraph.followWord_cons]
      rw [← CompleteEGraph.letterPerm_apply]
      rw [dependentDisjointStage_letterPerm]
      rw [ih]
      rw [CompleteEGraph.followWord_cons]
      rw [← CompleteEGraph.letterPerm_apply]

/-- The genuine transition word is trivial on the assembled
complete stage precisely when it is trivial on EVERY component.
No global faithfulness or non-emptiness assumption is needed. -/
theorem dependentDisjointStage_wordValue_eq_one_iff
    (T : ∀ j : J, CompleteEGraph (V j) (Edge j) ι)
    (w : LabelWord ι) :
    (dependentDisjointStage T).wordValue w = 1 ↔
      ∀ j : J, (T j).wordValue w = 1 := by
  constructor
  · intro h j
    apply ((T j).wordValue_eq_one_iff_all_vertices_fixed w).mpr
    intro x
    have hfixed :=
      ((dependentDisjointStage T).wordValue_eq_one_iff_all_vertices_fixed w).mp
        h (⟨j, x⟩ : Sigma V)
    rw [dependentDisjointStage_followWord] at hfixed
    exact (Sigma.mk.inj_iff.mp hfixed)
  · intro h
    apply ((dependentDisjointStage T).wordValue_eq_one_iff_all_vertices_fixed w).mpr
    rintro ⟨j, x⟩
    rw [dependentDisjointStage_followWord]
    rw [((T j).wordValue_eq_one_iff_all_vertices_fixed w).mp (h j) x]

end ABO
end PSTSEPPA
