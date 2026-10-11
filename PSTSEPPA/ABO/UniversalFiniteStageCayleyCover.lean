import PSTSEPPA.ABO.UniversalStageWordFactorization

/-!
# Genuine Cayley covers of EVERY bounded kernel-correct finite ABO stage

The universal finite generated group U(Γ,k,M) from #337–#339
has a true canonical labelled Cayley cover onto each completed
stage with at most M vertices and the rank-k word-kernel
condition. The target stage can have ANY finite vertex type,
including true tagged coset-extension quotient vertices.

The key nontrivial point is WELL-DEFINEDNESS: choose for each
group element g an arbitrary signed word representing g.
By the certified universal word-factorization theorem, its
T-endpoint is independent of this choice. Thus the assignment
g -> endpoint_T(u, chosenWord(g)) is a genuine right action
of U on every such T, giving an actual labelled graph morphism
Cayley(U) -> T. We certify target and inverse signed edges,
the chosen identity basepoint and the exact images of all
vertices and directed edge tokens of the root component.

This is the sufficiency half of the source-agnostic universal
finite covering criterion and removes the last abstract
stage-action covering interface. It does NOT establish the
source-specific Z1 size/kernel hypotheses, higher-rank
historical action or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable [Fintype V]

/-- An arbitrary but genuine signed-word representative of
every element of the ACTUAL synchronously generated universal
group. Its existence is certified by generatedness, not by
a hypothetical finite group presentation. -/
noncomputable def universalStageChosenWord
    (gen : ι → Γ) (k M : ℕ)
    (g : universalStageGroup gen k M) : LabelWord ι :=
  Classical.choose
    ((universalStageGenerator_isGenerated gen k M).exists_evalGroup_eq g)

theorem universalStageChosenWord_eval
    (gen : ι → Γ) (k M : ℕ)
    (g : universalStageGroup gen k M) :
    PSTS.SignedWord.evalGroup
      (universalStageGenerator gen k M)
      (universalStageChosenWord gen k M g) = g :=
  Classical.choose_spec
    ((universalStageGenerator_isGenerated gen k M).exists_evalGroup_eq g)

/-- Endpoint of the REAL signed path in T starting at u and
following an arbitrary representative of g in U.
The next theorem shows this is independent of representatives
and compatible with every labelled edge. -/
noncomputable def universalStageVertexMap
    (gen : ι → Γ) (k M : ℕ)
    (T : CompleteEGraph V Edge ι)
    (hsize : Fintype.card V ≤ M)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1)
    (u : V) :
    universalStageGroup gen k M → V :=
  fun g => T.followWord u (universalStageChosenWord gen k M g)

/-- The canonical universal vertex map evaluates ANY chosen
signed word to its exact target endpoint in the true completed
stage. The proof uses group-word equality in U and the
independent verified finite-stage transport, so there is no
choice-dependence or identification of coset quotient points. -/
theorem universalStageVertexMap_evalGroup
    (gen : ι → Γ) (k M : ℕ)
    (T : CompleteEGraph V Edge ι)
    (hsize : Fintype.card V ≤ M)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1)
    (u : V) (w : LabelWord ι) :
    universalStageVertexMap gen k M T hsize hkernel u
      (PSTS.SignedWord.evalGroup
        (universalStageGenerator gen k M) w) =
      T.followWord u w := by
  change
    T.followWord u
      (universalStageChosenWord gen k M
        (PSTS.SignedWord.evalGroup
          (universalStageGenerator gen k M) w)) =
    T.followWord u w
  exact universalStage_wordEquality_reflects_completedStage
    gen k M T hsize hkernel
    (universalStageChosenWord gen k M
      (PSTS.SignedWord.evalGroup
        (universalStageGenerator gen k M) w))
    w
    (universalStageChosenWord_eval gen k M
      (PSTS.SignedWord.evalGroup
        (universalStageGenerator gen k M) w))
    u

/-- Actual source identity of U maps to the chosen completed
stage basepoint u, with no extra accessibility assumption. -/
theorem universalStageVertexMap_one
    (gen : ι → Γ) (k M : ℕ)
    (T : CompleteEGraph V Edge ι)
    (hsize : Fintype.card V ≤ M)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1)
    (u : V) :
    universalStageVertexMap gen k M T hsize hkernel u 1 = u := by
  have h := universalStageVertexMap_evalGroup
    gen k M T hsize hkernel u ([] : LabelWord ι)
  simpa using h

/-- Every TRUE signed Cayley edge in U is mapped to exactly
the equally labelled completed T-transition at its source.
This is the genuine equivariance statement, including negative
edge labels, and not merely a value equality on positive words. -/
theorem universalStageVertexMap_target
    (gen : ι → Γ) (k M : ℕ)
    (T : CompleteEGraph V Edge ι)
    (hsize : Fintype.card V ≤ M)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1)
    (u : V)
    (g : universalStageGroup gen k M) (s : SignedLabel ι) :
    universalStageVertexMap gen k M T hsize hkernel u
      ((cayleyGraph (universalStageGenerator gen k M)).target (g,s)) =
    T.target
      (T.edgeAt (universalStageVertexMap gen k M T hsize hkernel u g) s) := by
  let genU := universalStageGenerator gen k M
  let w := universalStageChosenWord gen k M g
  have hword :
      PSTS.SignedWord.evalGroup genU (w ++ [s]) =
      (cayleyGraph genU).target (g,s) := by
    calc
      PSTS.SignedWord.evalGroup genU (w ++ [s]) =
          PSTS.SignedWord.evalGroup genU w *
            PSTS.SignedWord.evalGroup genU [s] :=
        PSTS.SignedWord.evalGroup_append genU w [s]
      _ = g * PSTS.SignedWord.evalGroupLetter genU s := by
        rw [universalStageChosenWord_eval gen k M g]
        simp [PSTS.SignedWord.evalGroup]
      _ = (cayleyGraph genU).target (g,s) :=
        (cayleyGraph.target_eq_mul_evalGroupLetter genU g s).symm
  calc
    universalStageVertexMap gen k M T hsize hkernel u
        ((cayleyGraph genU).target (g,s)) =
      universalStageVertexMap gen k M T hsize hkernel u
        (PSTS.SignedWord.evalGroup genU (w ++ [s])) :=
        congrArg (universalStageVertexMap gen k M T hsize hkernel u)
          hword.symm
    _ = T.followWord u (w ++ [s]) :=
      universalStageVertexMap_evalGroup gen k M T hsize hkernel u (w ++ [s])
    _ = T.followWord (T.followWord u w) [s] :=
      T.followWord_append u w [s]
    _ = T.target
        (T.edgeAt (universalStageVertexMap gen k M T hsize hkernel u g) s) := by
        change T.followWord (T.followWord u w) [s] =
          T.target (T.edgeAt (T.followWord u w) s)
        rfl

/-- The LITERAL labelled graph morphism from the generated
universal group's Cayley graph to any bounded kernel-correct
finite COMPLETE stage T, based at u. This covers a genuine
oriented graph, not merely a quotient of its word monoid. -/
noncomputable def universalStageCayleyCover
    (gen : ι → Γ) (k M : ℕ)
    (T : CompleteEGraph V Edge ι)
    (hsize : Fintype.card V ≤ M)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1)
    (u : V) :
    LabelledGraphHom
      (cayleyGraph (universalStageGenerator gen k M)).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph where
  onVertex := universalStageVertexMap gen k M T hsize hkernel u
  onEdge := fun e => T.edgeAt
    (universalStageVertexMap gen k M T hsize hkernel u e.1) e.2
  map_source e := T.edgeAt_source _ _
  map_label e := T.edgeAt_label _ _
  map_inv e := by
    rcases e with ⟨g,s⟩
    change
      T.edgeAt
        (universalStageVertexMap gen k M T hsize hkernel u
          ((cayleyGraph (universalStageGenerator gen k M)).target (g,s)))
        (PSTS.SignedLetter.inv s) =
      T.inv (T.edgeAt
        (universalStageVertexMap gen k M T hsize hkernel u g) s)
    rw [universalStageVertexMap_target]
    exact T.edgeAt_inv _ _

/-- The image of the TRUE complete-group Cayley cover is
PRECISELY the full labelled-word-reachable T-component of
the selected basepoint, not the unrelated ambient Γ-coset.
The positive direction uses the chosen word of each element;
the negative direction evaluates the genuine path's word. -/
theorem universalStageCayleyCover_vertex_range
    (gen : ι → Γ) (k M : ℕ)
    (T : CompleteEGraph V Edge ι)
    (hsize : Fintype.card V ≤ M)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1)
    (u : V) :
    Set.range (universalStageCayleyCover gen k M T hsize hkernel u).onVertex =
      {v : V | T.Reachable u v} := by
  change Set.range (universalStageVertexMap gen k M T hsize hkernel u) =
    {v : V | T.Reachable u v}
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨universalStageChosenWord gen k M g, rfl⟩
  · rintro ⟨w,hw⟩
    refine ⟨PSTS.SignedWord.evalGroup
      (universalStageGenerator gen k M) w, ?_⟩
    exact (universalStageVertexMap_evalGroup
      gen k M T hsize hkernel u w).trans hw

/-- The canonical cover also hits EVERY TRUE signed oriented
T-edge whose source lies in the selected reachable component,
including formal inverses and the two tokens of genuine loops. -/
theorem universalStageCayleyCover_edge_range
    (gen : ι → Γ) (k M : ℕ)
    (T : CompleteEGraph V Edge ι)
    (hsize : Fintype.card V ≤ M)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1)
    (u : V) :
    Set.range (universalStageCayleyCover gen k M T hsize hkernel u).onEdge =
      {e : Edge | T.Reachable u (T.source e)} := by
  ext e
  constructor
  · rintro ⟨⟨g,s⟩,rfl⟩
    change T.Reachable u
      (T.source (T.edgeAt
        (universalStageVertexMap gen k M T hsize hkernel u g) s))
    rw [T.edgeAt_source]
    exact
      (universalStageCayleyCover_vertex_range
        gen k M T hsize hkernel u).mp
        ⟨g, rfl⟩
  · intro he
    obtain ⟨g,hg⟩ :=
      (universalStageCayleyCover_vertex_range
        gen k M T hsize hkernel u).mpr he
    refine ⟨(g,T.label e), ?_⟩
    change T.edgeAt
      (universalStageVertexMap gen k M T hsize hkernel u g)
      (T.label e) = e
    apply T.edgeAt_eq
    · exact hg.symm
    · rfl

end ABO
end PSTSEPPA
