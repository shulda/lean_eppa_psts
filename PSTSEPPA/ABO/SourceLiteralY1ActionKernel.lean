import PSTSEPPA.ABO.SourceX1ConcreteH1
import PSTSEPPA.ABO.DependentDisjointStages
import PSTSEPPA.ABO.DisjointStageWordKernel
import PSTSEPPA.ABO.FiniteActionStages

/-!
# Literal source Y₁ and its exact signed transition-word kernel

The source's corrected Section 5 starts from X₁, the complete action
of original positive input edges, and forms the LITERAL new complete
stage family

    Y₁ = X₁ ⊔ ⨆_{i ∈ ι} G₁[{i}],

where G₁ is the TRUE transition subgroup T(X₁), and the i-th
new component is the regular Cayley action of the ACTUAL generated
cyclic subgroup G₁[{i}]. Each label j outside {i} acts trivially
on this component; positive and negative loop tokens remain distinct.

This is the genuine disjoint EGraph action, with its true oriented
signed edges and old/new component tags. Its generated transition
group is the PAPER's literal T(Y₁), rather than our earlier
source-shaped abstract synchronized product H₁.

The key first comparison is an EXACT, iff signed-word kernel:
a word acts identically on all of Y₁ if and only if it evaluates
to the identity in G₁ AND in every genuine trivially completed
singleton subgroup G₁[{i}]. This is the algebraic invariant
needed to identify T(Y₁) with our synchronized H₁ in the next
step; that labelled-group isomorphism is NOT claimed in this file.

No completeness claim for the printed selected Z₁, Condition 5.2,
Theorem 4.7 or unconditional PSTS EPPA follows from this alone.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The paper's LITERAL first family of unary Cayley action stages:
one disjoint component for EACH original input-edge label i, on the
true generated G₁[{i}] subgroup, with every outside-i label fixed. -/
noncomputable abbrev sourceLiteralY1UnaryStage
    (src dst : ι → V) :=
  dependentDisjointStage (fun i : ι =>
    cayleyGraph (trivialCompletionGenerator
      (sourceG1Generator src dst) ({i} : Finset ι)))

/-- The exact source first expanded COMPLETE EGraph Y₁:
old X₁ action ⊔ the dependent family of all true G₁[{i}]
Cayley actions. No artificial quotient, chosen representatives
or coordinate collapse of differently tagged vertices. -/
noncomputable abbrev sourceLiteralY1
    (src dst : ι → V) :=
  (sourceX1 src dst).disjointUnion
    (sourceLiteralY1UnaryStage src dst)

/-- A faithful regular right-Cayley action has no additional
signed transition-word relations: its whole permutation action
is the identity iff the chronological signed group value is one.
This includes inverse letters and identity-labelled loops. -/
theorem cayleyWordValue_eq_one_iff_evalGroup
    {Γ : Type*} [Group Γ]
    (gen : ι → Γ) (w : LabelWord ι) :
    (cayleyGraph gen).wordValue w = 1 ↔
      PSTS.SignedWord.evalGroup gen w = 1 := by
  rw [(cayleyGraph gen).wordValue_eq_one_iff_all_vertices_fixed]
  constructor
  · intro hall
    have h := hall (1 : Γ)
    rw [cayleyGraph.followWord_eq_mul_evalGroup] at h
    simpa using h
  · intro h x
    rw [cayleyGraph.followWord_eq_mul_evalGroup, h, mul_one]

/-- EXACT first source Y₁ word kernel: original X₁ transition
group value one AND each true labelled unary Cayley group word
value one. The statement concerns the full completed signed
EGraph, not just evaluation at one selected vertex. -/
theorem sourceLiteralY1_wordValue_eq_one_iff
    (src dst : ι → V) (w : LabelWord ι) :
    (sourceLiteralY1 src dst).wordValue w = 1 ↔
      PSTS.SignedWord.evalGroup
        (sourceG1Generator src dst) w = 1 ∧
      ∀ i : ι,
        PSTS.SignedWord.evalGroup
          (trivialCompletionGenerator
            (sourceG1Generator src dst) ({i} : Finset ι)) w = 1 := by
  let U := fun i : ι =>
    cayleyGraph (trivialCompletionGenerator
      (sourceG1Generator src dst) ({i} : Finset ι))
  change ((sourceX1 src dst).disjointUnion
      (dependentDisjointStage U)).wordValue w = 1 ↔ _
  constructor
  · intro hY
    obtain ⟨hX, hU⟩ :=
      ((sourceX1 src dst).disjointUnion_wordValue_eq_one_iff
        (dependentDisjointStage U) w).mp hY
    have hAll :
        ∀ i : ι, (U i).wordValue w = 1 :=
      (dependentDisjointStage_wordValue_eq_one_iff U w).mp hU
    have hG1 :
        PSTS.SignedWord.evalGroup
          (sourceG1Generator src dst) w = 1 := by
      apply Subtype.ext
      exact ((sourceX1 src dst).evalGroup_transitionSubgroupGenerator_val w).trans hX
    refine ⟨hG1, ?_⟩
    intro i
    exact (cayleyWordValue_eq_one_iff_evalGroup
      (trivialCompletionGenerator
        (sourceG1Generator src dst) ({i} : Finset ι)) w).mp (hAll i)
  · rintro ⟨hG1, hAll⟩
    apply ((sourceX1 src dst).disjointUnion_wordValue_eq_one_iff
      (dependentDisjointStage U) w).mpr
    constructor
    · have hGroupVal :=
        congrArg Subtype.val hG1
      exact ((sourceX1 src dst).evalGroup_transitionSubgroupGenerator_val w).symm.trans
        hGroupVal
    · apply (dependentDisjointStage_wordValue_eq_one_iff U w).mpr
      intro i
      exact (cayleyWordValue_eq_one_iff_evalGroup
        (trivialCompletionGenerator
          (sourceG1Generator src dst) ({i} : Finset ι)) w).mpr (hAll i)

/-- The LITERAL finite Y₁ graph really has finitely many
vertices, even for an empty input alphabet, loops and repeated
labels; every unary subgroup is finite inside the actual G₁. -/
theorem finite_sourceLiteralY1Vertex
    (src dst : ι → V) :
    Finite (V ⊕
      (Σ i : ι,
        generatedSubgroup (sourceG1Generator src dst)
          ({i} : Finset ι))) := by
  classical
  letI : Finite (sourceX1 src dst).transitionGroup :=
    (sourceX1 src dst).finite_transitionGroup
  infer_instance

/-- Consequently the ACTUAL source transition group T(Y₁)
is finite, independently of the earlier synchronized model H₁.
The announced labelled-group identification is a separate gate. -/
theorem finite_sourceLiteralY1TransitionGroup
    (src dst : ι → V) :
    Finite (sourceLiteralY1 src dst).transitionGroup := by
  classical
  letI : Finite (V ⊕
      (Σ i : ι,
        generatedSubgroup (sourceG1Generator src dst)
          ({i} : Finset ι))) :=
    finite_sourceLiteralY1Vertex src dst
  letI : Fintype (V ⊕
      (Σ i : ι,
        generatedSubgroup (sourceG1Generator src dst)
          ({i} : Finset ι))) := Fintype.ofFinite _
  exact (sourceLiteralY1 src dst).finite_transitionGroup

end ABO
end PSTSEPPA
