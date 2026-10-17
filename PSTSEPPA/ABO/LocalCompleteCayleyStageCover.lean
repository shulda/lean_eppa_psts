import PSTSEPPA.ABO.KStableLocalGeneratedSubgroupQuotient
import PSTSEPPA.ABO.CayleyStageProjection
import PSTSEPPA.ABO.RetractabilitySource
import PSTSEPPA.ABO.CosetConnectivity

/-!
# Genuine complete signed Cayley(G[A]) cover of an A-connected selected stage

The full original printed P_A rank-two stage is LEGALLY completed
by adding ONLY missing stationary signed loops. Its true signed
edge support lies inside the parent A; hence each letter outside
A acts trivially, and no nontrivial outside-A transition remains.

The source induction must cover this entire COMPLETE stage
by Cayley of the *LOCAL* actual group G[A], not merely by
the A-labelled INCOMPLETE local skeleton. We prove a generic
source-faithful construction from the already certified
generator-preserving surjective group quotient

    Q : G ↠ Transition(T).

Suppose each transition outside A is the identity.
Restrict Q to the true generated subgroup G[A]; its image
lies inside Transition(T)[A], which includes naturally
in Transition(T). The resulting homomorphism sends every
COMPLETED generator, including i outside A, to the
corresponding actual signed transition of T. Therefore
it induces a genuine FULL labelled Cayley(G[A])→T
graph morphism, with correct positive/inverse oriented
edge tokens and fixed loops, based at ANY u∈T.

If T is reachable by signed A-words from u, the genuine
local Cayley map covers EVERY T vertex, and since both
graphs are complete and deterministic, covers EVERY
formally oriented signed edge as well. No 2-stability,
whole-G[A]-coset collision or ambient-coordinate
identification is assumed.

Applying this to the literal first-rank P_A stage requires
the separately built true outside-A stationary support
and complete-stage A-connectedness lemmas. No exact Z₁
selection/equivariance, corrected Theorem 4.7(iii),
higher-rank induction or unconditional PSTS EPPA follows.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)
variable {gen : ι → Γ}

/-- Exact local transition homomorphism from the TRUE subgroup G[A],
not an abstract free completion or a quotient of ambient coset tags. -/
noncomputable def localGeneratedStageTransitionHom
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (A : Finset ι) :
    generatedSubgroup gen A →* T.transitionGroup :=
  (generatedSubgroup T.transitionSubgroupGenerator A).subtype.comp
    (Q.localGeneratedSubgroupQuotient A).hom

/-- If every actual completed stage generator outside A is the
identity, the homomorphism from G[A] preserves ALL signed
original generator labels, even those outside A which
were completed by 1 on the local group side. -/
theorem localGeneratedStageTransitionHom_generator
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (A : Finset ι)
    (hOutside : ∀ i : ι, i ∉ A → T.transitionSubgroupGenerator i = 1)
    (i : ι) :
    T.localGeneratedStageTransitionHom Q A
      (trivialCompletionGenerator gen A i) =
      T.transitionSubgroupGenerator i := by
  change
    (((Q.localGeneratedSubgroupQuotient A).hom
      (trivialCompletionGenerator gen A i) :
        generatedSubgroup T.transitionSubgroupGenerator A) :
      T.transitionGroup) = T.transitionSubgroupGenerator i
  rw [(Q.localGeneratedSubgroupQuotient A).map_gen i]
  by_cases hi : i ∈ A
  · exact trivialCompletionGenerator_mem T.transitionSubgroupGenerator A hi
  · simp only [trivialCompletionGenerator_not_mem
        T.transitionSubgroupGenerator A hi, Subgroup.coe_one,
      hOutside i hi]

/-- The genuine COMPLETE signed Cayley(G[A]) morphism to the
actual complete stage T. It sends BOTH signs and
all legally stationary outside-A edges correctly;
no old input edge is fabricated. -/
noncomputable def localGeneratedCayleyStageHom
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (A : Finset ι)
    (hOutside : ∀ i : ι, i ∉ A → T.transitionSubgroupGenerator i = 1)
    (u : V) :
    LabelledGraphHom
      (cayleyGraph (trivialCompletionGenerator gen A)).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph :=
  T.cayleyProjectionFromGroup
    (trivialCompletionGenerator gen A)
    (T.localGeneratedStageTransitionHom Q A)
    (T.localGeneratedStageTransitionHom_generator Q A hOutside)
    u

/-- Exact rooted value of the true local generated Cayley cover. -/
theorem localGeneratedCayleyStageHom_one
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (A : Finset ι)
    (hOutside : ∀ i : ι, i ∉ A → T.transitionSubgroupGenerator i = 1)
    (u : V) :
    (T.localGeneratedCayleyStageHom Q A hOutside u).onVertex 1 = u :=
  T.cayleyProjectionFromGroup_one
    (trivialCompletionGenerator gen A)
    (T.localGeneratedStageTransitionHom Q A)
    (T.localGeneratedStageTransitionHom_generator Q A hOutside)
    u

/-- From one fixed root u, if every genuine stage vertex is reached
by an actual chronological SIGNED word supported on A, the
local Cayley(G[A]) morphism hits EVERY T vertex. -/
theorem localGeneratedCayleyStageHom_vertex_surjective
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (A : Finset ι)
    (hOutside : ∀ i : ι, i ∉ A → T.transitionSubgroupGenerator i = 1)
    (u : V)
    (hConnected : ∀ v : V, ∃ w : LabelWord ι,
      LabelWord.Uses A w ∧ T.followWord u w = v) :
    Function.Surjective (T.localGeneratedCayleyStageHom Q A hOutside u).onVertex := by
  intro v
  obtain ⟨w, _hw, hWord⟩ := hConnected v
  refine ⟨PSTS.SignedWord.evalGroup (trivialCompletionGenerator gen A) w, ?_⟩
  exact (T.cayleyProjectionFromGroup_evalGroup
    (trivialCompletionGenerator gen A)
    (T.localGeneratedStageTransitionHom Q A)
    (T.localGeneratedStageTransitionHom_generator Q A hOutside)
    u w).trans hWord

/-- The full local G[A] action covers EVERY actual oriented SIGNED
edge token in T, including newly inserted stationary inverse loops.
Surjectivity on vertices of a morphism between COMPLETE
deterministic EGraphs already forces edge surjectivity. -/
theorem localGeneratedCayleyStageHom_edge_surjective
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (A : Finset ι)
    (hOutside : ∀ i : ι, i ∉ A → T.transitionSubgroupGenerator i = 1)
    (u : V)
    (hConnected : ∀ v : V, ∃ w : LabelWord ι,
      LabelWord.Uses A w ∧ T.followWord u w = v) :
    Function.Surjective (T.localGeneratedCayleyStageHom Q A hOutside u).onEdge :=
  CompleteEGraph.hom_edge_surjective
    (cayleyGraph (trivialCompletionGenerator gen A)) T
    (T.localGeneratedCayleyStageHom Q A hOutside u)
    (T.localGeneratedCayleyStageHom_vertex_surjective
      Q A hOutside u hConnected)

end CompleteEGraph
end ABO
end PSTSEPPA
