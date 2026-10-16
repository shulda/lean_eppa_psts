import PSTSEPPA.ABO.SourceLiteralY1X2AllRankOne

/-!
# Surjective labelled group-to-stage Cayley projections cover EXACT components

A generator-preserving homomorphism Γ → Transition(T) produces a
based labelled Cayley(Γ) graph morphism to the actual complete
signed stage T. If this homomorphism is SURJECTIVE, we strengthen
the existing exact signed-word endpoint formula:

* ALL and ONLY stage vertices reachable from the selected
  basepoint lie in the vertex image;
* ALL and ONLY formally oriented signed edge tokens whose
  source is reachable lie in the EDGE image.

The latter includes inverse tokens and both distinct fixed-loop
tokens, with no injectivity on any group coordinates assumed.

We then instantiate this generic theorem at the ACTUAL paper
literal second-rank transition group
T(X₂^all), X₂^all = Y₁ ⊔ completed(Z₁^all),
using the independently certified surjective right-summand
transition quotient. This provides the exact finite rank-one
based Cayley-COVER requirement for the genuine printed
all-choice three-kind stage family. Equivariant Definition-5.3
selection, the cluster/embedding/bridge-freeness geometry of
corrected Theorem 4.7, and higher-rank PSTS EPPA remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)

/-- On each formally oriented Cayley edge, the based stage
projection applies the group quotient to the source coordinate
and preserves the signed edge label exactly. -/
@[simp] theorem cayleyProjectionFromGroup_onEdge
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (u : V) (e : ActionEdge Γ ι) :
    (T.cayleyProjectionFromGroup gen φ hφ u).onEdge e =
      T.canonicalEdge u (φ e.1, e.2) :=
  rfl

/-- Surjectivity of the group transition quotient gives
EXACT reachable-stage VERTEX coverage, not merely an
abstract labelled Cayley morphism. -/
theorem cayleyProjectionFromGroup_vertex_range_of_surjective
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (hSurj : Function.Surjective φ)
    (u : V) :
    Set.range (T.cayleyProjectionFromGroup gen φ hφ u).onVertex =
      {v : V | T.Reachable u v} := by
  rw [← T.canonicalVertex_range u]
  ext v
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨φ g, ?_⟩
    simpa only [T.cayleyProjectionFromGroup_onVertex] using hg
  · rintro ⟨g, hg⟩
    obtain ⟨x, hx⟩ := hSurj g
    refine ⟨x, ?_⟩
    simpa only [T.cayleyProjectionFromGroup_onVertex, hx] using hg

/-- With a surjective transition quotient, every complete
formally oriented STAGE EDGE whose source is reachable is
actually in the based Cayley edge image. Exact on both
positive and inverse tokens, including stationary loops. -/
theorem cayleyProjectionFromGroup_edge_range_of_surjective
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (hSurj : Function.Surjective φ)
    (u : V) :
    Set.range (T.cayleyProjectionFromGroup gen φ hφ u).onEdge =
      {e : Edge | T.Reachable u (T.source e)} := by
  rw [← T.canonicalEdge_range u]
  ext e
  constructor
  · rintro ⟨⟨g, s⟩, he⟩
    refine ⟨(φ g, s), ?_⟩
    simpa only [T.cayleyProjectionFromGroup_onEdge] using he
  · rintro ⟨⟨h, s⟩, he⟩
    obtain ⟨g, hg⟩ := hSurj h
    refine ⟨(g, s), ?_⟩
    simpa only [T.cayleyProjectionFromGroup_onEdge, hg] using he

end CompleteEGraph

variable {V₀ : Type*} [Fintype V₀] [DecidableEq V₀]

/-- Actual literal paper T(X₂^all) based Cayley map has image
EXACTLY the reachable old/fresh vertices of the selected
genuine printed three-kind stage, preserving all stage tags. -/
theorem sourceLiteralY1X2AllCayleyToThreeKind_vertex_range
    (src dst : ι → V₀)
    (u : Σ j : sourceLiteralY1ThreeKindIndex src dst,
      sourceLiteralY1ThreeKindStageVertex src dst j) :
    Set.range
      (sourceLiteralY1X2AllCayleyToThreeKind src dst u).onVertex =
      {v | (sourceLiteralY1ThreeKindStage src dst).Reachable u v} :=
  (sourceLiteralY1ThreeKindStage src dst).cayleyProjectionFromGroup_vertex_range_of_surjective
    (sourceLiteralY1X2AllGenerator src dst)
    (sourceLiteralY1X2AllToThreeKind src dst).hom
    (sourceLiteralY1X2AllToThreeKind src dst).map_gen
    (sourceLiteralY1X2AllToThreeKind src dst).surjective
    u

/-- Exact formal directed signed EDGE-token coverage for every
actual old/fresh printed stage, including both orientations and
legally completed loops. This is the full geometric based
cover requirement for the current first-rank all-choice family. -/
theorem sourceLiteralY1X2AllCayleyToThreeKind_edge_range
    (src dst : ι → V₀)
    (u : Σ j : sourceLiteralY1ThreeKindIndex src dst,
      sourceLiteralY1ThreeKindStageVertex src dst j) :
    Set.range
      (sourceLiteralY1X2AllCayleyToThreeKind src dst u).onEdge =
      {e : ActionEdge
        (Σ j : sourceLiteralY1ThreeKindIndex src dst,
          sourceLiteralY1ThreeKindStageVertex src dst j) ι |
        (sourceLiteralY1ThreeKindStage src dst).Reachable u
          ((sourceLiteralY1ThreeKindStage src dst).source e)} :=
  (sourceLiteralY1ThreeKindStage src dst).cayleyProjectionFromGroup_edge_range_of_surjective
    (sourceLiteralY1X2AllGenerator src dst)
    (sourceLiteralY1X2AllToThreeKind src dst).hom
    (sourceLiteralY1X2AllToThreeKind src dst).map_gen
    (sourceLiteralY1X2AllToThreeKind src dst).surjective
    u

end ABO
end PSTSEPPA
