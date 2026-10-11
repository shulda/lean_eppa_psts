import PSTSEPPA.ABO.UniversalKernelAllSizesCatalogue
import PSTSEPPA.ABO.CayleyStageProjection
import PSTSEPPA.ABO.TransitionGroupGenerated

/-!
# The universal group genuinely covers its indexed complete stages

The finite universal action construction is useful for corrected ABO
only if its ACTUAL synchronously generated group has graph coverings
of the completed actions, not merely a stable algebraic quotient.
Here we build those maps, without presuming any Cayley embedding of
the completed stages.

For ANY complete E-graph T, the generated synchronized group
H × T(T) has a natural labelled graph morphism from its literal
Cayley graph to T, based at each selected vertex. Both vertex
and directed signed-edge images are EXACTLY the selected reachable
component. The map preserves all positive/inverse paths and its
basepoint is the identity of the synchronized group.

Apply this to every index in the bounded-all-sizes universal stage:
its actual Cayley graph covers each tagged completed permutation
action component. This is the precise graph-facing part of the
universal finite catalogue. It does not yet prove that all source
Definition-5.3 stages occur as indices or the source period/size
bounds needed to put them there.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*} [Fintype ι] [DecidableEq ι]
variable [Group Γ]

namespace SynchronizedProduct

/-- The literal labelled morphism from the Cayley graph of the
TRUE synchronized generated subgroup of Γ × T(T) to the completed
stage T, based at u. Its group homomorphism is the actual second
coordinate projection, not an assumed map to the stage. -/
noncomputable def stageCoverCayleyHom
    (gen : ι → Γ) (T : CompleteEGraph V Edge ι) (u : V) :
    LabelledGraphHom
      (cayleyGraph (generator gen T.transitionSubgroupGenerator)).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph :=
  T.cayleyProjectionFromGroup
    (generator gen T.transitionSubgroupGenerator)
    (sndHom gen T.transitionSubgroupGenerator)
    (sndHom_generator gen T.transitionSubgroupGenerator) u

/-- The identity group element maps to the chosen actual
stage vertex, not merely to an ambient Cayley coordinate. -/
@[simp] theorem stageCoverCayleyHom_one
    (gen : ι → Γ) (T : CompleteEGraph V Edge ι) (u : V) :
    (stageCoverCayleyHom gen T u).onVertex 1 = u := by
  exact T.cayleyProjectionFromGroup_one
    (generator gen T.transitionSubgroupGenerator)
    (sndHom gen T.transitionSubgroupGenerator)
    (sndHom_generator gen T.transitionSubgroupGenerator) u

/-- The exact signed-word path from u is the image of the
corresponding word value in the synchronized group. -/
theorem stageCoverCayleyHom_word
    (gen : ι → Γ) (T : CompleteEGraph V Edge ι)
    (u : V) (w : LabelWord ι) :
    (stageCoverCayleyHom gen T u).onVertex
      (PSTS.SignedWord.evalGroup
        (generator gen T.transitionSubgroupGenerator) w) =
      T.followWord u w := by
  exact T.cayleyProjectionFromGroup_evalGroup
    (generator gen T.transitionSubgroupGenerator)
    (sndHom gen T.transitionSubgroupGenerator)
    (sndHom_generator gen T.transitionSubgroupGenerator) u w

/-- Surjectivity on exactly the true stage component:
the image of the actual synchronized Cayley group is
the set of vertices reachable from the chosen basepoint.
No connectedness assumption and no completion of old edges. -/
theorem stageCoverCayleyHom_vertex_range
    (gen : ι → Γ) (T : CompleteEGraph V Edge ι)
    (u : V) :
    Set.range (stageCoverCayleyHom gen T u).onVertex =
      {v : V | T.Reachable u v} := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    change T.Reachable u
      (T.canonicalVertex u
        (sndHom gen T.transitionSubgroupGenerator g))
    exact T.canonicalVertex_reachable u _
  · intro hv
    obtain ⟨t, ht⟩ := T.reachable_exists_canonicalVertex u hv
    obtain ⟨g, hg⟩ :=
      sndHom_surjective gen T.transitionSubgroupGenerator
        T.transitionSubgroupGenerator_isGenerated t
    refine ⟨g, ?_⟩
    change T.canonicalVertex u
      (sndHom gen T.transitionSubgroupGenerator g) = v
    simpa [hg] using ht

/-- The map also hits EVERY directed signed-edge token
whose source lies in the selected component; it is an
actual labelled E-graph cover onto that component, including
inverse-labelled edges and the two tokens of a geometric loop. -/
theorem stageCoverCayleyHom_edge_range
    (gen : ι → Γ) (T : CompleteEGraph V Edge ι)
    (u : V) :
    Set.range (stageCoverCayleyHom gen T u).onEdge =
      {e : Edge | T.Reachable u (T.source e)} := by
  ext e
  constructor
  · rintro ⟨⟨g, s⟩, rfl⟩
    change T.Reachable u
      (T.source
        (T.edgeAt
          (T.canonicalVertex u
            (sndHom gen T.transitionSubgroupGenerator g)) s))
    rw [T.edgeAt_source]
    exact T.canonicalVertex_reachable u _
  · intro he
    obtain ⟨t, ht⟩ :=
      T.reachable_exists_canonicalVertex u he
    obtain ⟨g, hg⟩ :=
      sndHom_surjective gen T.transitionSubgroupGenerator
        T.transitionSubgroupGenerator_isGenerated t
    refine ⟨(g, T.label e), ?_⟩
    change T.edgeAt
      (T.canonicalVertex u
        (sndHom gen T.transitionSubgroupGenerator g))
      (T.label e) = e
    apply T.edgeAt_eq
    · simpa [hg] using ht.symm
    · rfl

end SynchronizedProduct

variable (gen : ι → Γ) (k M : ℕ)

/-- The actual finite universal generated group constructed from
the all-size tagged permutation-stage catalogue. -/
noncomputable abbrev universalStageGroup :=
  SynchronizedProduct.stageCover gen
    (boundedKernelAllSizesStage gen k M)

/-- Its true distinguished generator family. -/
noncomputable abbrev universalStageGenerator :
    ι → universalStageGroup gen k M :=
  SynchronizedProduct.generator gen
    (boundedKernelAllSizesStage gen k M).transitionSubgroupGenerator

/-- A literal graph morphism from the Cayley graph of the
UNIVERSAL finite group to the whole bounded-size complete
stage, based at any given vertex. -/
noncomputable def universalStageCayleyHom
    (j : boundedKernelAllSizesIndex gen k M)
    (x : Fin j.1.val) :
    LabelledGraphHom
      (cayleyGraph (universalStageGenerator gen k M)).toEGraph.toLabelledGraph
      (boundedKernelAllSizesStage gen k M).toEGraph.toLabelledGraph :=
  SynchronizedProduct.stageCoverCayleyHom gen
    (boundedKernelAllSizesStage gen k M)
    (⟨j, x⟩ : boundedKernelAllSizesVertex gen k M)

/-- The universal Cayley morphism has exact basepoint,
and its value on any signed word is the same true path
as in the selected tagged component. -/
theorem universalStageCayleyHom_word
    (j : boundedKernelAllSizesIndex gen k M)
    (x : Fin j.1.val) (w : LabelWord ι) :
    (universalStageCayleyHom gen k M j x).onVertex
      (PSTS.SignedWord.evalGroup
        (universalStageGenerator gen k M) w) =
      (⟨j, (actionGraph j.2.1).followWord x w⟩ :
        boundedKernelAllSizesVertex gen k M) := by
  exact
    (SynchronizedProduct.stageCoverCayleyHom_word
      gen (boundedKernelAllSizesStage gen k M)
      (⟨j, x⟩ : boundedKernelAllSizesVertex gen k M) w).trans
      (dependentDisjointStage_followWord
        (fun j : boundedKernelAllSizesIndex gen k M =>
          actionGraph j.2.1) j x w)

/-- This one finite universal Cayley group covers the ENTIRE
reachable component of every one of its source-indexed
completed permutation stages (in the tagged disjoint graph). -/
theorem universalStageCayleyHom_vertex_range
    (j : boundedKernelAllSizesIndex gen k M)
    (x : Fin j.1.val) :
    Set.range (universalStageCayleyHom gen k M j x).onVertex =
      {v : boundedKernelAllSizesVertex gen k M |
        (boundedKernelAllSizesStage gen k M).Reachable
          (⟨j, x⟩ : boundedKernelAllSizesVertex gen k M) v} := by
  exact SynchronizedProduct.stageCoverCayleyHom_vertex_range
    gen (boundedKernelAllSizesStage gen k M) ⟨j, x⟩

/-- The same true Cayley cover is also onto every signed
directed edge of the corresponding reachable component. -/
theorem universalStageCayleyHom_edge_range
    (j : boundedKernelAllSizesIndex gen k M)
    (x : Fin j.1.val) :
    Set.range (universalStageCayleyHom gen k M j x).onEdge =
      {e : ActionEdge (boundedKernelAllSizesVertex gen k M) ι |
        (boundedKernelAllSizesStage gen k M).Reachable
          (⟨j, x⟩ : boundedKernelAllSizesVertex gen k M)
          ((boundedKernelAllSizesStage gen k M).source e)} := by
  exact SynchronizedProduct.stageCoverCayleyHom_edge_range
    gen (boundedKernelAllSizesStage gen k M) ⟨j, x⟩

end ABO
end PSTSEPPA
