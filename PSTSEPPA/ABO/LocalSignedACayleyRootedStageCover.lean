import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainOldAnchorCover
import PSTSEPPA.ABO.LocalCosetCayleySlice

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Actual A-labelled Cayley subgraph of the generated subgroup. -/
noncomputable def localSignedACayleySkeleton
    (gen : ι → Γ) (A : Finset ι) :
    CayleySubgraphSpec (trivialCompletionGenerator gen A) A where
  vertices := Set.univ
  edges := {e | signedBase e.2 ∈ A}
  source_mem := by
    intro e he
    trivial
  inv_mem := by
    intro e he
    change signedBase
      ((cayleyGraph (trivialCompletionGenerator gen A)).inv e).2 ∈ A
    rcases e with ⟨x, s⟩
    cases s <;> simpa [signedBase_inv] using he
  label_mem := by
    intro e he
    exact he

/-- The stage morphism restricted to the actual local signed A-edges. -/
noncomputable def CompleteEGraph.cayleyLocalSignedASkeletonHom
    (T : CompleteEGraph V Edge ι)
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (A : Finset ι) (g : Γ) :
    LabelledGraphHom
      ((localSignedACayleySkeleton gen A).toEGraph).toLabelledGraph
      T.toEGraph.toLabelledGraph where
  onVertex := fun x => F.onVertex (g * (x.1 : Γ))
  onEdge := fun e => F.onEdge (g * (e.1.1 : Γ), e.1.2)
  map_source := by
    intro e
    exact F.map_source (g * (e.1.1 : Γ), e.1.2)
  map_inv := by
    intro e
    have he : signedBase e.1.2 ∈ A := e.2
    change
      F.onEdge
        (g * (((cayleyGraph (trivialCompletionGenerator gen A)).inv e.1).1 : Γ),
         ((cayleyGraph (trivialCompletionGenerator gen A)).inv e.1).2) =
      T.inv (F.onEdge (g * (e.1.1 : Γ), e.1.2))
    rw [localCayley_inv_leftTranslate gen A g e.1 he]
    exact F.map_inv (g * (e.1.1 : Γ), e.1.2)
  map_label := by
    intro e
    exact F.map_label (g * (e.1.1 : Γ), e.1.2)

variable {W : Type*} [Fintype W] [DecidableEq W]

noncomputable def sourceLiteralY1X2AllSelectedRootLocalASkeletonHom
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      ((localSignedACayleySkeleton
        (sourceLiteralY1X2AllGenerator src dst) A).toEGraph).toLabelledGraph
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).toEGraph.toLabelledGraph :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).cayleyLocalSignedASkeletonHom
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1X2AllSelectedRootPlainCayleyHom
        src dst base A hcard root) A 1


/-- The local true G[A] identity is carried to the
exact old component-tagged H-root in the printed stage. -/
@[simp] theorem sourceLiteralY1X2AllSelectedRootLocalASkeletonHom_one
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1X2AllSelectedRootLocalASkeletonHom
      src dst base A hcard root).onVertex
        (⟨1, by trivial⟩ :
          (localSignedACayleySkeleton
            (sourceLiteralY1X2AllGenerator src dst) A).Vertex) =
    sourceLiteralY1SelectedRootPlainOldAnchor
      src dst base A hcard root := by
  change
    (sourceLiteralY1X2AllSelectedRootPlainCayleyHom
      src dst base A hcard root).onVertex
        (1 * (1 : (sourceLiteralY1X2AllStage src dst).transitionGroup)) =
    sourceLiteralY1SelectedRootPlainOldAnchor
      src dst base A hcard root
  simpa using sourceLiteralY1X2AllSelectedRootPlainCayleyHom_one
    src dst base A hcard root

end ABO
end PSTSEPPA
