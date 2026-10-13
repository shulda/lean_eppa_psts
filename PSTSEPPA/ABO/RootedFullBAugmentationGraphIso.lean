import PSTSEPPA.ABO.RootedFullCosetSignedGraphIso
import PSTSEPPA.ABO.RootedAugmentationGluePointNaturality
import PSTSEPPA.ABO.IsolatedCosetGluing

/-!
# A genuine signed graph isomorphism of FULL old+new B-augmentations

Corrected ABO Definition 5.3 attaches an actual full B-coset at ONE old
vertex whose previous outgoing B-edges are all absent. Both copies of
the attached root are IDENTIFIED; other new coset points retain separate
tags. Two distinct old quotient vertices must NEVER be identified merely
because their ambient Γ coordinates agree.

Suppose we have a genuine vertex- and signed-directed-edge-bijective
labelled graph morphism between old possibly incomplete EGraphs G and H.
Let B⊆A. The actual local generated subgroup Γ[A] with its trivial
completion generators is compared to ambient Γ under translation by r.
At the selected old root, assume the exact no-old-B-edge hypothesis
on BOTH sides, permitting deterministic full-coset augmentation.

The previously checked literal full B-coset signed-graph isomorphism,
the tagged fresh-vertex equivalence and the full gluePoint naturality
then combine into an isomorphism of the actual GLUED signed EGraphs.
Both old and newly completed oriented edges, their signed labels and
formal inverses are preserved and REFLECTED; so are genuine signed paths.

This abstract gluing theorem is reusable independently of rank-two
retractability. The source-specific application still has to supply
the correct Γ[A] root and its translated ambient Γ coordinate,
which are given by the certified source-glued value theorem (#394).
-/

namespace PSTSEPPA
namespace ABO

variable {V W E F ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- The actual old+new signed graph morphism between complete
B-coset AUGMENTATIONS of isomorphic incomplete old EGraphs.

The old and new edge types are a DISJOINT SUM. In particular
two separate tagged old points remain distinct even when their
ambient group coordinates coincide, and every formal signed
inverse is carried by a true oriented edge-token map. -/
noncomputable def rootedFullBAugmentationGraphHom
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) (root : V)
    (hMissingG : ∀ e : E,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : F,
      H.source e = f.onVertex root → signedBase (H.label e) ∉ B) :
    LabelledGraphHom
      (IsolatedCosetGluing.gluedEGraph G
        (trivialCompletionGenerator gen A) B g root hMissingG).toLabelledGraph
      (IsolatedCosetGluing.gluedEGraph H
        gen B (r * (g : Γ)) (f.onVertex root) hMissingH).toLabelledGraph where
  onVertex :=
    rootedLocalAugmentedVertexEquiv
      (f.vertexEquivOfBijective hv) gen A B hBA r g
  onEdge :=
    Equiv.sumCongr (f.edgeEquivOfBijective he)
      (rootedLocalFullCosetEdgeEquiv gen A B hBA r g)
  map_source := by
    intro edge
    cases edge with
    | inl e =>
        change Sum.inl (H.source (f.onEdge e)) =
          Sum.inl (f.onVertex (G.source e))
        exact congrArg Sum.inl (f.map_source e)
    | inr e =>
        let p : IsolatedCosetGluing.CosetPoint
            (trivialCompletionGenerator gen A) B g :=
          ⟨e.1.1, e.2.1⟩
        have hePoint :
            (⟨(rootedLocalFullCosetEdgeEquiv
              gen A B hBA r g e).1.1,
              (rootedLocalFullCosetEdgeEquiv
                gen A B hBA r g e).2.1⟩ :
              IsolatedCosetGluing.CosetPoint
                gen B (r * (g : Γ))) =
            rootedLocalFullCosetPointEquiv
              gen A B hBA r g p := by
          rfl
        change
          IsolatedCosetGluing.gluePoint
            gen B (r * (g : Γ)) (f.onVertex root)
            (⟨(rootedLocalFullCosetEdgeEquiv
              gen A B hBA r g e).1.1,
              (rootedLocalFullCosetEdgeEquiv
                gen A B hBA r g e).2.1⟩ :
              IsolatedCosetGluing.CosetPoint
                gen B (r * (g : Γ))) =
          rootedLocalAugmentedVertexEquiv
            (f.vertexEquivOfBijective hv) gen A B hBA r g
            (IsolatedCosetGluing.gluePoint
              (trivialCompletionGenerator gen A) B g root p)
        rw [hePoint]
        exact (rootedLocal_gluePoint_natural
          (f.vertexEquivOfBijective hv)
          gen A B hBA r g root p).symm
  map_inv := by
    intro edge
    cases edge with
    | inl e =>
        exact congrArg Sum.inl (f.map_inv e)
    | inr e =>
        exact congrArg Sum.inr
          ((rootedLocalFullCosetSignedGraphHom
            gen A B hBA r g).map_inv e)
  map_label := by
    intro edge
    cases edge with
    | inl e => exact f.map_label e
    | inr e => rfl

/-- The COMPLETE glued augmented signed EGraphs are isomorphic
on both vertex carriers and ALL directed oriented old/new edge
tokens, not only on their ambient Γ-coordinate projections. -/
theorem rootedFullBAugmentationGraphHom_bijective
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) (root : V)
    (hMissingG : ∀ e : E,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : F,
      H.source e = f.onVertex root → signedBase (H.label e) ∉ B) :
    Function.Bijective
      (rootedFullBAugmentationGraphHom G H f hv he gen A B hBA r g
        root hMissingG hMissingH).onVertex ∧
    Function.Bijective
      (rootedFullBAugmentationGraphHom G H f hv he gen A B hBA r g
        root hMissingG hMissingH).onEdge := by
  let fv := f.vertexEquivOfBijective hv
  let fe := f.edgeEquivOfBijective he
  change
    Function.Bijective (rootedLocalAugmentedVertexEquiv
      fv gen A B hBA r g) ∧
    Function.Bijective (Equiv.sumCongr
      fe (rootedLocalFullCosetEdgeEquiv gen A B hBA r g))
  exact ⟨(rootedLocalAugmentedVertexEquiv fv gen A B hBA r g).bijective,
    (Equiv.sumCongr fe
      (rootedLocalFullCosetEdgeEquiv gen A B hBA r g)).bijective⟩

/-- The ACTUAL full B-coset augmented EGraphs preserve and
reflect every genuinely realised signed path. Crucially the
old root is shared with the new coset, while no extra identifications
of old tagged quotient points have been introduced. -/
theorem rootedFullBAugmentationGraphHom_follows_iff
    (G : EGraph V E ι) (H : EGraph W F ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) (root : V)
    (hMissingG : ∀ e : E,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : F,
      H.source e = f.onVertex root → signedBase (H.label e) ∉ B)
    (u v : IsolatedCosetGluing.Vertex
      V (trivialCompletionGenerator gen A) B g)
    (w : LabelWord ι) :
    (IsolatedCosetGluing.gluedEGraph G
      (trivialCompletionGenerator gen A) B g root
        hMissingG).Follows u w v ↔
    (IsolatedCosetGluing.gluedEGraph H
      gen B (r * (g : Γ)) (f.onVertex root)
        hMissingH).Follows
      ((rootedFullBAugmentationGraphHom G H f hv he gen A B hBA r g
        root hMissingG hMissingH).onVertex u)
      w
      ((rootedFullBAugmentationGraphHom G H f hv he gen A B hBA r g
        root hMissingG hMissingH).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (rootedFullBAugmentationGraphHom G H f hv he gen A B hBA r g
      root hMissingG hMissingH)
    (rootedFullBAugmentationGraphHom_bijective G H f hv he gen A B hBA r g
      root hMissingG hMissingH).1
    (rootedFullBAugmentationGraphHom_bijective G H f hv he gen A B hBA r g
      root hMissingG hMissingH).2
    u v w

end ABO
end PSTSEPPA
