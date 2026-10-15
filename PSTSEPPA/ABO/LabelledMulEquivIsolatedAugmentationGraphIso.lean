import PSTSEPPA.ABO.LabelledMulEquivFreshCosetGlueNaturality
import PSTSEPPA.ABO.BijectiveGraphPathReflection

/-!
# Full OLD+NEW isolated-root B-augmentation signed graph isomorphism

At rank two, corrected ABO Definition 5.3 augments an honest
component-tagged old multi-coset EGraph by gluing a NEW, full
signed B-left coset to ONE selected old root, provided no old
outgoing B-edge is already present. The other coset vertices
remain separately tagged and the old graph is never collapsed
by equality of ambient group coordinates.

The generic old-graph map f is a true signed EGraph isomorphism
on both vertices and formally oriented edges; the NEW coset
is transported by a generator-preserving GROUP equivalence
E : Γ ≃* Δ, without global retractability assumptions. The
new and old gluing is compatible at the exact root via the
separately verified naturality of gluePoint.

We obtain a REAL signed labelled graph isomorphism of the
deterministic old+new augmented EGraphs, preserving and reflecting
all actual signed paths (including negative labels and loops).
The old missing-B-edge premises remain EXPLICIT: no arbitrary
augmentation is asserted to be legal, and identifying the
actual printed T(Y₁) selected type-(2) indices is a later gate.
-/

namespace PSTSEPPA
namespace ABO

variable {V W OldEdge NewEdge ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]

/-- Genuine vertex+oriented-signed-edge labelled graph morphism
between ACTUAL old+new isolated full B-coset augmentations,
under compatible old-graph and labelled-group isomorphisms.

No false equality of unrelated old-tagged points is used. -/
noncomputable def labelledMulEquivIsolatedAugmentationGraphHom
    (G : EGraph V OldEdge ι) (H : EGraph W NewEdge ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (E : Γ ≃* Δ)
    (hgen : ∀ i : ι, E (genΓ i) = genΔ i)
    (B : Finset ι) (g : Γ) (root : V)
    (hMissingG : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : NewEdge,
      H.source e = f.onVertex root → signedBase (H.label e) ∉ B) :
    LabelledGraphHom
      (IsolatedCosetGluing.gluedEGraph G
        genΓ B g root hMissingG).toLabelledGraph
      (IsolatedCosetGluing.gluedEGraph H
        genΔ B (E g) (f.onVertex root) hMissingH).toLabelledGraph where
  onVertex :=
    labelledMulEquivAugmentedVertexEquiv
      genΓ genΔ E hgen (f.vertexEquivOfBijective hv) B g
  onEdge :=
    Equiv.sumCongr (f.edgeEquivOfBijective he)
      (labelledMulEquivFullCosetEdgeEquiv genΓ genΔ E hgen B g)
  map_source := by
    intro edge
    cases edge with
    | inl e =>
        change Sum.inl (H.source (f.onEdge e)) =
          Sum.inl (f.onVertex (G.source e))
        exact congrArg Sum.inl (f.map_source e)
    | inr e =>
        let p : IsolatedCosetGluing.CosetPoint genΓ B g :=
          ⟨e.1.1, e.2.1⟩
        have hePoint :
            (⟨(labelledMulEquivFullCosetEdgeEquiv
              genΓ genΔ E hgen B g e).1.1,
              (labelledMulEquivFullCosetEdgeEquiv
                genΓ genΔ E hgen B g e).2.1⟩ :
              IsolatedCosetGluing.CosetPoint genΔ B (E g)) =
            labelledMulEquivFullCosetPointEquiv
              genΓ genΔ E hgen B g p := by
          apply Subtype.ext
          rfl
        change
          IsolatedCosetGluing.gluePoint
            genΔ B (E g) (f.onVertex root)
            (⟨(labelledMulEquivFullCosetEdgeEquiv
              genΓ genΔ E hgen B g e).1.1,
              (labelledMulEquivFullCosetEdgeEquiv
                genΓ genΔ E hgen B g e).2.1⟩ :
              IsolatedCosetGluing.CosetPoint genΔ B (E g)) =
          labelledMulEquivAugmentedVertexEquiv
            genΓ genΔ E hgen (f.vertexEquivOfBijective hv) B g
            (IsolatedCosetGluing.gluePoint genΓ B g root p)
        rw [hePoint]
        exact (labelledMulEquiv_gluePoint_natural
          genΓ genΔ E hgen (f.vertexEquivOfBijective hv)
          B g root p).symm
  map_inv := by
    intro edge
    cases edge with
    | inl e =>
        exact congrArg Sum.inl (f.map_inv e)
    | inr e =>
        exact congrArg Sum.inr
          ((labelledMulEquivFullCosetSignedGraphHom
            genΓ genΔ E hgen B g).map_inv e)
  map_label := by
    intro edge
    cases edge with
    | inl e => exact f.map_label e
    | inr e =>
        exact (labelledMulEquivFullCosetSignedGraphHom
          genΓ genΔ E hgen B g).map_label e

/-- The whole actual isolated old+new augmentation is
bijective on vertices AND signed directed EDGE TOKENS.
The source root is shared only with the new coset anchor. -/
theorem labelledMulEquivIsolatedAugmentationGraphHom_bijective
    (G : EGraph V OldEdge ι) (H : EGraph W NewEdge ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (E : Γ ≃* Δ)
    (hgen : ∀ i : ι, E (genΓ i) = genΔ i)
    (B : Finset ι) (g : Γ) (root : V)
    (hMissingG : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : NewEdge,
      H.source e = f.onVertex root → signedBase (H.label e) ∉ B) :
    Function.Bijective
      (labelledMulEquivIsolatedAugmentationGraphHom
        G H f hv he genΓ genΔ E hgen B g root
          hMissingG hMissingH).onVertex ∧
    Function.Bijective
      (labelledMulEquivIsolatedAugmentationGraphHom
        G H f hv he genΓ genΔ E hgen B g root
          hMissingG hMissingH).onEdge := by
  let fv := f.vertexEquivOfBijective hv
  let fe := f.edgeEquivOfBijective he
  change
    Function.Bijective (labelledMulEquivAugmentedVertexEquiv
      genΓ genΔ E hgen fv B g) ∧
    Function.Bijective (Equiv.sumCongr
      fe (labelledMulEquivFullCosetEdgeEquiv genΓ genΔ E hgen B g))
  exact ⟨(labelledMulEquivAugmentedVertexEquiv
      genΓ genΔ E hgen fv B g).bijective,
    (Equiv.sumCongr fe
      (labelledMulEquivFullCosetEdgeEquiv genΓ genΔ E hgen B g)).bijective⟩

/-- Every true signed path in the completed old+new
isolated augmented EGraph exists precisely when its image
path exists in the genuine target augmented EGraph. -/
theorem labelledMulEquivIsolatedAugmentationGraphHom_follows_iff
    (G : EGraph V OldEdge ι) (H : EGraph W NewEdge ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (E : Γ ≃* Δ)
    (hgen : ∀ i : ι, E (genΓ i) = genΔ i)
    (B : Finset ι) (g : Γ) (root : V)
    (hMissingG : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hMissingH : ∀ e : NewEdge,
      H.source e = f.onVertex root → signedBase (H.label e) ∉ B)
    (u v : IsolatedCosetGluing.Vertex V genΓ B g)
    (w : LabelWord ι) :
    (IsolatedCosetGluing.gluedEGraph G
      genΓ B g root hMissingG).Follows u w v ↔
    (IsolatedCosetGluing.gluedEGraph H
      genΔ B (E g) (f.onVertex root) hMissingH).Follows
      ((labelledMulEquivIsolatedAugmentationGraphHom
        G H f hv he genΓ genΔ E hgen B g root
          hMissingG hMissingH).onVertex u)
      w
      ((labelledMulEquivIsolatedAugmentationGraphHom
        G H f hv he genΓ genΔ E hgen B g root
          hMissingG hMissingH).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (labelledMulEquivIsolatedAugmentationGraphHom
      G H f hv he genΓ genΔ E hgen B g root
        hMissingG hMissingH)
    (labelledMulEquivIsolatedAugmentationGraphHom_bijective
      G H f hv he genΓ genΔ E hgen B g root
        hMissingG hMissingH).1
    (labelledMulEquivIsolatedAugmentationGraphHom_bijective
      G H f hv he genΓ genΔ E hgen B g root
        hMissingG hMissingH).2 u v w

end ABO
end PSTSEPPA
