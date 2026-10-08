import PSTSEPPA.ABO.SingleCosetEGraph
import PSTSEPPA.ABO.CayleySubgraphEdgeComponents

/-!
# Embedding the original skeleton in a single-B coset extension

Every old B-labelled edge is represented by its unique corresponding full
B-coset edge, while every old edge outside B remains an original edge token.
The canonical map from the original skeleton is a labelled-graph morphism,
injective on vertices and directed edges.

The essential compatibility condition for old B-edges is *intrinsic*
B-connectivity of their endpoints, not merely equality of their ambient
group cosets. No global injectivity of the extension-to-Cayley morphism is
assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A signed B-edge of the original skeleton agrees with the completed
B-coset step on its source's component-tagged copy. -/
theorem cosetStep_attached_source_eq_target
    (B : Finset ι) (e : K.Edge)
    (he : signedBase e.1.2 ∈ B) :
    K.cosetStep B
        (K.attachedOfSkeletonVertex B ((K.toEGraph).source e))
        ⟨e.1.2, he⟩ =
      K.attachedOfSkeletonVertex B ((K.toEGraph).target e) := by
  apply K.attachedValue_injective_of_same_index B
  · change K.componentClass B ((K.toEGraph).source e) =
      K.componentClass B ((K.toEGraph).target e)
    exact K.componentClass_source_eq_target B e he
  · change
      e.1.1 * PSTS.SignedWord.evalGroupLetter gen e.1.2 =
        ((K.toEGraph).target e).1
    exact (cayleyGraph.target_eq_mul_evalGroupLetter gen e.1.1 e.1.2).symm

/-- Every skeleton edge maps either to its original outside-B edge token,
or to the unique B-labelled edge in its component-tagged coset copy. -/
noncomputable def singleCosetSkeletonEdgeMap
    (B : Finset ι) (e : K.Edge) : K.SingleCosetEdge B :=
  if he : signedBase e.1.2 ∈ B then
    Sum.inr
      (K.attachedOfSkeletonVertex B ((K.toEGraph).source e),
        ⟨e.1.2, he⟩)
  else
    Sum.inl ⟨e, he⟩

theorem singleCosetSkeletonEdgeMap_source
    (B : Finset ι) (e : K.Edge) :
    (K.singleCosetEGraph B).source (K.singleCosetSkeletonEdgeMap B e) =
      K.attachedOfSkeletonVertex B ((K.toEGraph).source e) := by
  by_cases he : signedBase e.1.2 ∈ B
  · simp [singleCosetSkeletonEdgeMap, he, singleCosetEGraph,
      singleCosetLabelledGraph, singleCosetSource]
  · simp [singleCosetSkeletonEdgeMap, he, singleCosetEGraph,
      singleCosetLabelledGraph, singleCosetSource]

theorem singleCosetSkeletonEdgeMap_label
    (B : Finset ι) (e : K.Edge) :
    (K.singleCosetEGraph B).label (K.singleCosetSkeletonEdgeMap B e) =
      (K.toEGraph).label e := by
  by_cases he : signedBase e.1.2 ∈ B
  · simp [singleCosetSkeletonEdgeMap, he, singleCosetEGraph,
      singleCosetLabelledGraph, singleCosetLabel]
  · simp [singleCosetSkeletonEdgeMap, he, singleCosetEGraph,
      singleCosetLabelledGraph, singleCosetLabel]
  all_goals rfl

/-- Reversal does not change the unsigned generator of a skeleton edge. -/
theorem skeletonEdge_inv_signedBase
    (e : K.Edge) :
    signedBase ((K.toEGraph).inv e).1.2 = signedBase e.1.2 := by
  change signedBase ((cayleyGraph gen).label ((cayleyGraph gen).inv e.1)) =
    signedBase ((cayleyGraph gen).label e.1)
  rw [(cayleyGraph gen).label_inv_eq]
  exact signedBase_inv _

/-- The old skeleton edge map preserves formal edge inversion,
including geometric loops and trivial generators. -/
theorem singleCosetSkeletonEdgeMap_inv
    (B : Finset ι) (e : K.Edge) :
    K.singleCosetSkeletonEdgeMap B ((K.toEGraph).inv e) =
      K.singleCosetInv B (K.singleCosetSkeletonEdgeMap B e) := by
  have hbase := K.skeletonEdge_inv_signedBase e
  by_cases he : signedBase e.1.2 ∈ B
  · have hinv : signedBase ((K.toEGraph).inv e).1.2 ∈ B := by
      rw [hbase]
      exact he
    simp only [singleCosetSkeletonEdgeMap, dif_pos hinv, dif_pos he]
    apply congrArg Sum.inr
    apply Prod.ext
    · exact (K.cosetStep_attached_source_eq_target B e he).symm
    · apply Subtype.ext
      exact (K.toEGraph.toLabelledGraph).label_inv_eq e
  · have hinv : signedBase ((K.toEGraph).inv e).1.2 ∉ B := by
      rw [hbase]
      exact he
    simp only [singleCosetSkeletonEdgeMap, dif_neg hinv, dif_neg he]
    apply congrArg Sum.inl
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Canonical labelled-graph morphism embedding the original skeleton in
its single-alphabet coset extension. -/
noncomputable def skeletonToSingleCosetHom
    (B : Finset ι) :
    LabelledGraphHom
      (K.toEGraph).toLabelledGraph
      (K.singleCosetEGraph B).toLabelledGraph where
  onVertex := K.attachedOfSkeletonVertex B
  onEdge := K.singleCosetSkeletonEdgeMap B
  map_source e := K.singleCosetSkeletonEdgeMap_source B e
  map_inv e := K.singleCosetSkeletonEdgeMap_inv B e
  map_label e := K.singleCosetSkeletonEdgeMap_label B e

/-- The old skeleton is embedded injectively on vertices. -/
theorem skeletonToSingleCosetHom_vertex_injective
    (B : Finset ι) :
    Function.Injective (K.skeletonToSingleCosetHom B).onVertex :=
  K.attachedOfSkeletonVertex_injective B

/-- The composite from skeleton edges through the extension to the
ambient Cayley graph is the original literal skeleton inclusion. -/
theorem singleCosetSkeletonEdgeMap_ambient
    (B : Finset ι) (e : K.Edge) :
    (K.singleCosetAmbientHom B).onEdge
      (K.singleCosetSkeletonEdgeMap B e) = e.1 := by
  by_cases he : signedBase e.1.2 ∈ B
  · simp only [singleCosetSkeletonEdgeMap, dif_pos he]
    change (((K.toEGraph).source e).1, e.1.2) = e.1
    rfl
  · simp only [singleCosetSkeletonEdgeMap, dif_neg he]
    change e.1 = e.1
    rfl

/-- The old skeleton is also embedded injectively on directed edges.
This is *not* a claim that the whole extension-to-ambient map is injective. -/
theorem skeletonToSingleCosetHom_edge_injective
    (B : Finset ι) :
    Function.Injective (K.skeletonToSingleCosetHom B).onEdge := by
  intro e f hef
  have h := congrArg (K.singleCosetAmbientHom B).onEdge hef
  change
    (K.singleCosetAmbientHom B).onEdge
        (K.singleCosetSkeletonEdgeMap B e) =
      (K.singleCosetAmbientHom B).onEdge
        (K.singleCosetSkeletonEdgeMap B f) at h
  rw [K.singleCosetSkeletonEdgeMap_ambient B e,
    K.singleCosetSkeletonEdgeMap_ambient B f] at h
  exact Subtype.ext h

end CayleySubgraphSpec
end ABO
end PSTSEPPA
