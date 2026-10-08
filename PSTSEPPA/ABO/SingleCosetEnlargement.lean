import PSTSEPPA.ABO.SingleCosetSkeletonEmbedding
import PSTSEPPA.ABO.AttachedCosetNaturality
import PSTSEPPA.ABO.GraphHomInjectivity

/-!
# Functorial enlargement of a single-alphabet coset extension

For C ⊆ B, every vertex of the completed C-coset extension CE(G,K;C)
maps to the corresponding point in the completed B-coset extension
CE(G,K;B).

For signed directed edges there are two cases:
* A completed C-edge becomes the corresponding completed B-edge.
* An original skeleton edge outside C follows the canonical skeleton
  edge map into CE(G,K;B); it is either retained (label outside B)
  or becomes a completed B-edge (label inside B).

These maps together form a labelled E-graph morphism; this is stronger
than merely embedding component-indexed vertex cosets. Under
admissibility and B ⊂ A, it is injective on both vertices and signed
directed edges. No injectivity of the ambient Cayley projection is used.

The construction includes C=B, C=∅, labels inducing trivial
generators, and geometric loops as literal signed inverse-edge pairs.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Enlarge the directed edge tokens of the C-extension to B.
Outside-C old edges are treated through the already checked
canonical skeleton edge map for the B-extension. -/
noncomputable def singleCosetEdgeEnlarge
    (C B : Finset ι) (hCB : C ⊆ B) :
    K.SingleCosetEdge C → K.SingleCosetEdge B
  | .inl e => K.singleCosetSkeletonEdgeMap B e.1
  | .inr (p, s) =>
      Sum.inr
        (K.attachedSubalphabetMap C B hCB p, ⟨s.1, hCB s.2⟩)

/-- Source incidence commutes with single-alphabet enlargement. -/
theorem singleCosetEdgeEnlarge_source
    (C B : Finset ι) (hCB : C ⊆ B)
    (e : K.SingleCosetEdge C) :
    (K.singleCosetEGraph B).source
        (K.singleCosetEdgeEnlarge C B hCB e) =
      K.attachedSubalphabetMap C B hCB
        ((K.singleCosetEGraph C).source e) := by
  cases e with
  | inl e =>
      calc
        (K.singleCosetEGraph B).source
          (K.singleCosetEdgeEnlarge C B hCB (Sum.inl e)) =
          K.attachedOfSkeletonVertex B
            ((K.toEGraph).source e.1) :=
          K.singleCosetSkeletonEdgeMap_source B e.1
        _ = K.attachedSubalphabetMap C B hCB
            (K.attachedOfSkeletonVertex C
              ((K.toEGraph).source e.1)) :=
          (K.attachedSubalphabetMap_ofSkeletonVertex C B
            hCB ((K.toEGraph).source e.1)).symm
  | inr e =>
      rfl

/-- Enlarging a signed directed edge preserves its signed label. -/
theorem singleCosetEdgeEnlarge_label
    (C B : Finset ι) (hCB : C ⊆ B)
    (e : K.SingleCosetEdge C) :
    (K.singleCosetEGraph B).label
        (K.singleCosetEdgeEnlarge C B hCB e) =
      (K.singleCosetEGraph C).label e := by
  cases e with
  | inl e =>
      exact K.singleCosetSkeletonEdgeMap_label B e.1
  | inr e =>
      rfl

/-- Enlarging a signed directed edge commutes with formal inverse
tokens, not merely the underlying reversed group action. -/
theorem singleCosetEdgeEnlarge_inv
    (C B : Finset ι) (hCB : C ⊆ B)
    (e : K.SingleCosetEdge C) :
    K.singleCosetEdgeEnlarge C B hCB
        ((K.singleCosetEGraph C).inv e) =
      (K.singleCosetEGraph B).inv
        (K.singleCosetEdgeEnlarge C B hCB e) := by
  cases e with
  | inl e =>
      change
        K.singleCosetSkeletonEdgeMap B ((K.toEGraph).inv e.1) =
          K.singleCosetInv B
            (K.singleCosetSkeletonEdgeMap B e.1)
      exact K.singleCosetSkeletonEdgeMap_inv B e.1
  | inr e =>
      apply congrArg Sum.inr
      apply Prod.ext
      · exact K.attachedSubalphabetMap_cosetStep
          C B hCB e.1 e.2
      · apply Subtype.ext
        rfl

/-- Natural labelled graph morphism from CE(G,K;C) to CE(G,K;B)
for every C ⊆ B, without assuming C is proper in B. -/
noncomputable def singleCosetEnlargeHom
    (C B : Finset ι) (hCB : C ⊆ B) :
    LabelledGraphHom
      (K.singleCosetEGraph C).toLabelledGraph
      (K.singleCosetEGraph B).toLabelledGraph where
  onVertex := K.attachedSubalphabetMap C B hCB
  onEdge := K.singleCosetEdgeEnlarge C B hCB
  map_source e := K.singleCosetEdgeEnlarge_source C B hCB e
  map_inv e := K.singleCosetEdgeEnlarge_inv C B hCB e
  map_label e := K.singleCosetEdgeEnlarge_label C B hCB e

/-- Under admissibility, the natural embedding CE(G,K;C) → CE(G,K;B)
is injective on vertices for C ⊆ B ⊂ A. -/
theorem singleCosetEnlargeHom_vertex_injective
    (hadm : K.AdmissibleForCosetExtension)
    (C B : Finset ι) (hCB : C ⊆ B) (hBA : B ⊂ A) :
    Function.Injective (K.singleCosetEnlargeHom C B hCB).onVertex :=
  K.attachedSubalphabetMap_injective_of_admissible_le
    hadm B C hBA hCB

/-- The natural embedding is also injective on signed directed
edge tokens, including formal inverses of geometric loops. -/
theorem singleCosetEnlargeHom_edge_injective
    (hadm : K.AdmissibleForCosetExtension)
    (C B : Finset ι) (hCB : C ⊆ B) (hBA : B ⊂ A) :
    Function.Injective (K.singleCosetEnlargeHom C B hCB).onEdge :=
  (K.singleCosetEnlargeHom C B hCB).edge_injective_of_vertex_injective
    (K.singleCosetEnlargeHom_vertex_injective
      hadm C B hCB hBA)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
