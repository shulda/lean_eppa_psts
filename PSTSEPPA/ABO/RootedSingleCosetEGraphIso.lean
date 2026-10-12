import PSTSEPPA.ABO.RootedSingleCosetEGraphHom
import PSTSEPPA.ABO.GraphHomInjectivity

/-!
# Full signed E-graph isomorphism of rooted single-B coset extensions

The genuine source/local single-B coset-extension morphism from
RootedSingleCosetEGraphHom is bijective on vertices. Since the
source EGraph is deterministic, its preservation of labels and
vertex injectivity already imply injectivity on ALL oriented
signed edge tokens.

Surjectivity on edges requires a real geometric argument
distinguishing the two non-interchangeable kinds of B-extension
edges: old outside-B edges are pulled back by the certified old
rooted A-component isomorphism, while completed signed B-edges
are pulled back by the true component-TAGGED attached B-coset
bijection. No outside-B edge is invented in the completion.

We prove the resulting labelled E-graph morphism is bijective
on BOTH vertices and oriented signed edges, so it reflects all
true signed paths including formal inverses and loops.
This is a genuine single-B coset-extension graph isomorphism.
The multi-alphabet gluing of different B-summands and all
ABO source augmentations still remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- Injectivity on ALL true signed directed edge tokens
of the rooted single-B coset extension; the two kinds of
edges cannot collapse by label/source determinism. -/
theorem rootedSingleCosetEGraphHom_edge_injective
    (A B : Finset ι) (hBA : B ⊆ A)
    (root : K.Vertex) :
    Function.Injective
      (K.rootedSingleCosetEGraphHom A B hBA root).onEdge := by
  exact (K.rootedSingleCosetEGraphHom A B hBA root).edge_injective_of_vertex_injective
      (K.rootedSingleCosetEGraphHom_vertex_bijective A B hBA root).1

/-- Every target directed edge is the image of an ORIGINAL
source edge of the same kind (old outside B, or freshly
completed inside B). This prevents silently adding any
old edge merely because its endpoints occupy a common coset. -/
theorem rootedSingleCosetEGraphHom_edge_surjective
    (A B : Finset ι) (hBA : B ⊆ A)
    (root : K.Vertex) :
    Function.Surjective
      (K.rootedSingleCosetEGraphHom A B hBA root).onEdge := by
  let L := K.intrinsicComponentLocalSlice A root
  let M := K.subalphabetComponentSubgraph A root
  let f := K.intrinsicComponentLocalHom A root
  intro e
  cases e with
  | inl old =>
      obtain ⟨q, hq⟩ :=
        (K.intrinsicComponentLocalHom_bijective A root).2.2 old.1
      have hOutside : signedBase q.1.2 ∉ B := by
        change signedBase ((L.toEGraph).label q) ∉ B
        have hlabel :
            (L.toEGraph).label q =
              (M.toEGraph).label old.1 := by
          calc
            (L.toEGraph).label q =
                (M.toEGraph).label (f.onEdge q) :=
              (f.map_label q).symm
            _ = (M.toEGraph).label old.1 := by rw [hq]
        rw [hlabel]
        exact old.2
      refine ⟨Sum.inl ⟨q, hOutside⟩, ?_⟩
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hq
  | inr fresh =>
      obtain ⟨q, hq⟩ :=
        K.rootedLocalAttachedCosetMap_surjective A B hBA root fresh.1
      refine ⟨Sum.inr (q, fresh.2), ?_⟩
      apply congrArg Sum.inr
      exact Prod.ext hq rfl

/-- A full labelled graph ISOMORPHISM between the genuinely
incomplete source-rooted and local single-B coset extensions.
It is bijective on actual vertices AND on signed edge tokens. -/
theorem rootedSingleCosetEGraphHom_bijective
    (A B : Finset ι) (hBA : B ⊆ A)
    (root : K.Vertex) :
    Function.Bijective
      (K.rootedSingleCosetEGraphHom A B hBA root).onVertex ∧
    Function.Bijective
      (K.rootedSingleCosetEGraphHom A B hBA root).onEdge := by
  constructor
  · exact K.rootedSingleCosetEGraphHom_vertex_bijective
      A B hBA root
  · exact ⟨K.rootedSingleCosetEGraphHom_edge_injective
      A B hBA root,
      K.rootedSingleCosetEGraphHom_edge_surjective
      A B hBA root⟩

/-- Every realised signed path in a local single-B coset extension
occurs precisely when its image path occurs in the ORIGINAL
rooted ambient single-B extension. This handles B=empty,
B=A, formal inverse letters, and disconnected old graphs. -/
theorem rootedSingleCosetEGraphHom_follows_iff
    (A B : Finset ι) (hBA : B ⊆ A)
    (root : K.Vertex)
    (u v : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex B)
    (w : LabelWord ι) :
    ((K.intrinsicComponentLocalSlice A root).singleCosetEGraph B).Follows u w v ↔
      ((K.subalphabetComponentSubgraph A root).singleCosetEGraph B).Follows
        ((K.rootedSingleCosetEGraphHom A B hBA root).onVertex u)
        w
        ((K.rootedSingleCosetEGraphHom A B hBA root).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (K.rootedSingleCosetEGraphHom A B hBA root)
    (K.rootedSingleCosetEGraphHom_bijective A B hBA root).1
    (K.rootedSingleCosetEGraphHom_bijective A B hBA root).2
    u v w

end CayleySubgraphSpec
end ABO
end PSTSEPPA
