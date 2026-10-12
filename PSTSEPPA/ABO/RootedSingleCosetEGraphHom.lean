import PSTSEPPA.ABO.RootedCompletedCosetStepNaturality
import PSTSEPPA.ABO.SingleCosetEGraph

/-!
# True signed E-graph maps of rooted source/local single-coset extensions

Take any incomplete ambient labelled Cayley skeleton K, a real
A-connected component rooted at v, and its exact local representation
L in the generated subgroup Γ[A]. Let M be the actual rooted
A-component of K. For every B ⊆ A, the ordinary single-B coset
extension CE(L;B) contains TWO genuinely different edge types:

* old signed edges whose unsigned label lies OUTSIDE B;
* freshly completed signed B-edges on component-tagged full cosets.

No old missing edge is silently completed. The source/local
old-graph bijection (#352) handles the first type, while
the exact rooted attached-coset bijection (#367) and signed
B-transition naturality (#372) handle the second.

This file builds an ACTUAL label-preserving E-graph morphism
CE(L;B) -> CE(M;B), preserving sources, signed labels and both
formal inverse oriented edge tokens, including loops and trivial
generators. It is a genuine geometric step beyond matching
component tags and completed group coordinates. It does not
yet identify the globally glued multi-coset edge quotient,
outside-A trivial completion, augmented B-cosets or source
Condition 5.2 and PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- Genuine morphism between the non-complete single-B coset
E-graphs, retaining the old-outside-B versus newly completed-B
distinction. No ambient-coordinate graph embedding is postulated. -/
noncomputable def rootedSingleCosetEGraphHom
    (A B : Finset ι) (hBA : B ⊆ A) (root : K.Vertex) :
    LabelledGraphHom
      ((K.intrinsicComponentLocalSlice A root).singleCosetEGraph B).toLabelledGraph
      ((K.subalphabetComponentSubgraph A root).singleCosetEGraph B).
        toLabelledGraph := by
  let L := K.intrinsicComponentLocalSlice A root
  let M := K.subalphabetComponentSubgraph A root
  let f := K.intrinsicComponentLocalHom A root
  refine
    { onVertex := K.rootedLocalAttachedCosetMap A B hBA root
      onEdge := ?_
      map_source := ?_
      map_inv := ?_
      map_label := ?_ }
  · intro e
    cases e with
    | inl old =>
        refine Sum.inl ⟨f.onEdge old.1, ?_⟩
        change signedBase ((M.toEGraph).label (f.onEdge old.1)) ∉ B
        rw [f.map_label old.1]
        exact old.2
    | inr fresh =>
        exact Sum.inr
          (K.rootedLocalAttachedCosetMap A B hBA root fresh.1, fresh.2)
  · intro e
    cases e with
    | inl old =>
        change
          M.attachedOfSkeletonVertex B
              ((M.toEGraph).source (f.onEdge old.1)) =
            K.rootedLocalAttachedCosetMap A B hBA root
              (L.attachedOfSkeletonVertex B
                ((L.toEGraph).source old.1))
        rw [K.rootedLocalAttachedCosetMap_oldVertex]
        exact congrArg (M.attachedOfSkeletonVertex B) (f.map_source old.1)
    | inr fresh =>
        rfl
  · intro e
    cases e with
    | inl old =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact f.map_inv old.1
    | inr fresh =>
        apply congrArg Sum.inr
        apply Prod.ext
        · exact K.rootedLocalAttachedCosetMap_cosetStep
            A B hBA root fresh.1 fresh.2
        · rfl
  · intro e
    cases e with
    | inl old =>
        exact f.map_label old.1
    | inr fresh =>
        rfl

/-- The literal vertex action of the genuine single-coset
graph morphism is the certified COMPONENT-TAGGED B-coset
map, including all old skeleton vertices. -/
@[simp] theorem rootedSingleCosetEGraphHom_onVertex
    (A B : Finset ι) (hBA : B ⊆ A) (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex B) :
    (K.rootedSingleCosetEGraphHom A B hBA root).onVertex p =
      K.rootedLocalAttachedCosetMap A B hBA root p := rfl

/-- The source-rooted map of single-B coset extensions is
bijective on all vertices, not merely an injection into
ambient group coordinates. -/
theorem rootedSingleCosetEGraphHom_vertex_bijective
    (A B : Finset ι) (hBA : B ⊆ A) (root : K.Vertex) :
    Function.Bijective
      (K.rootedSingleCosetEGraphHom A B hBA root).onVertex := by
  exact (K.rootedLocalAttachedCosetEquiv A B hBA root).bijective

end CayleySubgraphSpec
end ABO
end PSTSEPPA
