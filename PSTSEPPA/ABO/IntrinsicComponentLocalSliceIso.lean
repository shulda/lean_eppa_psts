import PSTSEPPA.ABO.ComponentSubgraphPaths
import PSTSEPPA.ABO.LocalCosetCayleySlice

/-!
# Every genuine intrinsic component is isomorphic to a local subgroup skeleton

A source-H1-cover is a TRUE connected component of an incomplete
signed Cayley skeleton. It is NOT the full ambient H1[A] coset.
To feed the first corrected ABO stage construction, which expects
a local Cayley skeleton in the actual generated subgroup H1[A],
we must localize the component, preserving precisely its old
vertices and signed edge tokens.

Take ANY CayleySubgraphSpec K over ANY group Γ, a proper or
improper subalphabet B and an actual root. First extract the
literal B-component (realized-path component) subgraph L.
Then left-translate its vertices/edges by root^{-1} into Γ[B].
The previously formalized local coset-slice morphism from this
translated skeleton back to L is always injective.

We show more: because every vertex of the TRUE intrinsic
component is already inside the root Γ[B] coset, the morphism
is SURJECTIVE ON VERTICES AND ON DIRECTED SIGNED EDGE TOKENS.
Consequently it is a bijective labelled-graph morphism, with
no ambient-coordinate collapse, extra Cayley edges, choice
of component representatives or assumptions of retractability.

This supplies the precise component-to-local-K bridge for
indexing source H1-cover components in the finite all-local-K
rank-two catalogue. The coset-extension/gluing identification
of the completed stage is a further obligation.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The genuine B-component old skeleton, translated from
its rooted Γ-coset into the ACTUAL generated subgroup Γ[B].
It retains exactly its true signed directed edges. -/
noncomputable abbrev intrinsicComponentLocalSlice
    (B : Finset ι) (root : K.Vertex) :=
  (K.subalphabetComponentSubgraph B root).leftCosetSlice root.1

/-- The literal labelled morphism from the translated local
component skeleton into the original rooted B-component.
It is never a quotient by equal ambient group values. -/
noncomputable abbrev intrinsicComponentLocalHom
    (B : Finset ι) (root : K.Vertex) :=
  (K.subalphabetComponentSubgraph B root).leftCosetSliceHom root.1

/-- Every vertex of the actual rooted B-component belongs to
the root's ambient B-coset. This is a consequence of a REAL
signed path, not a fictitious ambient-coset completion. -/
theorem intrinsicComponent_all_vertices_in_root_coset
    (B : Finset ι) (root : K.Vertex)
    (y : (K.subalphabetComponentSubgraph B root).Vertex) :
    y.1 ∈ generatedLeftCoset gen B root.1 := by
  obtain ⟨x, hx, hReach⟩ := y.2
  have hxCoset := K.subalphabetReachable_implies_coset B root x hReach
  simpa only [hx] using hxCoset

/-- The translated local H1[B]-skeleton contains EVERY
actual vertex of the original rooted B-component.
No additional group vertex is introduced in either graph. -/
theorem intrinsicComponentLocalHom_vertex_surjective
    (B : Finset ι) (root : K.Vertex) :
    Function.Surjective
      (K.intrinsicComponentLocalHom B root).onVertex := by
  intro y
  exact ((K.subalphabetComponentSubgraph B root).leftCosetSliceHom_vertex_range_iff
    root.1 y).mpr
    (K.intrinsicComponent_all_vertices_in_root_coset B root y)

/-- The translated local component likewise hits EVERY
original oriented signed edge, not just the vertices.
The lifted source is the actual inverse-translated group
coordinate, and its signed edge token is the SAME letter. -/
theorem intrinsicComponentLocalHom_edge_surjective
    (B : Finset ι) (root : K.Vertex) :
    Function.Surjective
      (K.intrinsicComponentLocalHom B root).onEdge := by
  let L := K.subalphabetComponentSubgraph B root
  intro e
  obtain ⟨x, hx⟩ :=
    K.intrinsicComponentLocalHom_vertex_surjective B root
      ((L.toEGraph).source e)
  have hCoord : root.1 * (x.1.1 : Γ) = e.1.1 := by
    have h := congrArg (fun y : L.Vertex => y.1) hx
    exact h
  have he :
      (x.1, e.1.2) ∈ (K.intrinsicComponentLocalSlice B root).edges := by
    change (root.1 * (x.1.1 : Γ), e.1.2) ∈ L.edges
    rw [hCoord]
    exact e.2
  refine ⟨⟨(x.1, e.1.2), he⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext hCoord rfl

/-- Both vertex and signed-edge maps of the rooted local
component translation are genuine bijections. This is
precisely the data of a labelled-graph isomorphism, without
requiring an existing graph-isomorphism API. -/
theorem intrinsicComponentLocalHom_bijective
    (B : Finset ι) (root : K.Vertex) :
    Function.Bijective
      (K.intrinsicComponentLocalHom B root).onVertex ∧
    Function.Bijective
      (K.intrinsicComponentLocalHom B root).onEdge := by
  constructor
  · exact ⟨
      (K.subalphabetComponentSubgraph B root).leftCosetSliceHom_vertex_injective root.1,
      K.intrinsicComponentLocalHom_vertex_surjective B root⟩
  · exact ⟨
      (K.subalphabetComponentSubgraph B root).leftCosetSliceHom_edge_injective root.1,
      K.intrinsicComponentLocalHom_edge_surjective B root⟩

/-- The identity element of Γ[B] represents the selected
original root in its local component skeleton. This is the
canonical normalization needed to compare source covers with
the all-local-K catalogue without a chosen coset transversal. -/
theorem intrinsicComponentLocal_identity_root
    (B : Finset ι) (root : K.Vertex) :
    ∃ x : (K.intrinsicComponentLocalSlice B root).Vertex,
      x.1 = (1 : generatedSubgroup gen B) ∧
      (K.intrinsicComponentLocalHom B root).onVertex x =
        K.componentLiftVertex B root root
          (K.subalphabetReachable_refl B root) := by
  have hmem :
      (1 : generatedSubgroup gen B) ∈
        (K.intrinsicComponentLocalSlice B root).vertices := by
    change root.1 * ((1 : generatedSubgroup gen B) : Γ) ∈
      (K.subalphabetComponentSubgraph B root).vertices
    simp only [Subgroup.coe_one, mul_one]
    exact ⟨root, rfl, K.subalphabetReachable_refl B root⟩
  refine ⟨⟨1, hmem⟩, rfl, ?_⟩
  apply Subtype.ext
  change root.1 * ((1 : generatedSubgroup gen B) : Γ) = root.1
  simp

end CayleySubgraphSpec
end ABO
end PSTSEPPA
