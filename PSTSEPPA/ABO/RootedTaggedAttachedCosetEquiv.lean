import PSTSEPPA.ABO.RootedComponentTaggedCosetFibres

/-!
# Source/local isomorphism of genuine component-tagged attached coset copies

The corrected ABO rank-one source covers are actual connected
components of an INCOMPLETE H1-Cayley preimage of the original
oriented input graph, not the whole ambient H1[A] Cayley graph.

After translating such a component by its root to the genuine
local subgroup Γ[A], we already have a bijection on OLD vertices
and directed signed edge tokens (#352), on intrinsic D-component
tags for every D (#361), and an exact matching of the ambient
D-coset point fibres for every D⊆A (#366).Here we assemble these ingredients into an actual equivalence of
the full dependent component-tagged AttachedCosetVertex D types
for every D⊆A. The map transports each point (component tag, coset
coordinate) to (translated tag, rooted ambient coordinate), and
is proved bijective even when distinct component tags happen to
have identical ambient group-coset coordinates. It also:
* maps original old skeleton vertices to their canonical attached
  copies without relabelling or collapsing components;
* commutes with all inclusions D⊆E⊆A of attached coset pieces,
  including D=∅, D=E and formal inverse generator labels.

Thus the COMPLETE constituent tagged-vertex/gluing diagrams for
rooted local coset copies are available in Lean. The remaining
nontrivial work is descending these maps to the multi-coset
GLUED quotient of all attached pieces, transporting the true
signed edge quotient and trivially completing outside labels,
and the full B-augmentation geometry. Condition 5.2, the
higher-rank stage-history invariant and PSTS EPPA remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- For every D⊆A, map genuine LOCAL tagged attached D-coset
points into precisely their rooted ambient counterparts.
Both quotient COMPONENT TAGS and point COORDINATES are changed
by their own independently proved bijections. -/
noncomputable def rootedLocalAttachedCosetMap
    (A D : Finset ι) (hDA : D ⊆ A)
    (root : K.Vertex) :
    (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex D →
      (K.subalphabetComponentSubgraph A root).AttachedCosetVertex D :=
  fun p =>
    ⟨K.rootedLocalComponentIndexEquiv A root D p.1,
      ⟨root.1 * (p.2.1 : Γ),
        (K.rootedLocal_componentAmbientCoset_translate_iff
          A D hDA root p.1 p.2.1).mp p.2.2⟩⟩

@[simp] theorem rootedLocalAttachedCosetMap_index
    (A D : Finset ι) (hDA : D ⊆ A)
    (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex D) :
    (K.subalphabetComponentSubgraph A root).attachedIndex D
      (K.rootedLocalAttachedCosetMap A D hDA root p) =
    K.rootedLocalComponentIndexEquiv A root D p.1 := rfl

@[simp] theorem rootedLocalAttachedCosetMap_value
    (A D : Finset ι) (hDA : D ⊆ A)
    (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex D) :
    (K.subalphabetComponentSubgraph A root).attachedValue D
      (K.rootedLocalAttachedCosetMap A D hDA root p) =
    root.1 * (p.2.1 : Γ) := rfl

/-- Injectivity of the genuine tagged coset map. Distinct
component classes cannot merge, even when their underlying
ambient coordinates happen to belong to the same subgroup coset. -/
theorem rootedLocalAttachedCosetMap_injective
    (A D : Finset ι) (hDA : D ⊆ A)
    (root : K.Vertex) :
    Function.Injective (K.rootedLocalAttachedCosetMap A D hDA root) := by
  intro p q hpq
  apply (K.intrinsicComponentLocalSlice A root).attachedValue_injective_of_same_index D
  · apply (K.rootedLocalComponentIndexEquiv A root D).injective
    exact congrArg
      ((K.subalphabetComponentSubgraph A root).attachedIndex D) hpq
  · apply Subtype.ext
    exact mul_left_cancel
      (congrArg ((K.subalphabetComponentSubgraph A root).attachedValue D) hpq)

/-- Every tagged ambient D-coset point is reached by a
UNIQUE local D-coset point, using the precise reverse coset
fibre theorem for D⊆A and inverse of the component-index
equivalence. No global surjectivity of Γ[A] into Γ. -/
theorem rootedLocalAttachedCosetMap_surjective
    (A D : Finset ι) (hDA : D ⊆ A)
    (root : K.Vertex) :
    Function.Surjective (K.rootedLocalAttachedCosetMap A D hDA root) := by
  intro q
  let F := K.rootedLocalComponentIndexEquiv A root D
  let c : (K.intrinsicComponentLocalSlice A root).ComponentIndex D :=
    F.symm q.1
  have hindex : F c = q.1 := F.apply_symm_apply q.1
  have hy :
      q.2.1 ∈
        (K.subalphabetComponentSubgraph A root).componentAmbientCoset D
          (F c) := by
    rw [hindex]
    exact q.2.2
  obtain ⟨z, hz, _hunique⟩ :=
    K.rootedLocal_componentAmbientCoset_unique_preimage
      A D hDA root c q.2.1 hy
  refine ⟨⟨c, ⟨z, hz.1⟩⟩, ?_⟩
  apply (K.subalphabetComponentSubgraph A root).attachedValue_injective_of_same_index D
  · exact hindex
  · exact hz.2

/-- A genuine dependent equivalence, NOT merely a bijection
of ambient coset coordinates or of untagged attached points. -/
noncomputable def rootedLocalAttachedCosetEquiv
    (A D : Finset ι) (hDA : D ⊆ A)
    (root : K.Vertex) :
    (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex D ≃
      (K.subalphabetComponentSubgraph A root).AttachedCosetVertex D :=
  Equiv.ofBijective (K.rootedLocalAttachedCosetMap A D hDA root)
    ⟨K.rootedLocalAttachedCosetMap_injective A D hDA root,
      K.rootedLocalAttachedCosetMap_surjective A D hDA root⟩

/-- Old source-skeleton vertices remain their correctly
component-tagged old vertices under attached-coset transport. -/
theorem rootedLocalAttachedCosetMap_oldVertex
    (A D : Finset ι) (hDA : D ⊆ A)
    (root : K.Vertex)
    (x : (K.intrinsicComponentLocalSlice A root).Vertex) :
    K.rootedLocalAttachedCosetMap A D hDA root
      ((K.intrinsicComponentLocalSlice A root).attachedOfSkeletonVertex D x) =
    (K.subalphabetComponentSubgraph A root).attachedOfSkeletonVertex D
      ((K.intrinsicComponentLocalHom A root).onVertex x) := by
  apply (K.subalphabetComponentSubgraph A root).attachedValue_injective_of_same_index D
  · exact
      (K.intrinsicComponentLocalSlice A root).componentIndexEquiv_of_graphIso_class
        (K.subalphabetComponentSubgraph A root)
        (K.intrinsicComponentLocalHom A root)
        (K.intrinsicComponentLocalHom_bijective A root).1
        (K.intrinsicComponentLocalHom_bijective A root).2 D x
  · rfl

/-- NATURALITY of the full component-tagged coset transport
under every D⊆E⊆A. The proof uses the naturality of actual
intrinsic COMPONENT-INDEX quotients, not an invalid equality
in the ambient group. -/
theorem rootedLocalAttachedCosetMap_natural
    (A D E : Finset ι)
    (hDA : D ⊆ A) (hDE : D ⊆ E) (hEA : E ⊆ A)
    (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex D) :
    K.rootedLocalAttachedCosetMap A E hEA root
      ((K.intrinsicComponentLocalSlice A root).attachedSubalphabetMap D E hDE p) =
    (K.subalphabetComponentSubgraph A root).attachedSubalphabetMap D E hDE
        (K.rootedLocalAttachedCosetMap A D hDA root p) := by
  apply (K.subalphabetComponentSubgraph A root).attachedValue_injective_of_same_index E
  · exact
      ((K.intrinsicComponentLocalSlice A root).componentIndexEquiv_of_graphIso_natural
          (K.subalphabetComponentSubgraph A root)
          (K.intrinsicComponentLocalHom A root)
          (K.intrinsicComponentLocalHom_bijective A root).1
          (K.intrinsicComponentLocalHom_bijective A root).2
          D E hDE p.1).symm
  · rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
