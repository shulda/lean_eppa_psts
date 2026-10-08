import PSTSEPPA.ABO.ComponentSubgraphAdmissibility
import PSTSEPPA.ABO.ComponentIndexedCosets

/-!
# Intrinsic lower components of a literal B-component subgraph

Let L be the actual B-path component of a skeleton K, realised as
a CayleySubgraphSpec on alphabet B. For every D⊆B, two L-vertices
are D-connected inside L if and only if they are D-connected in K.

This equivalence is not a statement about ambient group cosets.
The forward direction maps an actual L-path into K. Conversely,
every D-path of K beginning inside the B-component lifts to L
by the previously checked path-reflection theorem.

Consequently the canonical map from intrinsic D-component indices
of L to those of K is injective. Corresponding tagged attached
D-cosets have the same underlying ambient group coset, and their
canonical embedding retains the component tag accurately.

These facts are needed to compare CE(G,L;P) with the appropriate
subgraph of CE(G,K;P) in ABO Lemma 3.20.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Intrinsic D-paths of the B-component subgraph are exactly the
actual D-paths inherited from K, whenever D⊆B. -/
theorem componentSubgraph_reachable_iff
    (B D : Finset ι) (hDB : D ⊆ B)
    (root : K.Vertex)
    (x y : (K.subalphabetComponentSubgraph B root).Vertex) :
    (K.subalphabetComponentSubgraph B root).SubalphabetReachable D x y ↔
      K.SubalphabetReachable D
        ((K.subalphabetComponentSubgraphHom B root).onVertex x)
        ((K.subalphabetComponentSubgraphHom B root).onVertex y) := by
  constructor
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw, hp.map (K.subalphabetComponentSubgraphHom B root)⟩
  · intro hxy
    let ix := (K.subalphabetComponentSubgraphHom B root).onVertex x
    let iy := (K.subalphabetComponentSubgraphHom B root).onVertex y
    have hxRoot : K.SubalphabetReachable B root ix :=
      K.componentSubgraph_vertex_reachable B root x
    obtain ⟨hyRoot, hpath⟩ :=
      K.reachable_lift_component B D hDB root ix iy hxRoot hxy
    have hx : K.componentLiftVertex B root ix hxRoot = x := by
      apply Subtype.ext
      rfl
    have hy : K.componentLiftVertex B root iy hyRoot = y := by
      apply Subtype.ext
      rfl
    rw [hx, hy] at hpath
    exact hpath

/-- Inclusion of the B-component graph induces a well-defined map
on intrinsic D-component indices, for any D⊆B. -/
def componentSubgraphIndexMap
    (B D : Finset ι) (hDB : D ⊆ B)
    (root : K.Vertex) :
    (K.subalphabetComponentSubgraph B root).ComponentIndex D →
      K.ComponentIndex D :=
  fun c =>
    Quotient.liftOn c
      (fun x =>
        K.componentClass D
          ((K.subalphabetComponentSubgraphHom B root).onVertex x))
      (by
        intro x y hxy
        apply Quotient.sound
        exact (K.componentSubgraph_reachable_iff
          B D hDB root x y).mp hxy)

@[simp]
theorem componentSubgraphIndexMap_class
    (B D : Finset ι) (hDB : D ⊆ B)
    (root : K.Vertex)
    (x : (K.subalphabetComponentSubgraph B root).Vertex) :
    K.componentSubgraphIndexMap B D hDB root
        ((K.subalphabetComponentSubgraph B root).componentClass D x) =
      K.componentClass D
        ((K.subalphabetComponentSubgraphHom B root).onVertex x) :=
  rfl

/-- The induced map on intrinsic D-component indices is injective:
no two D-components of the literal B-subgraph can become connected
by a D-path leaving the chosen B-component in K. -/
theorem componentSubgraphIndexMap_injective
    (B D : Finset ι) (hDB : D ⊆ B)
    (root : K.Vertex) :
    Function.Injective (K.componentSubgraphIndexMap B D hDB root) := by
  intro c d hcd
  induction c using Quotient.inductionOn with
  | h x =>
      induction d using Quotient.inductionOn with
      | h y =>
          apply Quotient.sound
          exact (K.componentSubgraph_reachable_iff
            B D hDB root x y).mpr (Quotient.exact hcd)

/-- An intrinsic D-component of the literal B-subgraph selects
exactly the same ambient left D-coset as its image component in K.
This equality is at the level of actual sets of group points. -/
theorem componentSubgraphAmbientCoset_eq
    (B D : Finset ι) (hDB : D ⊆ B)
    (root : K.Vertex)
    (c : (K.subalphabetComponentSubgraph B root).ComponentIndex D) :
    (K.subalphabetComponentSubgraph B root).componentAmbientCoset D c =
      K.componentAmbientCoset D
        (K.componentSubgraphIndexMap B D hDB root c) := by
  induction c using Quotient.inductionOn with
  | h x =>
      rfl

/-- Canonical injection of tagged D-coset vertices from the
literal B-component subgraph into the original K's D-cosets. -/
def componentSubgraphAttachedMap
    (B D : Finset ι) (hDB : D ⊆ B)
    (root : K.Vertex) :
    (K.subalphabetComponentSubgraph B root).AttachedCosetVertex D →
      K.AttachedCosetVertex D :=
  fun p =>
    ⟨K.componentSubgraphIndexMap B D hDB root p.1,
      ⟨p.2.1, by
        rw [← K.componentSubgraphAmbientCoset_eq B D hDB root p.1]
        exact p.2.2⟩⟩

/-- The induced map of attached D-cosets preserves their group
coordinate; only component indices require bookkeeping. -/
@[simp]
theorem componentSubgraphAttachedMap_value
    (B D : Finset ι) (hDB : D ⊆ B)
    (root : K.Vertex)
    (p : (K.subalphabetComponentSubgraph B root).AttachedCosetVertex D) :
    K.attachedValue D
        (K.componentSubgraphAttachedMap B D hDB root p) =
      (K.subalphabetComponentSubgraph B root).attachedValue D p :=
  rfl

/-- The tagged attached D-coset inclusion is injective, even
if different intrinsic D-components occupy the same group coset. -/
theorem componentSubgraphAttachedMap_injective
    (B D : Finset ι) (hDB : D ⊆ B)
    (root : K.Vertex) :
    Function.Injective (K.componentSubgraphAttachedMap B D hDB root) := by
  intro p q hpq
  apply (K.subalphabetComponentSubgraph B root).attachedValue_injective_of_same_index D
  · apply K.componentSubgraphIndexMap_injective B D hDB root
    exact congrArg (K.attachedIndex D) hpq
  · exact congrArg (K.attachedValue D) hpq

/-- Literal original skeleton vertices agree under the attached
D-coset injection into K. -/
theorem componentSubgraphAttachedMap_skeleton
    (B D : Finset ι) (hDB : D ⊆ B)
    (root : K.Vertex)
    (x : (K.subalphabetComponentSubgraph B root).Vertex) :
    K.componentSubgraphAttachedMap B D hDB root
        ((K.subalphabetComponentSubgraph B root).attachedOfSkeletonVertex D x) =
      K.attachedOfSkeletonVertex D
        ((K.subalphabetComponentSubgraphHom B root).onVertex x) :=
  rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
