import PSTSEPPA.ABO.ComponentSubgraphIndices
import PSTSEPPA.ABO.ComponentCosetNaturality

/-!
# Parent-component invariance for local coset attachments

Suppose L is the intrinsic B-component of a skeleton K rooted at v.
For every lower alphabet C⊆B, an intrinsic C-component index of L
maps into the unique containing intrinsic B-component of K, namely
the index of v.

This is true on the quotient component indices and on the *tagged*
C-coset extensions, even for C=∅, C=B, repeated/trivial
generators and ambient coset overlaps. The proof uses actual
B-path connectedness of the underlying skeleton component.

The parent-index invariant is the precise condition needed to lift
a global (C∩D)-gluing witness back to the local B-component and
reflect vertex identifications in the multi-coset quotient.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every local C-component index maps, inside K, to the single
intrinsic B-component of the original root. -/
theorem componentSubgraphIndexMap_parent
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex)
    (c : (K.subalphabetComponentSubgraph B root).ComponentIndex C) :
    K.componentIndexMap C B hCB
      (K.componentSubgraphIndexMap B C hCB root c) =
        K.componentClass B root := by
  induction c using Quotient.inductionOn with
  | h x =>
      change
        K.componentClass B
          ((K.subalphabetComponentSubgraphHom B root).onVertex x) =
        K.componentClass B root
      exact (K.componentClass_eq_iff B _ _).2
        (K.subalphabetReachable_symm B
          (K.componentSubgraph_vertex_reachable B root x))

/-- Every component-tagged C-coset point of L, even with an
ambient coordinate outside the original skeleton, has its
image's intrinsic C-component contained in the root B-component. -/
theorem componentSubgraphAttachedMap_parent
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex)
    (p : (K.subalphabetComponentSubgraph B root).AttachedCosetVertex C) :
    K.componentIndexMap C B hCB
      (K.attachedIndex C
        (K.componentSubgraphAttachedMap B C hCB root p)) =
      K.componentClass B root :=
  K.componentSubgraphIndexMap_parent B C hCB root p.1

end CayleySubgraphSpec
end ABO
end PSTSEPPA
