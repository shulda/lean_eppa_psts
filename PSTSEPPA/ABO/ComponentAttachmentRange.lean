import PSTSEPPA.ABO.ComponentSubgraphIndices
import PSTSEPPA.ABO.MultiCosetMorphismsUnique

/-!
# Lifting attached coset points back into an intrinsic B-component

Fix an actual B-component L of K and a lower alphabet C⊆B.
The natural map of component-tagged attached C-cosets
  Attached_C(L) → Attached_C(K)
is injective.

We now prove a precise partial-surjectivity statement: every tagged
C-coset point of K whose intrinsic C-component lies in the selected
B-component of root is in the image. The point's *ambient coordinate*
can be arbitrary in that tagged C-coset; it need not be a skeleton
vertex.

This is the converse bookkeeping needed to reflect common
intersection-support witnesses from the global coset extension
back into the local multi-coset extension in ABO Lemma 3.20.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every component-tagged C-coset point of K whose C-component
belongs to the chosen intrinsic B-component has a preimage in
the literal B-component's attached C-cosets. -/
theorem componentSubgraphAttachedMap_surj_of_parent
    (B C : Finset ι) (hCB : C ⊆ B)
    (root : K.Vertex)
    (p : K.AttachedCosetVertex C)
    (hparent :
      K.componentIndexMap C B hCB p.1 =
        K.componentClass B root) :
    ∃ q :
      (K.subalphabetComponentSubgraph B root).AttachedCosetVertex C,
      K.componentSubgraphAttachedMap B C hCB root q = p := by
  let L := K.subalphabetComponentSubgraph B root
  obtain ⟨x, hx⟩ := K.componentClass_surjective C p.1
  have hclassB : K.componentClass B x = K.componentClass B root := by
    calc
      K.componentClass B x =
        K.componentIndexMap C B hCB (K.componentClass C x) :=
        (K.componentIndexMap_class C B hCB x).symm
      _ = K.componentIndexMap C B hCB p.1 :=
        congrArg (K.componentIndexMap C B hCB) hx
      _ = K.componentClass B root := hparent
  have hxRoot : K.SubalphabetReachable B root x :=
    K.subalphabetReachable_symm B
      ((K.componentClass_eq_iff B x root).mp hclassB)
  let lx : L.Vertex := K.componentLiftVertex B root x hxRoot
  have hcoset : p.2.1 ∈ generatedLeftCoset gen C x.1 := by
    have heq :
        K.componentAmbientCoset C p.1 =
          generatedLeftCoset gen C x.1 := by
      rw [← hx, K.componentAmbientCoset_class]
    exact (le_of_eq heq) p.2.2
  let q : L.AttachedCosetVertex C :=
    ⟨L.componentClass C lx, ⟨p.2.1, hcoset⟩⟩
  refine ⟨q, ?_⟩
  apply K.attachedValue_injective_of_same_index C
  · exact hx
  · rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
