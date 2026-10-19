import PSTSEPPA.ABO.ForwardInductionLocalAttachedCosetFibreEquiv
import PSTSEPPA.ABO.MultiCosetOverlap

/-!
# ABO Theorem 4.5: naturality of local/original tagged attachments under D ⊆ E ⊆ C

The printed ABO forward induction uses the TRUE generated subgroup H[C]
with the original rooted C-component normalized at its actual old vertex.
The accepted source localization theorem identifies its incomplete signed
OLD skeleton, while the independently verified complete D-fibre theorem
identifies all NEW attached points for each D ⊆ C.

Here we prove that these fibre maps COMMUTE with every inclusion
D ⊆ E ⊆ C. The component tag is not disposable: naturality is proved
using the exact old signed D-component-index equivalence and its
compatibility with enlargement of the original alphabet.

Consequently the original (D ∩ E)-supported gluing relation is preserved
by the map on actual, original-component-tagged constituent points.
There is NO appeal to injectivity of an ambient coset projection across
different original skeleton components, no fictitious old edges, and no
false assertion about alphabets lying outside the chosen local C group.

This is the constituent-level naturality required before transporting
the entire multi-coset vertex quotient in the source Theorem 4.5.
Reflecting the gluing relation and transporting ACTUAL oriented signed
edge tokens remain separate tasks, not assumptions or axioms.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A genuinely component-tagged D-coset point of the normalized local
H[C] skeleton maps to the corresponding original rooted C-component
D-attachment. On group coordinates the map is LEFT translation by root;
on intrinsic OLD connected-component tags it is the signed-graph
component-index equivalence.

D must belong to the local alphabet: D ⊆ C. -/
noncomputable def intrinsicComponentLocalAttachedMap
    (C D : Finset ι) (hDC : D ⊆ C)
    (root : K.Vertex) :
    (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D →
      (K.subalphabetComponentSubgraph C root).AttachedCosetVertex D :=
  fun p =>
    ⟨K.intrinsicComponentLocalIndexEquiv C D root p.1,
      ⟨root.1 * (p.2.1 : Γ),
        (K.intrinsicComponentLocalIndex_ambientCoset_mem_iff
          C D hDC root p.1 p.2.1).mp p.2.2⟩⟩

/-- The actual old local D-component tag is transported to its
correct original rooted C-component tag. -/
@[simp] theorem intrinsicComponentLocalAttachedMap_index
    (C D : Finset ι) (hDC : D ⊆ C)
    (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D) :
    (K.subalphabetComponentSubgraph C root).attachedIndex D
      (K.intrinsicComponentLocalAttachedMap C D hDC root p) =
      K.intrinsicComponentLocalIndexEquiv C D root p.1 :=
  rfl

/-- Every new attached point has the expected ORIGINAL translated group
coordinate. This is NOT a claim of globally injective ambient projection. -/
@[simp] theorem intrinsicComponentLocalAttachedMap_value
    (C D : Finset ι) (hDC : D ⊆ C)
    (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D) :
    (K.subalphabetComponentSubgraph C root).attachedValue D
      (K.intrinsicComponentLocalAttachedMap C D hDC root p) =
      root.1 * (p.2.1 : Γ) :=
  rfl

/-- EXACT source Theorem-4.5 naturality square, for every
D ⊆ E ⊆ C, INCLUDING the empty and equal-alphabet cases.

No independent representative of either D-component is selected,
and the intrinsic original index is preserved, not suppressed. -/
theorem intrinsicComponentLocalAttachedMap_natural
    (C D E : Finset ι)
    (hDE : D ⊆ E) (hEC : E ⊆ C)
    (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D) :
    K.intrinsicComponentLocalAttachedMap C E hEC root
        ((K.intrinsicComponentLocalSlice C root).attachedSubalphabetMap
          D E hDE p) =
      (K.subalphabetComponentSubgraph C root).attachedSubalphabetMap
        D E hDE
        (K.intrinsicComponentLocalAttachedMap C D
          (hDE.trans hEC) root p) := by
  let L := K.intrinsicComponentLocalSlice C root
  let O := K.subalphabetComponentSubgraph C root
  apply O.attachedValue_injective_of_same_index E
  · change K.intrinsicComponentLocalIndexEquiv C E root
        (L.componentIndexMap D E hDE p.1) =
      O.componentIndexMap D E hDE
        (K.intrinsicComponentLocalIndexEquiv C D root p.1)
    exact (K.intrinsicComponentLocalIndexEquiv_natural
      C D E root hDE p.1).symm
  · rfl

/-- Source (3.10) FORWARD compatibility:
if two actual local tagged constituent points are glued using one
common tagged (D ∩ E)-support, their original rooted C-component
images have the SAME genuine common intersection-support witness.

In particular, the proof does not infer gluing from equal ambient
Cayley coordinates. -/
theorem intrinsicComponentLocalAttachedMap_shareIntersection
    (C D E : Finset ι)
    (hDC : D ⊆ C) (hEC : E ⊆ C)
    (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D)
    (q : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex E)
    (hShare :
      (K.intrinsicComponentLocalSlice C root).ShareIntersectionSupport
        D E p q) :
    (K.subalphabetComponentSubgraph C root).ShareIntersectionSupport
      D E
      (K.intrinsicComponentLocalAttachedMap C D hDC root p)
      (K.intrinsicComponentLocalAttachedMap C E hEC root q) := by
  let L := K.intrinsicComponentLocalSlice C root
  let O := K.subalphabetComponentSubgraph C root
  obtain ⟨s, hsD, hsE⟩ := hShare
  have hIC : D ∩ E ⊆ C := Finset.inter_subset_left.trans hDC
  refine ⟨K.intrinsicComponentLocalAttachedMap C (D ∩ E)
      hIC root s, ?_, ?_⟩
  · calc
      O.attachedSubalphabetMap (D ∩ E) D
          Finset.inter_subset_left
          (K.intrinsicComponentLocalAttachedMap C (D ∩ E)
            hIC root s) =
        K.intrinsicComponentLocalAttachedMap C D hDC root
          (L.attachedSubalphabetMap (D ∩ E) D
            Finset.inter_subset_left s) :=
        (K.intrinsicComponentLocalAttachedMap_natural
          C (D ∩ E) D Finset.inter_subset_left hDC root s).symm
      _ = K.intrinsicComponentLocalAttachedMap C D hDC root p :=
        congrArg (K.intrinsicComponentLocalAttachedMap C D hDC root) hsD
  · calc
      O.attachedSubalphabetMap (D ∩ E) E
          Finset.inter_subset_right
          (K.intrinsicComponentLocalAttachedMap C (D ∩ E)
            hIC root s) =
        K.intrinsicComponentLocalAttachedMap C E hEC root
          (L.attachedSubalphabetMap (D ∩ E) E
            Finset.inter_subset_right s) :=
        (K.intrinsicComponentLocalAttachedMap_natural
          C (D ∩ E) E Finset.inter_subset_right hEC root s).symm
      _ = K.intrinsicComponentLocalAttachedMap C E hEC root q :=
        congrArg (K.intrinsicComponentLocalAttachedMap C E hEC root) hsE

end CayleySubgraphSpec
end ABO
end PSTSEPPA
