import PSTSEPPA.ABO.ForwardInductionLocalAttachedCosetNaturality

/-!
# ABO Theorem 4.5: tagged local/original attachment bijections reflect exact gluing

The printed forward induction compares the proper coset extension of one
ORIGINAL rooted incomplete C-component with the extension of its genuine
normalized local H[C]-skeleton.

The previously verified D-fibre equivalence and D⊆E naturality are not
enough without REFLECTION of the original (3.10) gluing relation.
We provide that exact converse here, using the genuine bijection on
COMPONENT-TAGGED D-attachments, not merely the shared Γ-coordinate.

For each selected D⊆C the full attached D-fibre map is bijective.
In particular, every original D-attached point has a unique actual
local preimage indexed by its correctly transported signed D-component.
Given two D,E attached points, their original images share one
(D∩E)-tagged old support if and only if their local preimages share
one local (D∩E)-tagged old support.

The forward direction uses accepted enlargement naturality. For the
reverse direction, lift the original intersection witness back into
the true local D∩E attached fibre by surjectivity; the naturality
commuting square and injectivity recover the ORIGINAL local gluing
equalities. All subgroup coordinates and old skeleton tags remain exact.

This is vertex GLUING compatibility in the source ABO Theorem 4.5;
full gluing quotient bijectivity and transport of ACTUAL oriented
signed old/fresh edge tokens are distinct next gates.
No global Γ retractability, fictitious old edges, sorry or new axioms.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Full injection on local attached D-coset points, retaining both
the ACTUAL local signed D-component index and the local group point.
No implication of global ambient Cayley injectivity. -/
theorem intrinsicComponentLocalAttachedMap_injective
    (C D : Finset ι) (hDC : D ⊆ C)
    (root : K.Vertex) :
    Function.Injective
      (K.intrinsicComponentLocalAttachedMap C D hDC root) := by
  let L := K.intrinsicComponentLocalSlice C root
  let O := K.subalphabetComponentSubgraph C root
  intro p q h
  have hIndex :
      p.1 = q.1 := by
    apply (K.intrinsicComponentLocalIndexEquiv C D root).injective
    exact congrArg (fun t : O.AttachedCosetVertex D => t.1) h
  have hValue : L.attachedValue D p = L.attachedValue D q := by
    apply Subtype.ext
    have hMapped :=
      congrArg (fun t : O.AttachedCosetVertex D => t.2.1) h
    change root.1 * (p.2.1 : Γ) =
      root.1 * (q.2.1 : Γ) at hMapped
    exact mul_left_cancel hMapped
  exact L.attachedValue_injective_of_same_index D hIndex hValue

/-- Full surjection on the original rooted C-component's tagged
D-attachments. Every old component tag and every newly attached
group point has a TRUE local Γ[C] preimage; there is no assumption
that Γ[C] equals the whole ambient group. -/
theorem intrinsicComponentLocalAttachedMap_surjective
    (C D : Finset ι) (hDC : D ⊆ C)
    (root : K.Vertex) :
    Function.Surjective
      (K.intrinsicComponentLocalAttachedMap C D hDC root) := by
  let L := K.intrinsicComponentLocalSlice C root
  let O := K.subalphabetComponentSubgraph C root
  intro q
  let F := K.intrinsicComponentLocalIndexEquiv C D root
  let c : L.ComponentIndex D := F.symm q.1
  have hTag : F c = q.1 := F.apply_symm_apply q.1
  have hMem :
      q.2.1 ∈ O.componentAmbientCoset D (F c) := by
    rw [hTag]
    exact q.2.2
  let fibre := K.intrinsicComponentLocalAttachedCosetFibreEquiv
    C D hDC root c
  let v : {x : generatedSubgroup gen C //
      x ∈ L.componentAmbientCoset D c} :=
    fibre.symm ⟨q.2.1, hMem⟩
  refine ⟨⟨c, v⟩, ?_⟩
  apply O.attachedValue_injective_of_same_index D
  · exact hTag
  · change root.1 * (v.1 : Γ) = q.2.1
    calc
      root.1 * (v.1 : Γ) = (fibre v).1 :=
        (K.intrinsicComponentLocalAttachedCosetFibreEquiv_value
          C D hDC root c v).symm
      _ = q.2.1 :=
        congrArg Subtype.val
          (fibre.apply_symm_apply (⟨q.2.1, hMem⟩))

/-- Therefore the full source attachment map is a bijection
on the ENTIRE D-fibre, including new old/fresh completed points. -/
theorem intrinsicComponentLocalAttachedMap_bijective
    (C D : Finset ι) (hDC : D ⊆ C)
    (root : K.Vertex) :
    Function.Bijective
      (K.intrinsicComponentLocalAttachedMap C D hDC root) :=
  ⟨K.intrinsicComponentLocalAttachedMap_injective C D hDC root,
    K.intrinsicComponentLocalAttachedMap_surjective C D hDC root⟩

/-- Exact source (3.10) preservation AND reflection:
D,E⊆C local coset points have common original D∩E support
IF AND ONLY IF their honest normalized local H[C] points have
common local D∩E support.

This is an equivalence of actual original-component-tagged
gluing predicates, not equality of untagged Cayley group values. -/
theorem intrinsicComponentLocalAttachedMap_shareIntersection_iff
    (C D E : Finset ι)
    (hDC : D ⊆ C) (hEC : E ⊆ C)
    (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D)
    (q : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex E) :
    (K.subalphabetComponentSubgraph C root).ShareIntersectionSupport
        D E
        (K.intrinsicComponentLocalAttachedMap C D hDC root p)
        (K.intrinsicComponentLocalAttachedMap C E hEC root q) ↔
      (K.intrinsicComponentLocalSlice C root).ShareIntersectionSupport
        D E p q := by
  let L := K.intrinsicComponentLocalSlice C root
  let O := K.subalphabetComponentSubgraph C root
  constructor
  · intro h
    obtain ⟨s, hsD, hsE⟩ := h
    have hIC : D ∩ E ⊆ C :=
      Finset.inter_subset_left.trans hDC
    obtain ⟨t, ht⟩ :=
      K.intrinsicComponentLocalAttachedMap_surjective
        C (D ∩ E) hIC root s
    refine ⟨t, ?_, ?_⟩
    · apply K.intrinsicComponentLocalAttachedMap_injective
        C D hDC root
      calc
        K.intrinsicComponentLocalAttachedMap C D hDC root
            (L.attachedSubalphabetMap (D ∩ E) D
              Finset.inter_subset_left t) =
          O.attachedSubalphabetMap (D ∩ E) D
            Finset.inter_subset_left
            (K.intrinsicComponentLocalAttachedMap
              C (D ∩ E) hIC root t) :=
          K.intrinsicComponentLocalAttachedMap_natural
            C (D ∩ E) D Finset.inter_subset_left hDC root t
        _ = O.attachedSubalphabetMap (D ∩ E) D
              Finset.inter_subset_left s :=
          congrArg (O.attachedSubalphabetMap
            (D ∩ E) D Finset.inter_subset_left) ht
        _ = K.intrinsicComponentLocalAttachedMap C D hDC root p :=
          hsD
    · apply K.intrinsicComponentLocalAttachedMap_injective
        C E hEC root
      calc
        K.intrinsicComponentLocalAttachedMap C E hEC root
            (L.attachedSubalphabetMap (D ∩ E) E
              Finset.inter_subset_right t) =
          O.attachedSubalphabetMap (D ∩ E) E
            Finset.inter_subset_right
            (K.intrinsicComponentLocalAttachedMap
              C (D ∩ E) hIC root t) :=
          K.intrinsicComponentLocalAttachedMap_natural
            C (D ∩ E) E Finset.inter_subset_right hEC root t
        _ = O.attachedSubalphabetMap (D ∩ E) E
              Finset.inter_subset_right s :=
          congrArg (O.attachedSubalphabetMap
            (D ∩ E) E Finset.inter_subset_right) ht
        _ = K.intrinsicComponentLocalAttachedMap C E hEC root q :=
          hsE
  · exact K.intrinsicComponentLocalAttachedMap_shareIntersection
      C D E hDC hEC root p q

end CayleySubgraphSpec
end ABO
end PSTSEPPA
