import PSTSEPPA.ABO.AdmissibleAttachedEmbedding
import PSTSEPPA.ABO.CosetIntersections

/-!
# Common refinements of tagged coset copies (ABO equation 3.9)

Suppose two lower-alphabet attachments are mapped into a common larger
B-component-indexed coset copy, where both lower alphabets are proper
subsets of B and B is proper in the ambient alphabet A.

Admissibility reflects their common ambient group coordinate to an actual
common vertex in the skeleton; retractability then identifies the
intersection of their attached cosets as a coset over the intersection
alphabet. Hence their overlap has a component-tagged witness over
C₁ ∩ C₂ mapping into both original attachments.

The result is uniform under C₁ = C₂, nested alphabets and the empty
intersection. It establishes the vertex-level common-refinement property;
it does not yet construct the multi-alphabet gluing quotient.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every intrinsic component index is represented by a skeleton vertex. -/
theorem componentClass_surjective (B : Finset ι) :
    Function.Surjective (K.componentClass B) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro x
  exact ⟨x, rfl⟩

/-- Vertex-intersection property of component-tagged coset attachments.

If the C₁- and C₂-attachments map to the same point of the B-attachment,
the coincidence is witnessed in the (C₁ ∩ C₂)-attachment and is compatible
with both smaller component indices, not only their ambient coordinates. -/
theorem attachedSubalphabetMap_common_refinement
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C₁ C₂ : Finset ι)
    (hBA : B ⊂ A)
    (hC₁ : C₁ ⊂ B)
    (hC₂ : C₂ ⊂ B)
    (p : K.AttachedCosetVertex C₁)
    (q : K.AttachedCosetVertex C₂)
    (heq :
      K.attachedSubalphabetMap C₁ B hC₁.subset p =
        K.attachedSubalphabetMap C₂ B hC₂.subset q) :
    ∃ r : K.AttachedCosetVertex (C₁ ∩ C₂),
      K.attachedSubalphabetMap (C₁ ∩ C₂) C₁
          (Finset.inter_subset_left) r = p ∧
      K.attachedSubalphabetMap (C₁ ∩ C₂) C₂
          (Finset.inter_subset_right) r = q := by
  obtain ⟨x, hx⟩ := K.componentClass_surjective C₁ p.1
  obtain ⟨y, hy⟩ := K.componentClass_surjective C₂ q.1
  have hpCoset : p.2.1 ∈ generatedLeftCoset gen C₁ x.1 := by
    have hh := p.2.2
    rw [← hx] at hh
    exact hh
  have hqCoset : q.2.1 ∈ generatedLeftCoset gen C₂ y.1 := by
    have hh := q.2.2
    rw [← hy] at hh
    exact hh
  have hval : p.2.1 = q.2.1 := by
    have h := congrArg (K.attachedValue B) heq
    exact h
  have hidx :
      K.componentIndexMap C₁ B hC₁.subset p.1 =
        K.componentIndexMap C₂ B hC₂.subset q.1 := by
    exact congrArg (K.attachedIndex B) heq
  have hxy :
      K.componentClass B x = K.componentClass B y := by
    calc
      K.componentClass B x =
          K.componentIndexMap C₁ B hC₁.subset
            (K.componentClass C₁ x) := by
              rw [K.componentIndexMap_class]
      _ = K.componentIndexMap C₁ B hC₁.subset p.1 :=
        congrArg _ hx
      _ = K.componentIndexMap C₂ B hC₂.subset q.1 := hidx
      _ = K.componentIndexMap C₂ B hC₂.subset
            (K.componentClass C₂ y) := (congrArg _ hy).symm
      _ = K.componentClass B y := by
            rw [K.componentIndexMap_class]
  have hreachB : K.SubalphabetReachable B x y :=
    (K.componentClass_eq_iff B x y).1 hxy
  have hmeet :
      (generatedLeftCoset gen C₁ x.1 ∩
        generatedLeftCoset gen C₂ y.1).Nonempty := by
    refine ⟨p.2.1, hpCoset, ?_⟩
    rw [hval]
    exact hqCoset
  obtain ⟨w, hw₁, hw₂⟩ :=
    hadm B C₁ C₂ hBA hC₁ hC₂ x y hreachB hmeet
  have hwCoset₁ : w.1 ∈ generatedLeftCoset gen C₁ x.1 :=
    K.subalphabetReachable_implies_coset C₁ x w hw₁
  have hwCoset₂ : w.1 ∈ generatedLeftCoset gen C₂ y.1 :=
    K.subalphabetReachable_implies_coset C₂ y w hw₂
  have hinter :=
    generatedLeftCoset_inter gen hgen hret
      C₁ C₂ x.1 y.1 w.1 hwCoset₁ hwCoset₂
  have hpIntersection :
      p.2.1 ∈ generatedLeftCoset gen (C₁ ∩ C₂) w.1 := by
    rw [← hinter]
    exact ⟨hpCoset, by rw [hval]; exact hqCoset⟩
  let r : K.AttachedCosetVertex (C₁ ∩ C₂) :=
    ⟨K.componentClass (C₁ ∩ C₂) w,
      ⟨p.2.1, by
        change p.2.1 ∈ generatedLeftCoset gen (C₁ ∩ C₂) w.1
        exact hpIntersection⟩⟩
  refine ⟨r, ?_, ?_⟩
  · apply K.attachedValue_injective_of_same_index C₁
    · change K.componentClass C₁ w = p.1
      exact ((K.componentClass_eq_iff C₁ x w).2 hw₁).symm.trans hx
    · rfl
  · apply K.attachedValue_injective_of_same_index C₂
    · change K.componentClass C₂ w = q.1
      exact ((K.componentClass_eq_iff C₂ y w).2 hw₂).symm.trans hy
    · exact hval

end CayleySubgraphSpec

end ABO
end PSTSEPPA
