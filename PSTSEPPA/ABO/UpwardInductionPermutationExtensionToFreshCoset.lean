import PSTSEPPA.ABO.TrivialLoopCompletion

/-!
# Extend an actual old transition permutation along an INJECTIVE vertex embedding

The corrected ABO upward Theorem 4.7(iii) nonisolated B-augmentation
keeps ALL original H vertices, though some old B-component vertices
are represented in a new completed full H[B] coset. This is not an
ambient group-coordinate quotient of all old component tags.

For generator labels OUTSIDE B we must retain each original OLD
completed H transition, even when its actual edge crosses the
boundary of the chosen B-component. Newly attached coset points
must be fixed by those outside-B generator transitions.

The general construction below extends ANY actual permutation of
an old carrier X along an INJECTIVE old-vertex embedding f:X→Y:
on the real old image f(X) it acts exactly by f∘σ∘f⁻¹;
on all genuinely new points Y \\ f(X) it fixes each point.
Its inverse is obtained from the actual inverse old permutation.

The extension preserves positive AND inverse action equations
and never collapses distinct original old quotient tags.
This will be used after the real whole-B-component coset
replacement carrier/injective old embedding has been built.
-/

namespace PSTSEPPA
namespace ABO

variable {X Y : Type*}

/-- Apply the old permutation inside the range of an
old-vertex map, leaving every point outside that range fixed.
The injection hypothesis enters in the proof of coherence,
not in this definition. -/
private noncomputable def embeddedPermStep
    (f : X → Y) (σ : Equiv.Perm X) (y : Y) : Y := by
  classical
  exact if h : ∃ x : X, f x = y then
    f (σ (Classical.choose h))
  else y

private theorem embeddedPermStep_image
    (f : X → Y) (hf : Function.Injective f)
    (σ : Equiv.Perm X) (x : X) :
    embeddedPermStep f σ (f x) = f (σ x) := by
  classical
  unfold embeddedPermStep
  split_ifs with h
  · have hChoose : Classical.choose h = x :=
      hf (Classical.choose_spec h)
    rw [hChoose]
  · exact (h ⟨x, rfl⟩).elim

private theorem embeddedPermStep_outside
    (f : X → Y) (σ : Equiv.Perm X) (y : Y)
    (hOutside : ¬ ∃ x : X, f x = y) :
    embeddedPermStep f σ y = y := by
  classical
  simp only [embeddedPermStep, dif_neg hOutside]

/-- Extend a TRUE old permutation to a larger carrier along
an injective map of the old vertices. ALL new points outside
the original image are stationary for this generator; each
old transition maps to its EXACT original permutation image.
The actual signed inverse is extended simultaneously. -/
noncomputable def extendPermAlongEmbedding
    (f : X → Y) (hf : Function.Injective f)
    (σ : Equiv.Perm X) : Equiv.Perm Y where
  toFun := embeddedPermStep f σ
  invFun := embeddedPermStep f σ.symm
  left_inv := by
    intro y
    by_cases h : ∃ x : X, f x = y
    · obtain ⟨x, hx⟩ := h
      subst y
      change embeddedPermStep f σ.symm
        (embeddedPermStep f σ (f x)) = f x
      rw [embeddedPermStep_image f hf σ x]
      rw [embeddedPermStep_image f hf σ.symm (σ x)]
      simp
    · change embeddedPermStep f σ.symm
        (embeddedPermStep f σ y) = y
      rw [embeddedPermStep_outside f σ y h]
      exact embeddedPermStep_outside f σ.symm y h
  right_inv := by
    intro y
    by_cases h : ∃ x : X, f x = y
    · obtain ⟨x, hx⟩ := h
      subst y
      change embeddedPermStep f σ
        (embeddedPermStep f σ.symm (f x)) = f x
      rw [embeddedPermStep_image f hf σ.symm x]
      rw [embeddedPermStep_image f hf σ (σ.symm x)]
      simp
    · change embeddedPermStep f σ
        (embeddedPermStep f σ.symm y) = y
      rw [embeddedPermStep_outside f σ.symm y h]
      exact embeddedPermStep_outside f σ y h

/-- Every original vertex follows EXACTLY its old permutation
when represented by the genuine injection f. -/
theorem extendPermAlongEmbedding_old_action
    (f : X → Y) (hf : Function.Injective f)
    (σ : Equiv.Perm X) (x : X) :
    extendPermAlongEmbedding f hf σ (f x) =
      f (σ x) :=
  embeddedPermStep_image f hf σ x

/-- Its inverse follows EXACTLY the original signed inverse
on original vertices. -/
theorem extendPermAlongEmbedding_old_inverse
    (f : X → Y) (hf : Function.Injective f)
    (σ : Equiv.Perm X) (x : X) :
    (extendPermAlongEmbedding f hf σ).symm (f x) =
      f (σ.symm x) :=
  embeddedPermStep_image f hf σ.symm x

/-- No outside-B action can move a genuinely new coset point
which is not in the image of any original old vertex. -/
theorem extendPermAlongEmbedding_fresh_fixed
    (f : X → Y) (hf : Function.Injective f)
    (σ : Equiv.Perm X) (y : Y)
    (hFresh : ¬ ∃ x : X, f x = y) :
    extendPermAlongEmbedding f hf σ y = y :=
  embeddedPermStep_outside f σ y hFresh

end ABO
end PSTSEPPA
