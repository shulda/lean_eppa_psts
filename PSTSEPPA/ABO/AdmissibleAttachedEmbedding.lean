import PSTSEPPA.ABO.ComponentIndexMonotonicity
import PSTSEPPA.ABO.AdmissibleComponentOverlap

/-!
# Admissibility prevents collisions of lower-alphabet tagged coset copies

Suppose C ⊂ B ⊂ A. There is a canonical map from the C-component-indexed
coset copies to the B-component-indexed coset copies, preserving the
ambient group coordinate. Under ABO admissibility, this map is injective.

The obstruction in general is that two different intrinsic C-components
inside one B-component could determine meeting ambient C-cosets. This
is exactly what Definition 3.16 excludes.

The result is one of the essential algebraic ingredients behind the
embeddings CE(G,K;C) ↪ CE(G,K;B) in ABO (3.9). No global injectivity of
the canonical map to the ambient Cayley graph is assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A collision in the containing B-component of two C-component indices
whose ambient C-cosets meet is impossible under admissibility. -/
theorem componentIndex_eq_of_map_eq_and_cosets_meet
    (hadm : K.AdmissibleForCosetExtension)
    (B C : Finset ι)
    (hBA : B ⊂ A) (hCB : C ⊂ B)
    (hsub : C ⊆ B)
    (c d : K.ComponentIndex C)
    (heq :
      K.componentIndexMap C B hsub c =
        K.componentIndexMap C B hsub d)
    (hne :
      (K.componentAmbientCoset C c ∩
        K.componentAmbientCoset C d).Nonempty) :
    c = d := by
  revert heq hne
  refine Quotient.inductionOn c ?_
  intro x
  refine Quotient.inductionOn d ?_
  intro y heq hne
  change K.componentClass B x = K.componentClass B y at heq
  change
    (generatedLeftCoset gen C x.1 ∩
      generatedLeftCoset gen C y.1).Nonempty at hne
  exact
    K.admissible_componentClass_eq_of_cosets_meet
      hadm B C hBA hCB x y
      ((K.componentClass_eq_iff B x y).1 heq) hne

/-- Hence, within a parent B-component, two lower C-coset copies cannot
be identified unless their intrinsic C-component tags were equal. -/
theorem attachedSubalphabetMap_injective_of_admissible
    (hadm : K.AdmissibleForCosetExtension)
    (B C : Finset ι)
    (hBA : B ⊂ A) (hCB : C ⊂ B)
    (hsub : C ⊆ B) :
    Function.Injective (K.attachedSubalphabetMap C B hsub) := by
  intro p q hpq
  rcases p with ⟨c, xc⟩
  rcases q with ⟨d, yd⟩
  have hindex :
      K.componentIndexMap C B hsub c =
        K.componentIndexMap C B hsub d :=
    congrArg (fun z : K.AttachedCosetVertex B => z.1) hpq
  have hvalue : xc.1 = yd.1 :=
    congrArg (fun z : K.AttachedCosetVertex B => z.2.1) hpq
  have hmeet :
      (K.componentAmbientCoset C c ∩
        K.componentAmbientCoset C d).Nonempty := by
    refine ⟨xc.1, xc.2, ?_⟩
    rw [hvalue]
    exact yd.2
  have hcd :=
    K.componentIndex_eq_of_map_eq_and_cosets_meet
      hadm B C hBA hCB hsub c d hindex hmeet
  subst d
  have hxy : xc = yd := Subtype.ext hvalue
  cases hxy
  rfl

end CayleySubgraphSpec

end ABO
end PSTSEPPA
