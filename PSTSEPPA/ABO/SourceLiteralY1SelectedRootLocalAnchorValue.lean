import PSTSEPPA.ABO.SourceLiteralY1SelectedRootAmbientValueNaturality
import PSTSEPPA.ABO.RootedSourceMultiCosetAmbientValue
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootOffBIndexEquiv

/-!
# Genuine two-step original paper T(Y₁) → SourceH₁ → local H₁[A] anchor naturality

The selected original incomplete paper T(Y₁) rank-two A-root has
a true quotient of component-tagged coset points. Its ambient
group value is well-defined but NOT globally injective. The
generator-preserving group isomorphism T(Y₁) ≃* SourceH₁
transports the literal old root quotient and its group value.
The SourceH₁ rooted-component normalization is separately
isomorphic to a truly local H₁[A] skeleton. The corresponding
ambient group values satisfy exactly
  sourceValue(F(z)) = sourceRoot · localValue(e⁻¹(F(z))).

We combine these two previously certified statements to define
the correct local coordinate of EVERY printed original selected
old glued vertex and prove the exact three-way formula. It
requires neither global retractability of H₁ nor membership
in a particular B-coset component; it retains all tagged
quotient data and does NOT use ambient-coordinate injectivity.

This is the last group-anchor calculation needed to identify
fresh B-coset augmentations of literal paper type-(2) stages
with the corresponding root-translated source H₁[A] stages.
The actual dependent signed-completed-stage HEq and finite G₂
action are separate follow-up gates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The actual local H₁[A] group coordinate underlying a
selected old paper quotient vertex, obtained via the REAL
original old-root component-tagged quotient equivalences,
not by identifying equally valued old vertices. -/
noncomputable def literalPaperRootLocalSourceGroupValue
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (z : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root P)) : SourceH1 src dst := by
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex :=
    ⟨(sourceH1EquivLiteralY1Transition src dst).symm root, by trivial⟩
  let e := K.rootedLocalMultiCosetVertexQuotientEquiv
    A hcard (sourceH1_twoRetractable src dst) r P
  let F := sourceLiteralY1RootToH1MultiCosetVertexEquiv
    src dst base A hcard root P
  let w := e.symm (F z)
  exact ((K.intrinsicComponentLocalSlice A r).multiCosetAmbientValue
    P ((K.intrinsicComponentLocalSlice A r).admissible_of_card_le_two hcard.le)
    (isGenerated_trivialCompletionGenerator (sourceH1Generator src dst) A)
    (retractable_trivialCompletionGenerator_of_kRetractable
      (sourceH1Generator src dst) 2
      (sourceH1_twoRetractable src dst) A hcard.le)
    w : SourceH1 src dst)

/-- The canonical selected paper T(Y₁) old-root group value
maps to a TRUE source-H₁ group element which is exactly the
source root times the normalized local H₁[A] group value.
No equality of old component-tagged quotient points is inferred
from equality of these coordinates. -/
theorem literalPaperRootGroupValue_eq_root_mul_sourceLocalValue
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (z : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root P)) :
    (sourceH1EquivLiteralY1Transition src dst).symm
      (sourceLiteralY1SelectedRootAmbientValue
        src dst base A hcard root P z) =
    (sourceH1EquivLiteralY1Transition src dst).symm root *
      literalPaperRootLocalSourceGroupValue
        src dst base A hcard root P z := by
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex :=
    ⟨(sourceH1EquivLiteralY1Transition src dst).symm root, by trivial⟩
  let hret := sourceH1_twoRetractable src dst
  let e := K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret r P
  let F := sourceLiteralY1RootToH1MultiCosetVertexEquiv
    src dst base A hcard root P
  let w := e.symm (F z)
  have hs := sourceLiteralY1SelectedRootAmbientValue_natural
    src dst base A hcard root P z
  have hv := K.rootedAmbientMultiCosetValue_natural
    A hcard hret r P w
  have hw : e w = F z := e.apply_symm_apply (F z)
  rw [hw] at hv
  calc
    (sourceH1EquivLiteralY1Transition src dst).symm
        (sourceLiteralY1SelectedRootAmbientValue
          src dst base A hcard root P z) =
      sourceH1OriginalSelectedRootAmbientValue
        src dst base A hcard
          ((sourceH1EquivLiteralY1Transition src dst).symm root)
          P (F z) := hs
    _ = (sourceH1EquivLiteralY1Transition src dst).symm root *
          literalPaperRootLocalSourceGroupValue
            src dst base A hcard root P z := by
      change
        K.rootedAmbientMultiCosetValue A hcard hret r P (F z) =
        r.1 * ((K.intrinsicComponentLocalSlice A r).multiCosetAmbientValue
          P ((K.intrinsicComponentLocalSlice A r).admissible_of_card_le_two hcard.le)
          (isGenerated_trivialCompletionGenerator (sourceH1Generator src dst) A)
          (retractable_trivialCompletionGenerator_of_kRetractable
            (sourceH1Generator src dst) 2 hret A hcard.le) w : SourceH1 src dst)
      exact hv

end ABO
end PSTSEPPA
