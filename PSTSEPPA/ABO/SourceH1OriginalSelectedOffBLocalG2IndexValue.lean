import PSTSEPPA.ABO.SourceLiteralY1SelectedRootAmbientValueNaturality
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootOffBIndexEquiv
import PSTSEPPA.ABO.SourceH1Type2StageCatalogueIndex
import PSTSEPPA.ABO.RootedSourceMultiCosetAmbientValue

/-!
# Genuine original SourceH₁ selected rank-two type-(2) local catalogue index and anchor

A corrected off-B type-(2) stage is NOT specified by a group
coordinate alone: a genuine old component-tagged multi-coset
quotient vertex must lie outside the entire selected B-summand.
The original source-H₁ local Γ[A] normalization provides an
exact bijection of the full off-B dependent stage index with
the actual rank-two (B,z) type-(2) summand of the concrete G₂
all-local catalogue.

This module makes that normalization directly accessible from
ANY original basepoint, any actual old SourceH₁ root and any
genuine selected off-B quotient vertex z, without choosing
coset representatives or assuming global H₁ retractability.
It also records the exact ambient anchor coordinate formula:
sourceValue(z) = root · localValue(localIndex(z)).
This is the only correct anchor for translating freshly
attached full B-left cosets back to the original SourceH₁
covering; it is NOT an injective coordinate map on the
component-tagged old quotient vertices.

The modules do not yet compare the literal printed paper T(Y₁)
complete type-(2) stage with this normalized source stage, nor
establish concrete G₂ action for the printed type-(2) stage or
the entire selected three-kind Z₁ family.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Exact local H₁[A] old signed skeleton of the selected SOURCE
component, rooted at the ORIGINAL H₁ group element. -/
noncomputable abbrev sourceH1OriginalSelectedLocalSkeleton
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : SourceH1 src dst) :=
  ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).intrinsicComponentLocalSlice
    A (⟨root, by trivial⟩ :
      ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).Vertex)

/-- An original source-H₁ selected old rank-two off-B vertex
is an ACTUAL (B,z) stage index of the local Γ[A] type-(2)
family used by the finite input-dependent G₂. The exact
component-tagged B-constituent nonmembership is retained. -/
noncomputable def sourceH1OriginalSelectedOffBLocalG2Index
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : Quotient (sourceH1OriginalRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A)))
    (hOff : ¬ ∃ p : (sourceH1OriginalRootComponent
      src dst base A root).AttachedCosetVertex B,
      sourceH1SelectedRootBInclude
        src dst base A hcard root (allProperCosetFamily A)
        B hBP p = z) :
    CayleySubgraphSpec.rankTwoType2SingletonIndex
      (sourceH1OriginalSelectedLocalSkeleton src dst base A root)
      hcard
       (isGenerated_trivialCompletionGenerator (sourceH1Generator src dst) A)
       (retractable_trivialCompletionGenerator_of_kRetractable
         (sourceH1Generator src dst) 2
         (sourceH1_twoRetractable src dst) A hcard.le) := by
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let hret := sourceH1_twoRetractable src dst
  let P := allProperCosetFamily A
  have hOffK :
      ¬ ∃ p : (K.subalphabetComponentSubgraph A r).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret r P B hBP p = z := by
    change
      (¬ ∃ p : (K.subalphabetComponentSubgraph A r).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret r P B hBP p = z) at hOff
    exact hOff
  exact K.rootedSourceType2CatalogueIndexEquiv A hcard hret r
    ⟨⟨B,hBP⟩, ⟨z,hOffK⟩⟩

/-- The actual selected proper B tag is unchanged by
source-H₁ rooted-local rank-two normalization, including B=∅. -/
@[simp] theorem sourceH1OriginalSelectedOffBLocalG2Index_alphabet
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : Quotient (sourceH1OriginalRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A)))
    (hOff : ¬ ∃ p : (sourceH1OriginalRootComponent
      src dst base A root).AttachedCosetVertex B,
      sourceH1SelectedRootBInclude
        src dst base A hcard root (allProperCosetFamily A)
        B hBP p = z) :
    (sourceH1OriginalSelectedOffBLocalG2Index
      src dst base A hcard root B hBP z hOff).1.1 = B :=
  rfl

/-- Exact root-translated ambient anchor of an actual off-B
SourceH₁ old quotient vertex z. The local coordinate comes
from its selected actual local G₂-index; only the anchor
coordinate is claimed equal, never different old vertex tags. -/
theorem sourceH1OriginalSelectedOffB_ambientValue_eq_root_mul_localValue
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : Quotient (sourceH1OriginalRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A)))
    (hOff : ¬ ∃ p : (sourceH1OriginalRootComponent
      src dst base A root).AttachedCosetVertex B,
      sourceH1SelectedRootBInclude
        src dst base A hcard root (allProperCosetFamily A)
        B hBP p = z) :
    sourceH1OriginalSelectedRootAmbientValue
      src dst base A hcard root (allProperCosetFamily A) z =
    root * (((sourceH1OriginalSelectedLocalSkeleton src dst base A root).multiCosetAmbientValue
      (allProperCosetFamily A)
      ((sourceH1OriginalSelectedLocalSkeleton src dst base A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator (sourceH1Generator src dst) A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        (sourceH1Generator src dst) 2
        (sourceH1_twoRetractable src dst) A hcard.le)
      (sourceH1OriginalSelectedOffBLocalG2Index
        src dst base A hcard root B hBP z hOff).2.1 : SourceH1 src dst)) := by
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let hret := sourceH1_twoRetractable src dst
  let P := allProperCosetFamily A
  let e := K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret r P
  let w := e.symm z
  have hvalue := K.rootedAmbientMultiCosetValue_natural
    A hcard hret r P w
  have hroot : e w = z := e.apply_symm_apply z
  rw [hroot] at hvalue
  change
    K.rootedAmbientMultiCosetValue A hcard hret r P z =
      root * (K.intrinsicComponentLocalSlice A r).multiCosetAmbientValue
        P ((K.intrinsicComponentLocalSlice A r).admissible_of_card_le_two hcard.le)
        (isGenerated_trivialCompletionGenerator (sourceH1Generator src dst) A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          (sourceH1Generator src dst) 2 hret A hcard.le)
        w
  exact hvalue

end ABO
end PSTSEPPA
