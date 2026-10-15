import PSTSEPPA.ABO.SourceLiteralY1SelectedRootAmbientValue
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootRawGraphIso
import PSTSEPPA.ABO.LabelledIsoTaggedCosetTransport

/-!
# Corrected ABO selected T(Y₁)/SourceH₁ root quotient AMBIENT VALUE naturality

The literal paper rank-two original old A-component has a genuine
component-tagged, intersection-support-glued quotient. Its ambient
coordinate is well-defined without global retractability and is
NOT injective. The corresponding source-H₁ A-component has a
separately verified ambient coordinate from local H₁[A] geometry.

Under the true generator-preserving group isomorphism
E : T(Y₁) ≃* SourceH₁, every attached B-coset coordinate is
mapped exactly by E, without forgetting the intrinsic old
B-path component tag. We lift this equality through the EXACT
selected raw-gluing quotient and its already certified paper→
source vertex equivalence, obtaining a true value-naturality
equation for every completed rank-two selected root vertex.

This is essential for corrected off-B type-(2) augmented stages:
the added B-left coset is anchored at the real group coordinate
of the selected quotient vertex and MUST commute with paper/
source identification. The function is not an embedding and does
not collapse tagged points with equal group values.

No signed B-augmentation EGraph or final Z₁ theorem here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Genuine ambient SourceH₁ group value of one original-root
rank-two glued coset quotient vertex, without global H₁
retractability. -/
noncomputable def sourceH1OriginalSelectedRootAmbientValue
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (P : CosetFamilySpec A)
    (z : Quotient
      (sourceH1OriginalRootMultiCosetSetoid
        src dst base A hcard root P)) :
    SourceH1 src dst :=
  ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).rootedAmbientMultiCosetValue
    A hcard (sourceH1_twoRetractable src dst)
    (⟨root, by trivial⟩ :
      ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).Vertex)
    P z

/-- The true root signed graph/group equivalence transports
the ambient coordinate of EVERY separately tagged B-coset
point exactly by T(Y₁)≃*SourceH₁, not merely at old vertices. -/
theorem sourceLiteralY1DirectRootTaggedBCosetEquiv_value
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (p : (sourceLiteralY1DirectRootComponent
      src dst base A root).AttachedCosetVertex B) :
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).attachedValue B
      (sourceLiteralY1DirectRootTaggedBCosetEquiv
        src dst base A root B p) =
    (sourceH1EquivLiteralY1Transition src dst).symm
      ((sourceLiteralY1DirectRootComponent
        src dst base A root).attachedValue B p) := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  let K := sourceH1OriginalRootComponent src dst base A
    ((sourceH1EquivLiteralY1Transition src dst).symm root)
  let f := sourceLiteralY1DirectRootComponentGraphHom src dst base A root
  let hb := sourceLiteralY1DirectRootComponentGraphHom_bijective src dst base A root
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  have hc : ∀ x : L.Vertex, E x.1 = (f.onVertex x).1 := by
    intro x
    rfl
  exact L.attachedCosetEquivOfLabelledGroupIso_value
    K f hb.1 hb.2 E
    (sourceLiteralY1Generator_to_sourceH1 src dst) hc B p

/-- The literal paper T(Y₁) ambient value at EVERY genuinely
glued original rank-two vertex agrees with the true source-H₁
value after exact vertex transport by the labelled group
isomorphism. Does NOT assert either value map is injective. -/
theorem sourceLiteralY1SelectedRootAmbientValue_natural
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (z : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root P)) :
    (sourceH1EquivLiteralY1Transition src dst).symm
      (sourceLiteralY1SelectedRootAmbientValue
        src dst base A hcard root P z) =
    sourceH1OriginalSelectedRootAmbientValue
      src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root)
        P (sourceLiteralY1RootToH1MultiCosetVertexEquiv
          src dst base A hcard root P z) := by
  induction z using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨b, p⟩
    rw [sourceLiteralY1RootToH1MultiCosetVertexEquiv_mk]
    change
      (sourceH1EquivLiteralY1Transition src dst).symm
        ((sourceLiteralY1DirectRootComponent src dst base A root).attachedValue b.1 p) =
      (sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).attachedValue b.1
        (sourceLiteralY1DirectRootTaggedBCosetEquiv
          src dst base A root b.1 p)
    exact (sourceLiteralY1DirectRootTaggedBCosetEquiv_value
      src dst base A root b.1 p).symm

end ABO
end PSTSEPPA
