import PSTSEPPA.ABO.SourceLiteralY1RootMultiCosetSetoid
import PSTSEPPA.ABO.RootedSourceMultiCosetAmbientValue

/-!
# True ambient group coordinate of selected paper T(Y₁) rank-two coset quotient

At the first corrected ABO rank, the actual original signed
T(Y₁) old A-component (|A|=2) is extended by separately
INTRINSIC-component-tagged full B-left cosets, then quotiented
by exact common (B∩C)-support. The new Lean-certified selected
paper root Setoid is precisely that literal relation, even
though the ambient group T(Y₁) is NOT globally retractable.

We show directly that every glued selected paper vertex has a
WELL-DEFINED ambient group value: common intersection-support
implies equality of true group coordinates. The value function
is induced from the actual attached coset point value; it is
NOT assumed injective, and hence DOES NOT collapse distinct
intrinsic component-tagged points sharing ambient coordinates.

The defining inclusion formula is especially important for
the corrected B-augmentation type-(2) at an off-B quotient
vertex: the added full B-left coset must be anchored at this
ACTUAL group value, not at a chosen arbitrary local lift.

Source/paper coordinate naturality, signed B-augmentation and
the legal completed type-(2) stage are later obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The ACTUAL printed-paper ambient T(Y₁) group value of a
genuinely glued rank-two original-root proper-family coset
vertex. Descent uses only exact (B∩C)-support and is valid
WITHOUT globally retractable T(Y₁). -/
noncomputable def sourceLiteralY1SelectedRootAmbientValue
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (z : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root P)) :
    (sourceLiteralY1 src dst).transitionGroup := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  exact Quotient.liftOn z
    (fun p => L.attachedValue p.1.1 p.2)
    (by
      intro p q hpq
      change L.ShareIntersectionSupport p.1.1 q.1.1 p.2 q.2 at hpq
      exact L.shareIntersectionSupport_value_eq p.1.1 q.1.1 hpq)

/-- Every genuine included component-tagged attached B-coset
point retains exactly its own old ambient T(Y₁) coordinate.
No injectivity of the ambient coordinate projection is claimed. -/
@[simp] theorem sourceLiteralY1SelectedRootAmbientValue_mk
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (b : {B : Finset ι // B ∈ P.alphabets})
    (p : (sourceLiteralY1DirectRootComponent src dst base A root).AttachedCosetVertex b.1) :
    sourceLiteralY1SelectedRootAmbientValue src dst base A hcard root P
      (Quotient.mk (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root P)
        (⟨b, p⟩ :
          (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawVertex P)) =
      (sourceLiteralY1DirectRootComponent src dst base A root).attachedValue b.1 p :=
  rfl

end ABO
end PSTSEPPA
