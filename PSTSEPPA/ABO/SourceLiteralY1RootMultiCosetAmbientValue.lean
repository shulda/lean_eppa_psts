import PSTSEPPA.ABO.SourceLiteralY1RootMultiCosetSetoid
import PSTSEPPA.ABO.RootedSourceMultiCosetAmbientValue

/-!
# Genuine ambient group coordinates of selected paper T(Y₁) glued vertices

A selected corrected Definition-5.3 rank-two original A-root
proper-alphabet coset extension has a REAL quotient of
alphabet-and-path-component-tagged attached coset points by the
EXACT B∩C intersection-support Setoid. The quotient is NOT a
quotient by equality of ambient group coordinates.

Nevertheless every intersection-support gluing identifies two
points with the same ambient group value. We descend the
canonical coordinate projection to the true selected PAPER
T(Y₁) vertex quotient, using only the certified exact Setoid
on its original incomplete root A-component. We also expose
the actual source H₁ rooted quotient coordinate via its
independently proven local H₁[A] normalization.

These coordinates provide the genuine anchor for a later newly
attached full B-coset at an eligible type-(2) root. Neither
value projection is claimed injective or used to identify two
differently tagged old vertices. No global retractability
of either full ambient group is assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The genuine T(Y₁) group coordinate of a PRINTED selected
original rank-two A-root glued multi-coset vertex. Unlike the
quotient type, the group value forgets component/alphabet tags;
this map need not be injective. -/
noncomputable def sourceLiteralY1DirectRootMultiCosetValue
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (z : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root P)) :
    (sourceLiteralY1 src dst).transitionGroup := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  exact Quotient.liftOn z
    (fun p => L.attachedValue p.1.1 p.2)
    (by
      intro p q hpq
      have hrel : L.ShareIntersectionSupport p.1.1 q.1.1 p.2 q.2 :=
        (sourceLiteralY1DirectRootMultiCosetSetoid_exact
          src dst base A hcard root P p q).mp hpq
      exact L.shareIntersectionSupport_value_eq p.1.1 q.1.1 hrel)

/-- The actual quotient-class value is exactly the original
group coordinate of every representative in its tagged copy.
The quotient introduces no new ambient coordinate identifications. -/
@[simp] theorem sourceLiteralY1DirectRootMultiCosetValue_mk
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (p : (sourceLiteralY1DirectRootComponent
      src dst base A root).MultiCosetRawVertex P) :
    sourceLiteralY1DirectRootMultiCosetValue
      src dst base A hcard root P
      (Quotient.mk (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root P) p) =
    (sourceLiteralY1DirectRootComponent
      src dst base A root).attachedValue p.1.1 p.2 :=
  rfl

/-- The true SourceH₁-side selected original A-root quotient
also has its actual group coordinate. This is the previously
certified ROOTED Γ[A] normalization API, not global H₁
retractability or an untagged group-coordinate quotient. -/
noncomputable def sourceH1OriginalRootMultiCosetValue
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (P : CosetFamilySpec A)
    (z : Quotient (sourceH1OriginalRootMultiCosetSetoid
      src dst base A hcard root P)) : SourceH1 src dst :=
  CayleySubgraphSpec.rootedAmbientMultiCosetValue
    ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A)
    A hcard (sourceH1_twoRetractable src dst)
    (⟨root, by trivial⟩ :
      ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).Vertex)
    P z

/-- Likewise the old ORIGINAL source root's selected quotient
representative retains the exact SourceH₁ group coordinate. -/
@[simp] theorem sourceH1OriginalRootMultiCosetValue_mk
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (P : CosetFamilySpec A)
    (p : (sourceH1OriginalRootComponent
      src dst base A root).MultiCosetRawVertex P) :
    sourceH1OriginalRootMultiCosetValue
      src dst base A hcard root P
      (Quotient.mk (sourceH1OriginalRootMultiCosetSetoid
        src dst base A hcard root P) p) =
    (sourceH1OriginalRootComponent
      src dst base A root).attachedValue p.1.1 p.2 :=
  rfl

end ABO
end PSTSEPPA
