import PSTSEPPA.ABO.SourceLiteralY1RootCosetGluingTransport
import PSTSEPPA.ABO.InverseTaggedCosetNaturality
import PSTSEPPA.ABO.RootedSourceMultiCosetVertexQuotient

/-!
# Real selected Definition-5.3 paper T(Y₁) A-root coset gluing SETOIDS

The original printed rank-one source indices select TRUE
A-connected components of the incomplete original-input T(Y₁)
Cayley preimage, for |A|=2. The source-H₁ presentation was
proved independently to be 2-retractable, but neither whole
H₁ presentation is assumed globally retractable.

For each actual source-H₁ selected original A-root component,
the previously certified root-local Γ[A] normalization gives
the precise corrected ABO (3.10) intersection-support Setoid,
WITHOUT global retractability of ambient SourceH₁.

The genuine printed-to-source root old signed graph isomorphism
and natural component-tagged full B-coset equivalences give
natural INVERSES as well. Transport the exact source Setoid
BACK to the actual printed T(Y₁) selected root A-component.
Consequently the literal corrected ABO common-(B∩C)-support
predicate is an equivalence relation in each genuine selected
paper A-component, for EVERY proper alphabet family P (including
empty B). We also construct the bijection of actual glued
quotient VERTICES, not group-coordinate quotients.

Still open: transport the actual oriented signed raw edges and
target congruence to obtain a complete selected EGraph, then
legal trivial completion and B-augmentations, full printed Z₁
coverage and the higher-rank Section 4/5 induction and PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- A genuine *source-H₁* original-input rooted A-component has
an actual exact corrected ABO intersection-supported Setoid for
|A|=2, transported from its rank-two Γ[A] local representative. -/
noncomputable def sourceH1OriginalRootMultiCosetSetoid
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst) (P : CosetFamilySpec A) :
    Setoid ((sourceH1OriginalRootComponent src dst base A root).MultiCosetRawVertex P) :=
  CayleySubgraphSpec.rootedAmbientMultiCosetSetoid
    ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A)
    A hcard
      (sourceH1_twoRetractable src dst)
      (⟨root, by trivial⟩ :
        ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).Vertex) P

/-- In the true original source rank-two root, relation equality
means EXACTLY a common component-tagged (B∩C)-support, including
B=C and B∩C=∅; never just equal H₁ group coordinates. -/
theorem sourceH1OriginalRootMultiCosetSetoid_exact
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst) (P : CosetFamilySpec A)
    (p q : (sourceH1OriginalRootComponent src dst base A root).MultiCosetRawVertex P) :
    (sourceH1OriginalRootMultiCosetSetoid src dst base A hcard root P).r p q ↔
      (sourceH1OriginalRootComponent src dst base A root).MultiCosetRawRelated P p q :=
  Iff.rfl

/-- The LITERAL printed T(Y₁) old-input root A-component has its
own exact corrected ABO (3.10) gluing Setoid for EVERY family P
of proper A-subalphabets. The proof uses the source Γ[A] rank-two
normalization, via the INVERSE of the true component-tagged
old-cover isomorphism, not a fictitious global retractability
assertion for T(Y₁). -/
noncomputable def sourceLiteralY1DirectRootMultiCosetSetoid
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    Setoid ((sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawVertex P) := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  let rootK := (sourceH1EquivLiteralY1Transition src dst).symm root
  let K := sourceH1OriginalRootComponent src dst base A rootK
  let e := sourceLiteralY1DirectRootTaggedFamily src dst base A root
  let eInv := L.inverseTaggedCosetEquivFamily K e
  let hNat := sourceLiteralY1DirectRootTaggedFamily_natural src dst base A root
  let hInvNat := L.inverseTaggedCosetEquivFamily_natural K e hNat
  let sK := sourceH1OriginalRootMultiCosetSetoid src dst base A hcard rootK P
  exact K.transportedMultiCosetSetoid L P eInv hInvNat sK
    (sourceH1OriginalRootMultiCosetSetoid_exact src dst base A hcard rootK P)

/-- This is precisely the paper's original intersection-support
relation, not its transitive closure or ambient coset equality.
The existence of the equivalence relation is now unconditional
for each ACTUAL selected |A|=2 old input component. -/
theorem sourceLiteralY1DirectRootMultiCosetSetoid_exact
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (p q : (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawVertex P) :
    (sourceLiteralY1DirectRootMultiCosetSetoid src dst base A hcard root P).r p q ↔
      (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawRelated P p q :=
  Iff.rfl

/-- Genuine exact glued coset VERTEX equivalence for the chosen
paper and source original input-rooted A-components, for every
proper-alphabet family P, including degenerate empty alphabets. -/
noncomputable def sourceH1RootToLiteralY1MultiCosetVertexEquiv
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    Quotient (sourceH1OriginalRootMultiCosetSetoid src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root) P) ≃
    Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root P) := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  let rootK := (sourceH1EquivLiteralY1Transition src dst).symm root
  let K := sourceH1OriginalRootComponent src dst base A rootK
  let e := sourceLiteralY1DirectRootTaggedFamily src dst base A root
  let eInv := L.inverseTaggedCosetEquivFamily K e
  let hNat := sourceLiteralY1DirectRootTaggedFamily_natural src dst base A root
  let hInvNat := L.inverseTaggedCosetEquivFamily_natural K e hNat
  let sK := sourceH1OriginalRootMultiCosetSetoid src dst base A hcard rootK P
  exact K.multiCosetQuotientEquivOfNatural L P eInv hInvNat sK
    (sourceH1OriginalRootMultiCosetSetoid_exact src dst base A hcard rootK P)

/-- The paper→source direction of the exact selected rank-two
old-component glued quotient comparison, retaining all path tags. -/
noncomputable def sourceLiteralY1RootToH1MultiCosetVertexEquiv
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root P) ≃
    Quotient (sourceH1OriginalRootMultiCosetSetoid src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root) P) :=
  (sourceH1RootToLiteralY1MultiCosetVertexEquiv src dst base A hcard root P).symm

end ABO
end PSTSEPPA
