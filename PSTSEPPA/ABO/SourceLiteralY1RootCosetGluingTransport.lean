import PSTSEPPA.ABO.SourceLiteralY1RootComponentGraphIso
import PSTSEPPA.ABO.MultiCosetGluingIsoTransport

/-!
# Exact component-tagged coset gluing for literal paper ROOTED A-components

The true incomplete original signed rooted A-component of the paper's
T(Y₁) is isomorphic as an oriented signed graph to the corresponding
source-H₁ rooted A-component. Their group coordinates are intertwined
by the independently certified generator-preserving isomorphism.

Consequently, for every B (in particular all proper B⊊A), the full
dependent attached B-coset types agree: both the intrinsic OLD
B-component index and its full generated left B-coset coordinate
are transported together. The equivalences are natural in B⊆C.

The original ABO (3.10) gluing predicate for every pair of
component-tagged attached points is therefore reflected and
preserved, including B∩C empty, nested or equal subalphabets.
The complete raw alphabet-labelled coset disjoint union is
likewise identified, and its EXACT intersection-support raw
gluing relation agrees in both directions.

No global retractability of either ambient H₁ presentation is
assumed, and this file DOES NOT yet assert a setoid on a selected
root A-component or a full quotient EGraph. That requires the
already formalized rank-two source H₁[A] local normalization.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Exact equivalence of the component-tagged B-coset attachments
to the TRUE rooted old A-components, not to whole H₁[A] cosets.
This includes B=∅ and all B ⊆ A. -/
noncomputable def sourceLiteralY1DirectRootTaggedBCosetEquiv
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι) :
    (sourceLiteralY1DirectRootComponent src dst base A root).AttachedCosetVertex B ≃
      (sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).AttachedCosetVertex B := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  let K := sourceH1OriginalRootComponent src dst base A
    ((sourceH1EquivLiteralY1Transition src dst).symm root)
  let f := sourceLiteralY1DirectRootComponentGraphHom src dst base A root
  let hbij := sourceLiteralY1DirectRootComponentGraphHom_bijective src dst base A root
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  have hcoord : ∀ x : L.Vertex, E x.1 = (f.onVertex x).1 := by
    intro x
    rfl
  exact L.attachedCosetEquivOfLabelledGroupIso
    K f hbij.1 hbij.2 E
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    hcoord B

/-- The full rooted old-component attached-coset transport commutes
with every enlargement B⊆C, including empty alphabets and equality.
No ambient coset equality can identify distinct B-component tags. -/
theorem sourceLiteralY1DirectRootTaggedBCosetEquiv_natural
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (B C : Finset ι) (hBC : B ⊆ C)
    (p : (sourceLiteralY1DirectRootComponent src dst base A root).AttachedCosetVertex B) :
    sourceLiteralY1DirectRootTaggedBCosetEquiv src dst base A root C
      ((sourceLiteralY1DirectRootComponent src dst base A root).attachedSubalphabetMap
        B C hBC p) =
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).attachedSubalphabetMap
        B C hBC
      (sourceLiteralY1DirectRootTaggedBCosetEquiv src dst base A root B p) := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  let K := sourceH1OriginalRootComponent src dst base A
    ((sourceH1EquivLiteralY1Transition src dst).symm root)
  let f := sourceLiteralY1DirectRootComponentGraphHom src dst base A root
  let hbij := sourceLiteralY1DirectRootComponentGraphHom_bijective src dst base A root
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  have hcoord : ∀ x : L.Vertex, E x.1 = (f.onVertex x).1 := by
    intro x
    rfl
  exact L.attachedCosetEquivOfLabelledGroupIso_natural
    K f hbij.1 hbij.2 E
    (sourceLiteralY1Generator_to_sourceH1 src dst) hcoord B C hBC p

/-- The rank-two selected-root analogue of the whole-cover tagged
equivalence FAMILY, natural for every B⊆C. -/
noncomputable def sourceLiteralY1DirectRootTaggedFamily
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1DirectRootComponent src dst base A root).TaggedCosetEquivFamily
      (sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)) :=
  fun B => sourceLiteralY1DirectRootTaggedBCosetEquiv src dst base A root B

/-- Compatibility of the ACTUAL rooted A-component coset family
with the entire inclusion diagram of all subalphabets. -/
theorem sourceLiteralY1DirectRootTaggedFamily_natural
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1DirectRootTaggedFamily src dst base A root).Natural := by
  intro B C hBC p
  exact sourceLiteralY1DirectRootTaggedBCosetEquiv_natural
    src dst base A root B C hBC p

/-- Exact preservation/reflection of ABO (3.10) gluing of the
ACTUAL printed T(Y₁) and source H₁ selected rooted components.
The shared point lies in its genuine (B∩C)-tagged copy. -/
theorem sourceLiteralY1DirectRoot_shareIntersectionSupport_iff
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (B C : Finset ι)
    (p : (sourceLiteralY1DirectRootComponent src dst base A root).AttachedCosetVertex B)
    (q : (sourceLiteralY1DirectRootComponent src dst base A root).AttachedCosetVertex C) :
    (sourceLiteralY1DirectRootComponent src dst base A root).ShareIntersectionSupport B C p q ↔
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).ShareIntersectionSupport B C
      (sourceLiteralY1DirectRootTaggedBCosetEquiv src dst base A root B p)
      (sourceLiteralY1DirectRootTaggedBCosetEquiv src dst base A root C q) := by
  exact (sourceLiteralY1DirectRootComponent src dst base A root).shareIntersectionSupport_iff_of_naturalEquivs
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root))
    (sourceLiteralY1DirectRootTaggedFamily src dst base A root)
    (sourceLiteralY1DirectRootTaggedFamily_natural src dst base A root)
    B C p q

/-- Genuine entire tagged raw coset-vertex bijection, preserving
the proper-alphabet family labels in the TRUE rooted A-components. -/
noncomputable def sourceLiteralY1DirectRootMultiCosetRawVertexEquiv
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawVertex P ≃
      (sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).MultiCosetRawVertex P :=
  (sourceLiteralY1DirectRootComponent src dst base A root).multiCosetRawEquivOfNatural
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root))
    P (sourceLiteralY1DirectRootTaggedFamily src dst base A root)

/-- The literal labelled union gluing relation is identical after
transport, without assuming global T(Y₁)/H₁ retractability. -/
theorem sourceLiteralY1DirectRootMultiCosetRawRelated_iff
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (p q : (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawVertex P) :
    (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawRelated P p q ↔
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).MultiCosetRawRelated P
      (sourceLiteralY1DirectRootMultiCosetRawVertexEquiv src dst base A root P p)
      (sourceLiteralY1DirectRootMultiCosetRawVertexEquiv src dst base A root P q) := by
  exact (sourceLiteralY1DirectRootComponent src dst base A root).multiCosetRawRelated_iff_ofNatural
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root))
    P (sourceLiteralY1DirectRootTaggedFamily src dst base A root)
    (sourceLiteralY1DirectRootTaggedFamily_natural src dst base A root) p q

end ABO
end PSTSEPPA
