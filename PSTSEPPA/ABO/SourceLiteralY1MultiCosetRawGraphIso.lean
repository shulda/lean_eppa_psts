import PSTSEPPA.ABO.SourceLiteralY1SingleCosetSignedEdges
import PSTSEPPA.ABO.MultiCosetGluingIsoTransport
import PSTSEPPA.ABO.RootedMultiCosetRawGraphNaturality

/-!
# True original-cover T(Y₁) / SourceH₁ multi-coset RAW signed graph transport

For each proper-alphabet family P in the entire *original incomplete*
signed T(Y₁) covering and its independent SourceH₁ realization, the
component-tagged B-coset equivalences transport exact (B∩C) support
gluing. The single-B completed graph isomorphisms transport every raw
signed edge token, including original outside-B and fresh inside-B
edges. Here these two ingredients are assembled into one genuine
RAW signed graph isomorphism over exact quotient vertices.

The source vertex setoid is required to be precisely the original
intersection-support relation; its image is therefore the precise
target relation rather than ambient coordinate equality. We do NOT
assume that the whole H₁ group is globally retractable, nor assert
that the entire original-cover relation automatically forms a setoid.
The needed setoid exists for properly selected rank-two root
components via separate certified local retractability arguments.

No edge quotient, source-and-label target congruence, completed
multi-coset EGraph or Definition-5.3 selected Z₁ assertion is made
in this file.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Concrete natural equivalence family on actual B-component-tagged
coset attachments of the two ORIGINAL old-input H₁ coverings. -/
noncomputable def sourceLiteralY1DirectTaggedFamily
    (src dst : ι → V) (base : V) :
    (sourceLiteralY1DirectOriginalSkeleton src dst base).TaggedCosetEquivFamily
      (sourceH1OriginalSkeleton src dst base) :=
  fun B => sourceLiteralY1DirectTaggedBCosetEquiv src dst base B

/-- Naturality in every alphabet inclusion B⊆C, including ∅. -/
theorem sourceLiteralY1DirectTaggedFamily_natural
    (src dst : ι → V) (base : V) :
    (sourceLiteralY1DirectTaggedFamily src dst base).Natural := by
  intro B C hBC p
  exact sourceLiteralY1DirectTaggedBCosetEquiv_natural
    src dst base B C hBC p

/-- The genuine gluing setoid on the paper original-cover side
induces the exact intersection-support setoid on the source H₁
original-cover side, without global H₁ retractability. -/
noncomputable def sourceLiteralY1DirectTransportedMultiCosetSetoid
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton
      src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q) :
    Setoid ((sourceH1OriginalSkeleton src dst base).MultiCosetRawVertex P) :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).transportedMultiCosetSetoid
    (sourceH1OriginalSkeleton src dst base) P
    (sourceLiteralY1DirectTaggedFamily src dst base)
    (sourceLiteralY1DirectTaggedFamily_natural src dst base)
    sL hL

/-- Exact quotient vertex equivalence on original paper/source covering
raw coset gluing, retaining both alphabet and intrinsic path-component
tags. The target setoid is the transported REAL (B∩C) support relation. -/
noncomputable def sourceLiteralY1DirectMultiCosetVertexEquiv
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton
      src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q) :
    Quotient sL ≃ Quotient
      (sourceLiteralY1DirectTransportedMultiCosetSetoid src dst base P sL hL) :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetQuotientEquivOfNatural
    (sourceH1OriginalSkeleton src dst base) P
    (sourceLiteralY1DirectTaggedFamily src dst base)
    (sourceLiteralY1DirectTaggedFamily_natural src dst base)
    sL hL

/-- The TRUE raw signed edge map commutes with SOURCE INCIDENCE after
the exact tagged vertex gluing quotient, not after ambient-coordinate
identification. The only required hypotheses are the original
intersection-supported setoid and its relation characterization. -/
theorem sourceLiteralY1DirectMultiCosetRawGraph_source_natural
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton
      src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q)
    (e : (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawEdge P) :
    ((sourceH1OriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
      P (sourceLiteralY1DirectTransportedMultiCosetSetoid src dst base P sL hL)).source
        (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P e) =
    (sourceLiteralY1DirectMultiCosetVertexEquiv src dst base P sL hL)
      (((sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
        P sL).source e) := by
  let L := sourceLiteralY1DirectOriginalSkeleton src dst base
  let K := sourceH1OriginalSkeleton src dst base
  let eFam := sourceLiteralY1DirectTaggedFamily src dst base
  let hnat := sourceLiteralY1DirectTaggedFamily_natural src dst base
  change Quotient.mk (L.transportedMultiCosetSetoid K P eFam hnat sL hL)
      (⟨(sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P e).1,
        (K.singleCosetEGraph (sourceLiteralY1DirectMultiCosetRawEdgeEquiv
          src dst base P e).1.1).source
            (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P e).2⟩ :
        K.MultiCosetRawVertex P) =
    (L.multiCosetQuotientEquivOfNatural K P eFam hnat sL hL)
      (Quotient.mk sL
        (⟨e.1, (L.singleCosetEGraph e.1.1).source e.2⟩ :
          L.MultiCosetRawVertex P))
  rw [L.multiCosetQuotientEquivOfNatural_mk]
  apply congrArg (Quotient.mk (L.transportedMultiCosetSetoid
    K P eFam hnat sL hL))
  exact (sourceLiteralY1DirectMultiCosetRawEdgeEquiv_source
    src dst base P e).symm

/-- A genuine signed RAW graph morphism between the two original
covering systems, on their exact gluing quotient VERTICES and on
each actual unquotiented oriented signed EDGE token. -/
noncomputable def sourceLiteralY1DirectMultiCosetRawGraphHom
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton
      src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q) :
    LabelledGraphHom
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid P sL)
      ((sourceH1OriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
        P (sourceLiteralY1DirectTransportedMultiCosetSetoid src dst base P sL hL)) where
  onVertex := sourceLiteralY1DirectMultiCosetVertexEquiv src dst base P sL hL
  onEdge := sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P
  map_source := sourceLiteralY1DirectMultiCosetRawGraph_source_natural
    src dst base P sL hL
  map_inv := sourceLiteralY1DirectMultiCosetRawEdgeEquiv_inv src dst base P
  map_label := sourceLiteralY1DirectMultiCosetRawEdgeEquiv_label src dst base P

/-- The source/paper RAW signed graph comparison is bijective on
both already-glued exact vertices and all distinct old/new directed
edge tokens (which have NOT YET been quotient-identified). -/
theorem sourceLiteralY1DirectMultiCosetRawGraphHom_bijective
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton
      src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q) :
    Function.Bijective
      (sourceLiteralY1DirectMultiCosetRawGraphHom src dst base P sL hL).onVertex ∧
    Function.Bijective
      (sourceLiteralY1DirectMultiCosetRawGraphHom src dst base P sL hL).onEdge :=
  ⟨(sourceLiteralY1DirectMultiCosetVertexEquiv src dst base P sL hL).bijective,
    (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P).bijective⟩

end ABO
end PSTSEPPA
