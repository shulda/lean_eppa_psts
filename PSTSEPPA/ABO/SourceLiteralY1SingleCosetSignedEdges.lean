import PSTSEPPA.ABO.LabelledGroupSingleCosetGraphIso
import PSTSEPPA.ABO.SourceLiteralY1TaggedCosetAttachments
import PSTSEPPA.ABO.SourceLiteralY1MultiCosetRawGluingTransport
import PSTSEPPA.ABO.MultiCosetRawEdges

/-!
# Literal paper T(Y₁) original preimage: genuine single-B signed edges

The first-rank source-group comparison is an honest group isomorphism,
and its direct original-old-edge preimage comparison is a true signed
graph isomorphism, over the SAME original incomplete input EGraph.

We now apply the generic labelled-group coset-extension theorem to
all B, including B=∅. This supplies an ACTUAL original-cover
single-B coset EGraph isomorphism, including old outside-B edges,
newly completed inside-B edges, formal signed inverse tokens and
whole signed path reflection.

We also lift these bijections to every proper-alphabet-tagged
disjoint union of raw oriented edges. The raw edges are still
SEPARATE according to their alphabet summand; the subsequent
source-and-label quotient and complete multi-coset graph are
deliberately not asserted in this module.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Real signed EGraph isomorphism (vertex and oriented edge
bijection) between the full original T(Y₁) single-B coset
extension and the corresponding SourceH₁ single-B extension.
Neither graph is replaced with an artificial X₁ Cayley completion. -/
noncomputable def sourceLiteralY1DirectSingleCosetGraphHom
    (src dst : ι → V) (base : V) (B : Finset ι) :
    LabelledGraphHom
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).singleCosetEGraph B).toLabelledGraph
      ((sourceH1OriginalSkeleton src dst base).singleCosetEGraph B).toLabelledGraph :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).labelledGroupIsoSingleCosetGraphHom
    (sourceH1OriginalSkeleton src dst base)
    (sourceLiteralY1DirectToSourceH1OriginalHom src dst base)
    (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).1
    (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).2
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    (sourceLiteralY1DirectToSourceH1_coordinate src dst base) B

/-- The full signed old+new single-B coset graph map is bijective
on the actual vertex type AND formal oriented signed edge tokens. -/
theorem sourceLiteralY1DirectSingleCosetGraphHom_bijective
    (src dst : ι → V) (base : V) (B : Finset ι) :
    Function.Bijective
      (sourceLiteralY1DirectSingleCosetGraphHom src dst base B).onVertex ∧
    Function.Bijective
      (sourceLiteralY1DirectSingleCosetGraphHom src dst base B).onEdge := by
  exact
    (sourceLiteralY1DirectOriginalSkeleton src dst base).labelledGroupIsoSingleCosetGraphHom_bijective
      (sourceH1OriginalSkeleton src dst base)
      (sourceLiteralY1DirectToSourceH1OriginalHom src dst base)
      (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).1
      (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).2
      (sourceH1EquivLiteralY1Transition src dst).symm
      (sourceLiteralY1Generator_to_sourceH1 src dst)
      (sourceLiteralY1DirectToSourceH1_coordinate src dst base) B

/-- Every truly realised single-B completed signed path in the
printed T(Y₁) original cover is realised precisely when its
transported path exists in SourceH₁. This includes B empty,
inverse signs, loops and disconnected original input graphs. -/
theorem sourceLiteralY1DirectSingleCosetGraphHom_follows_iff
    (src dst : ι → V) (base : V) (B : Finset ι)
    (u v : (sourceLiteralY1DirectOriginalSkeleton
      src dst base).AttachedCosetVertex B)
    (w : LabelWord ι) :
    ((sourceLiteralY1DirectOriginalSkeleton src dst base).singleCosetEGraph B).Follows
        u w v ↔
    ((sourceH1OriginalSkeleton src dst base).singleCosetEGraph B).Follows
        ((sourceLiteralY1DirectSingleCosetGraphHom src dst base B).onVertex u)
        w
        ((sourceLiteralY1DirectSingleCosetGraphHom src dst base B).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (sourceLiteralY1DirectSingleCosetGraphHom src dst base B)
    (sourceLiteralY1DirectSingleCosetGraphHom_bijective src dst base B).1
    (sourceLiteralY1DirectSingleCosetGraphHom_bijective src dst base B).2
    u v w

/-- The actual original-cover signed edge-token equivalence for
one selected B, containing BOTH old and fresh edges, not merely
an equivalence of ambient Cayley edge coordinates. -/
noncomputable def sourceLiteralY1DirectSingleCosetEdgeEquiv
    (src dst : ι → V) (base : V) (B : Finset ι) :
    (sourceLiteralY1DirectOriginalSkeleton src dst base).SingleCosetEdge B ≃
      (sourceH1OriginalSkeleton src dst base).SingleCosetEdge B :=
  Equiv.ofBijective
    (sourceLiteralY1DirectSingleCosetGraphHom src dst base B).onEdge
    (sourceLiteralY1DirectSingleCosetGraphHom_bijective src dst base B).2

/-- Canonical bijection of EVERY ALPHABET-AND-COMPONENT-TAGGED raw
oriented edge summand for the literal source original preimage.
All P may include ∅; no edge quotient is taken here. -/
noncomputable def sourceLiteralY1DirectMultiCosetRawEdgeEquiv
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι)) :
    (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawEdge P ≃
      (sourceH1OriginalSkeleton src dst base).MultiCosetRawEdge P where
  toFun := fun e =>
    ⟨e.1, sourceLiteralY1DirectSingleCosetEdgeEquiv src dst base e.1.1 e.2⟩
  invFun := fun e =>
    ⟨e.1, (sourceLiteralY1DirectSingleCosetEdgeEquiv src dst base e.1.1).symm e.2⟩
  left_inv := by
    rintro ⟨b, e⟩
    change
      (⟨b, (sourceLiteralY1DirectSingleCosetEdgeEquiv src dst base b.1).symm
          (sourceLiteralY1DirectSingleCosetEdgeEquiv src dst base b.1 e)⟩ :
        (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawEdge P) =
        ⟨b, e⟩
    simp
  right_inv := by
    rintro ⟨b, e⟩
    change
      (⟨b, sourceLiteralY1DirectSingleCosetEdgeEquiv src dst base b.1
          ((sourceLiteralY1DirectSingleCosetEdgeEquiv src dst base b.1).symm e)⟩ :
        (sourceH1OriginalSkeleton src dst base).MultiCosetRawEdge P) =
        ⟨b, e⟩
    simp

/-- Real signed edge transport commutes with oriented token inversion,
including all new B-completed inverse edges, not only original edges. -/
theorem sourceLiteralY1DirectMultiCosetRawEdgeEquiv_inv
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (e : (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawEdge P) :
    sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawEdgeInv P e) =
    (sourceH1OriginalSkeleton src dst base).multiCosetRawEdgeInv P
      (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P e) := by
  rcases e with ⟨b, e⟩
  apply congrArg (fun q => (⟨b, q⟩ :
    (sourceH1OriginalSkeleton src dst base).MultiCosetRawEdge P))
  exact (sourceLiteralY1DirectSingleCosetGraphHom src dst base b.1).map_inv e

/-- The raw edge bijection preserves the exact SIGNED label,
including negative letters even if positive and negative generators
have equal ambient group effect. -/
theorem sourceLiteralY1DirectMultiCosetRawEdgeEquiv_label
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (e : (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawEdge P) :
    (sourceH1OriginalSkeleton src dst base).multiCosetRawEdgeLabel P
        (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P e) =
      (sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawEdgeLabel P e := by
  rcases e with ⟨b, e⟩
  exact (sourceLiteralY1DirectSingleCosetGraphHom src dst base b.1).map_label e

/-- On the raw alphabet-tagged level, SOURCE incidence agrees with
the already verified raw vertex transport. No global retractability
or premature vertex quotient is needed in this equality. -/
theorem sourceLiteralY1DirectMultiCosetRawEdgeEquiv_source
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (e : (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawEdge P) :
    sourceLiteralY1DirectMultiCosetRawVertexEquiv src dst base P
      (⟨e.1,
        ((sourceLiteralY1DirectOriginalSkeleton src dst base).singleCosetEGraph e.1.1).source e.2⟩ :
        (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P) =
      (⟨(sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P e).1,
        ((sourceH1OriginalSkeleton src dst base).singleCosetEGraph e.1.1).source
          (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P e).2⟩ :
        (sourceH1OriginalSkeleton src dst base).MultiCosetRawVertex P) := by
  rcases e with ⟨b, e⟩
  apply congrArg (fun q => (⟨b, q⟩ :
    (sourceH1OriginalSkeleton src dst base).MultiCosetRawVertex P))
  exact ((sourceLiteralY1DirectSingleCosetGraphHom src dst base b.1).map_source e).symm

end ABO
end PSTSEPPA
