import PSTSEPPA.ABO.SourceLiteralY1MultiCosetRawGraphIso
import PSTSEPPA.ABO.SourceLabelEdgeQuotientGraphIso

/-!
# Exact signed quotient EGraph transport for true paper H₁ old covers

The directly constructed original incomplete T(Y₁) covering and the
synchronized source H₁ covering have a verified genuine signed RAW
multi-coset graph isomorphism (#507). That isomorphism preserves
alphabet+component tagged old/fresh oriented edge tokens; its already
glued vertex carrier is the literal B∩C-intersection-support quotient.

An EGraph, however, requires the *distinct additional* target-
congruence property: two raw oriented edges with the SAME GLUED
source and SAME signed label have the SAME GLUED target. This
property cannot be inferred merely from group-coordinate equality,
and the full H₁ old preimage need not be globally retractable.

Here we formally show that, once an exact intersection-support setoid
and the source target-congruence are actually supplied, the genuine
RAW isomorphism transfers target-congruence to the other side and
induces a full deterministic quotient SIGNED EGraph isomorphism.
We identify the ACTUAL quotient oriented edge classes (source +
signed label), not just raw edges or ambient Cayley coordinates.
All realised signed paths are preserved and REFLECTED.

These are CONDITIONAL geometric transport statements: the existence
of the exact setoid and target-congruence for the selected rank-two
root components must still be established using local H₁[A] geometry.
Neither the full original H₁ group is assumed globally retractable
nor is any Definition-5.3 Z₁ augmentation/EPPA conclusion asserted.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The target H₁ raw graph has source-and-signed-label target
congruence as soon as the corresponding exact original paper
T(Y₁) raw graph has it. In particular, this does NOT assert that
the latter holds without the selected rank-two locality proof. -/
theorem sourceLiteralY1DirectMultiCoset_targetCongruent_transport
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton
      src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton
        src dst base).MultiCosetRawRelated P p q)
    (hG :
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
        P sL).SourceLabelTargetCongruent) :
    ((sourceH1OriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
      P (sourceLiteralY1DirectTransportedMultiCosetSetoid
        src dst base P sL hL)).SourceLabelTargetCongruent := by
  let G := (sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
    P sL
  let H := (sourceH1OriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
    P (sourceLiteralY1DirectTransportedMultiCosetSetoid src dst base P sL hL)
  let F := sourceLiteralY1DirectMultiCosetRawGraphHom src dst base P sL hL
  exact sourceLabelTargetCongruent_transport G H
    (sourceLiteralY1DirectMultiCosetVertexEquiv src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P)
    (fun e => F.map_source e)
    (fun e => F.map_label e)
    (fun e => (F.map_inv e).symm)
    hG

/-- The full deterministic signed quotient EGraphs agree ON ACTUAL
GLUED VERTICES and quotient ORIENTED EDGE TOKENS, provided the exact
original intersection-support setoid and the source target-congruence
have been established. No implicit global retractability assumption. -/
noncomputable def sourceLiteralY1DirectMultiCoset_quotientGraphHom
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton
      src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton
        src dst base).MultiCosetRawRelated P p q)
    (hG :
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
        P sL).SourceLabelTargetCongruent) :
    LabelledGraphHom
      (sourceLabelGraphQuotientEGraph
        ((sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
          P sL) hG).toLabelledGraph
      (sourceLabelGraphQuotientEGraph
        ((sourceH1OriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
          P (sourceLiteralY1DirectTransportedMultiCosetSetoid src dst base P sL hL))
        (sourceLiteralY1DirectMultiCoset_targetCongruent_transport
          src dst base P sL hL hG)).toLabelledGraph := by
  let G := (sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
    P sL
  let H := (sourceH1OriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
    P (sourceLiteralY1DirectTransportedMultiCosetSetoid src dst base P sL hL)
  let F := sourceLiteralY1DirectMultiCosetRawGraphHom src dst base P sL hL
  exact sourceLabelGraphQuotientHom G H
    (sourceLiteralY1DirectMultiCosetVertexEquiv src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P)
    (fun e => F.map_source e)
    (fun e => F.map_label e)
    (fun e => (F.map_inv e).symm)
    hG
    (sourceLiteralY1DirectMultiCoset_targetCongruent_transport
      src dst base P sL hL hG)

/-- An actual bijection of original paper/source glued VERTICES
and precise source+signed-label quotient EDGE CLASSES. -/
theorem sourceLiteralY1DirectMultiCoset_quotientGraphHom_bijective
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton
      src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton
        src dst base).MultiCosetRawRelated P p q)
    (hG :
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
        P sL).SourceLabelTargetCongruent) :
    Function.Bijective
      (sourceLiteralY1DirectMultiCoset_quotientGraphHom
        src dst base P sL hL hG).onVertex ∧
    Function.Bijective
      (sourceLiteralY1DirectMultiCoset_quotientGraphHom
        src dst base P sL hL hG).onEdge := by
  let G := (sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
    P sL
  let H := (sourceH1OriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
    P (sourceLiteralY1DirectTransportedMultiCosetSetoid src dst base P sL hL)
  let F := sourceLiteralY1DirectMultiCosetRawGraphHom src dst base P sL hL
  exact sourceLabelGraphQuotientHom_bijective G H
    (sourceLiteralY1DirectMultiCosetVertexEquiv src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P)
    (fun e => F.map_source e)
    (fun e => F.map_label e)
    (fun e => (F.map_inv e).symm)
    hG
    (sourceLiteralY1DirectMultiCoset_targetCongruent_transport
      src dst base P sL hL hG)

/-- TRUE signed path reflection between the completed
source+signed-label edge quotient EGraphs, still conditional
on the existence of their exact deterministic quotient. -/
theorem sourceLiteralY1DirectMultiCoset_quotientGraphHom_follows_iff
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton
      src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton
        src dst base).MultiCosetRawRelated P p q)
    (hG :
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
        P sL).SourceLabelTargetCongruent)
    (u v : Quotient sL) (w : LabelWord ι) :
    (sourceLabelGraphQuotientEGraph
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
        P sL) hG).Follows u w v ↔
    (sourceLabelGraphQuotientEGraph
      ((sourceH1OriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
        P (sourceLiteralY1DirectTransportedMultiCosetSetoid src dst base P sL hL))
      (sourceLiteralY1DirectMultiCoset_targetCongruent_transport
        src dst base P sL hL hG)).Follows
      ((sourceLiteralY1DirectMultiCoset_quotientGraphHom
        src dst base P sL hL hG).onVertex u)
      w
      ((sourceLiteralY1DirectMultiCoset_quotientGraphHom
        src dst base P sL hL hG).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (sourceLiteralY1DirectMultiCoset_quotientGraphHom
      src dst base P sL hL hG)
    (sourceLiteralY1DirectMultiCoset_quotientGraphHom_bijective
      src dst base P sL hL hG).1
    (sourceLiteralY1DirectMultiCoset_quotientGraphHom_bijective
      src dst base P sL hL hG).2 u v w

end ABO
end PSTSEPPA
