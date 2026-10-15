import PSTSEPPA.ABO.SourceLiteralY1OriginalCoverComponentEquiv
import PSTSEPPA.ABO.LabelledIsoTaggedCosetTransport

/-!
# Genuine tagged B-coset equivalence for printed T(Y₁) and source H₁ old covers

The previous source bridge identifies the ACTUAL literal-paper
T(Y₁)-Cayley original-edge preimage EGraph with the SourceH₁ preimage
OVER the same original signed incomplete input graph. Separately,
the generator-preserving group isomorphism SourceH₁ ≃* T(Y₁)
identifies all generated B-subgroups and left B-cosets.

Combining these certified data with the generic tagged-coset theorem,
we build, for every original input basepoint and EVERY subalphabet B,
an actual equivalence of attached coset point types. The B-component
index (quotient by realised B-paths) is retained; no identification
is made from equal ambient group coordinates alone.

This settles the attached-coset point-level identification for
the WHOLE printed original preimage, before restricting to each
connected A-component and constructing its full proper-family
multi-coset gluing quotient and B-augmentation.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The coordinate part of the real direct-paper-to-source
original signed graph isomorphism is LITERALLY the inverse
labelled H₁ group isomorphism on every group vertex. -/
theorem sourceLiteralY1DirectToSourceH1_coordinate
    (src dst : ι → V) (base : V)
    (x : (sourceLiteralY1DirectOriginalSkeleton
      src dst base).Vertex) :
    (sourceH1EquivLiteralY1Transition src dst).symm x.1 =
      ((sourceLiteralY1DirectToSourceH1OriginalHom
        src dst base).onVertex x).1 := by
  rfl

/-- The paper's literal T(Y₁) positive generator is mapped
exactly to its original SourceH₁ generator by the inverse
isomorphism, including all loops and coincident labels. -/
theorem sourceLiteralY1Generator_to_sourceH1
    (src dst : ι → V) (i : ι) :
    (sourceH1EquivLiteralY1Transition src dst).symm
      ((sourceLiteralY1 src dst).transitionSubgroupGenerator i) =
    sourceH1Generator src dst i := by
  exact (sourceLiteralY1ToSourceH1Quotient src dst).map_gen i

/-- A genuine equivalence on BOTH coordinates of each
component-tagged full B-coset attachment: intrinsic old-edge
B-path component and point in its full generated LEFT B-coset.
It applies for every B including ∅ and all input letters. -/
noncomputable def sourceLiteralY1DirectTaggedBCosetEquiv
    (src dst : ι → V) (base : V) (B : Finset ι) :
    (sourceLiteralY1DirectOriginalSkeleton src dst base).AttachedCosetVertex B ≃
      (sourceH1OriginalSkeleton src dst base).AttachedCosetVertex B := by
  let L := sourceLiteralY1DirectOriginalSkeleton src dst base
  let K := sourceH1OriginalSkeleton src dst base
  let f := sourceLiteralY1DirectToSourceH1OriginalHom src dst base
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  let hb := sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base
  exact L.attachedCosetEquivOfLabelledGroupIso K f hb.1 hb.2 E
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    (sourceLiteralY1DirectToSourceH1_coordinate src dst base) B

/-- The transported tagged coset point has EXACTLY the image
of its original T(Y₁) group coordinate, without changing or
erasing the B-component quotient tag. -/
theorem sourceLiteralY1DirectTaggedBCosetEquiv_value
    (src dst : ι → V) (base : V) (B : Finset ι)
    (p : (sourceLiteralY1DirectOriginalSkeleton src dst base).AttachedCosetVertex B) :
    (sourceH1OriginalSkeleton src dst base).attachedValue B
      (sourceLiteralY1DirectTaggedBCosetEquiv src dst base B p) =
      (sourceH1EquivLiteralY1Transition src dst).symm
        ((sourceLiteralY1DirectOriginalSkeleton src dst base).attachedValue B p) := by
  exact (sourceLiteralY1DirectOriginalSkeleton src dst base).attachedCosetEquivOfLabelledGroupIso_value
      (sourceH1OriginalSkeleton src dst base)
      (sourceLiteralY1DirectToSourceH1OriginalHom src dst base)
      (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).1
      (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).2
      (sourceH1EquivLiteralY1Transition src dst).symm
      (sourceLiteralY1Generator_to_sourceH1 src dst)
      (sourceLiteralY1DirectToSourceH1_coordinate src dst base) B p

/-- The equivalence maps a literal old input skeleton vertex
to the attached point of its image in the SourceH₁ old graph.
Thus original B-component tags match even when two ambient
coset coordinates accidentally coincide. -/
theorem sourceLiteralY1DirectTaggedBCosetEquiv_old
    (src dst : ι → V) (base : V) (B : Finset ι)
    (x : (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex) :
    sourceLiteralY1DirectTaggedBCosetEquiv src dst base B
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).attachedOfSkeletonVertex B x) =
      (sourceH1OriginalSkeleton src dst base).attachedOfSkeletonVertex B
        ((sourceLiteralY1DirectToSourceH1OriginalHom src dst base).onVertex x) := by
  exact (sourceLiteralY1DirectOriginalSkeleton src dst base).attachedCosetEquivOfLabelledGroupIso_oldVertex
      (sourceH1OriginalSkeleton src dst base)
      (sourceLiteralY1DirectToSourceH1OriginalHom src dst base)
      (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).1
      (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).2
      (sourceH1EquivLiteralY1Transition src dst).symm
      (sourceLiteralY1Generator_to_sourceH1 src dst)
      (sourceLiteralY1DirectToSourceH1_coordinate src dst base) B x

/-- The literal original-cover tag comparison commutes with
every B ⊆ C enlargement, including B=C and B=∅. It is a
prerequisite for preserving the actual B∩C gluing witnesses
of the future printed multi-coset vertex quotient. -/
theorem sourceLiteralY1DirectTaggedBCosetEquiv_natural
    (src dst : ι → V) (base : V)
    (B C : Finset ι) (hBC : B ⊆ C)
    (p : (sourceLiteralY1DirectOriginalSkeleton src dst base).AttachedCosetVertex B) :
    sourceLiteralY1DirectTaggedBCosetEquiv src dst base C
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).attachedSubalphabetMap B C hBC p) =
      (sourceH1OriginalSkeleton src dst base).attachedSubalphabetMap B C hBC
        (sourceLiteralY1DirectTaggedBCosetEquiv src dst base B p) := by
  exact (sourceLiteralY1DirectOriginalSkeleton src dst base).attachedCosetEquivOfLabelledGroupIso_natural
      (sourceH1OriginalSkeleton src dst base)
      (sourceLiteralY1DirectToSourceH1OriginalHom src dst base)
      (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).1
      (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).2
      (sourceH1EquivLiteralY1Transition src dst).symm
      (sourceLiteralY1Generator_to_sourceH1 src dst)
      (sourceLiteralY1DirectToSourceH1_coordinate src dst base)
      B C hBC p

end ABO
end PSTSEPPA
