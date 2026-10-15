import PSTSEPPA.ABO.SourceLiteralY1TaggedCosetAttachments
import PSTSEPPA.ABO.MultiCosetVertexQuotient

/-!
# The literal paper T(Y₁) original cover preserves exact ABO coset gluing

The separately certified original-cover signed graph isomorphism and
labelled group isomorphism induce a component-tagged B-coset equivalence for
EVERY B, commuting with the actual B ⊆ C enlargement maps.

Here we prove that this bijection PRESERVES AND REFLECTS the literal
common-(B ∩ C)-support relation underlying corrected ABO (3.10). In
particular, distinct original signed-path component tags cannot be merged
merely because their ambient group coordinates agree.

We also obtain a genuine bijection of alphabet-tagged raw multi-coset
vertices for EVERY proper-alphabet family P and prove iff of the exact
raw gluing relation. This is the quotient-compatibility prerequisite;
it is not yet an isomorphism of the completed quotient EGraphs or of
the selected Definition-5.3 root A-component stages.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- For every B and C, common support from an ACTUAL original signed
(B ∩ C)-path-component is invariant under the literal-paper/source H₁
cover transport. This is stronger than equality of ambient values. -/
theorem sourceLiteralY1Direct_shareIntersectionSupport_iff
    (src dst : ι → V) (base : V)
    (B C : Finset ι)
    (p : (sourceLiteralY1DirectOriginalSkeleton src dst base).AttachedCosetVertex B)
    (q : (sourceLiteralY1DirectOriginalSkeleton src dst base).AttachedCosetVertex C) :
    (sourceLiteralY1DirectOriginalSkeleton src dst base).ShareIntersectionSupport B C p q ↔
    (sourceH1OriginalSkeleton src dst base).ShareIntersectionSupport B C
      (sourceLiteralY1DirectTaggedBCosetEquiv src dst base B p)
      (sourceLiteralY1DirectTaggedBCosetEquiv src dst base C q) := by
  let L := sourceLiteralY1DirectOriginalSkeleton src dst base
  let K := sourceH1OriginalSkeleton src dst base
  constructor
  · rintro ⟨r, hrp, hrq⟩
    refine ⟨sourceLiteralY1DirectTaggedBCosetEquiv src dst base (B ∩ C) r, ?_, ?_⟩
    · calc
        K.attachedSubalphabetMap (B ∩ C) B Finset.inter_subset_left
            (sourceLiteralY1DirectTaggedBCosetEquiv src dst base (B ∩ C) r) =
          sourceLiteralY1DirectTaggedBCosetEquiv src dst base B
            (L.attachedSubalphabetMap (B ∩ C) B Finset.inter_subset_left r) :=
          (sourceLiteralY1DirectTaggedBCosetEquiv_natural
            src dst base (B ∩ C) B Finset.inter_subset_left r).symm
        _ = sourceLiteralY1DirectTaggedBCosetEquiv src dst base B p :=
          congrArg _ hrp
    · calc
        K.attachedSubalphabetMap (B ∩ C) C Finset.inter_subset_right
            (sourceLiteralY1DirectTaggedBCosetEquiv src dst base (B ∩ C) r) =
          sourceLiteralY1DirectTaggedBCosetEquiv src dst base C
            (L.attachedSubalphabetMap (B ∩ C) C Finset.inter_subset_right r) :=
          (sourceLiteralY1DirectTaggedBCosetEquiv_natural
            src dst base (B ∩ C) C Finset.inter_subset_right r).symm
        _ = sourceLiteralY1DirectTaggedBCosetEquiv src dst base C q :=
          congrArg _ hrq
  · rintro ⟨r, hrp, hrq⟩
    let R := sourceLiteralY1DirectTaggedBCosetEquiv src dst base (B ∩ C)
    let s : L.AttachedCosetVertex (B ∩ C) := R.symm r
    have hs : sourceLiteralY1DirectTaggedBCosetEquiv src dst base (B ∩ C) s = r :=
      R.apply_symm_apply r
    refine ⟨s, ?_, ?_⟩
    · apply (sourceLiteralY1DirectTaggedBCosetEquiv src dst base B).injective
      calc
        sourceLiteralY1DirectTaggedBCosetEquiv src dst base B
            (L.attachedSubalphabetMap (B ∩ C) B Finset.inter_subset_left s) =
          K.attachedSubalphabetMap (B ∩ C) B Finset.inter_subset_left
            (sourceLiteralY1DirectTaggedBCosetEquiv src dst base (B ∩ C) s) :=
          sourceLiteralY1DirectTaggedBCosetEquiv_natural
            src dst base (B ∩ C) B Finset.inter_subset_left s
        _ = K.attachedSubalphabetMap (B ∩ C) B Finset.inter_subset_left r := by
          rw [hs]
        _ = sourceLiteralY1DirectTaggedBCosetEquiv src dst base B p := hrp
    · apply (sourceLiteralY1DirectTaggedBCosetEquiv src dst base C).injective
      calc
        sourceLiteralY1DirectTaggedBCosetEquiv src dst base C
            (L.attachedSubalphabetMap (B ∩ C) C Finset.inter_subset_right s) =
          K.attachedSubalphabetMap (B ∩ C) C Finset.inter_subset_right
            (sourceLiteralY1DirectTaggedBCosetEquiv src dst base (B ∩ C) s) :=
          sourceLiteralY1DirectTaggedBCosetEquiv_natural
            src dst base (B ∩ C) C Finset.inter_subset_right s
        _ = K.attachedSubalphabetMap (B ∩ C) C Finset.inter_subset_right r := by
          rw [hs]
        _ = sourceLiteralY1DirectTaggedBCosetEquiv src dst base C q := hrq

/-- Transport every raw component-and-alphabet-tagged coset point of the
ACTUAL paper T(Y₁) original cover to the corresponding SourceH₁ point.
The family P may include the empty alphabet and its members may be nested. -/
noncomputable def sourceLiteralY1DirectMultiCosetRawVertexEquiv
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι)) :
    (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P ≃
    (sourceH1OriginalSkeleton src dst base).MultiCosetRawVertex P where
  toFun p :=
    ⟨p.1, sourceLiteralY1DirectTaggedBCosetEquiv src dst base p.1.1 p.2⟩
  invFun p :=
    ⟨p.1, (sourceLiteralY1DirectTaggedBCosetEquiv src dst base p.1.1).symm p.2⟩
  left_inv := by
    rintro ⟨b, p⟩
    let e := sourceLiteralY1DirectTaggedBCosetEquiv src dst base b.1
    change
      (⟨b, e.symm (e p)⟩ :
        (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P) =
      ⟨b, p⟩
    rw [e.symm_apply_apply]
  right_inv := by
    rintro ⟨b, p⟩
    let e := sourceLiteralY1DirectTaggedBCosetEquiv src dst base b.1
    change
      (⟨b, e (e.symm p)⟩ :
        (sourceH1OriginalSkeleton src dst base).MultiCosetRawVertex P) =
      ⟨b, p⟩
    rw [e.apply_symm_apply]

/-- Exact iff of the unquotiented ABO (3.10) gluing relation on
the literal-paper and SourceH₁ original preimage graphs. The
proof uses the common tagged intersection witness in BOTH directions. -/
theorem sourceLiteralY1DirectMultiCosetRawRelated_iff
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (p q : (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P) :
    (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q ↔
    (sourceH1OriginalSkeleton src dst base).MultiCosetRawRelated P
      (sourceLiteralY1DirectMultiCosetRawVertexEquiv src dst base P p)
      (sourceLiteralY1DirectMultiCosetRawVertexEquiv src dst base P q) := by
  rcases p with ⟨b, p⟩
  rcases q with ⟨c, q⟩
  change
    (sourceLiteralY1DirectOriginalSkeleton src dst base).ShareIntersectionSupport
      b.1 c.1 p q ↔
    (sourceH1OriginalSkeleton src dst base).ShareIntersectionSupport
      b.1 c.1
      (sourceLiteralY1DirectTaggedBCosetEquiv src dst base b.1 p)
      (sourceLiteralY1DirectTaggedBCosetEquiv src dst base c.1 q)
  exact sourceLiteralY1Direct_shareIntersectionSupport_iff
    src dst base b.1 c.1 p q

end ABO
end PSTSEPPA
