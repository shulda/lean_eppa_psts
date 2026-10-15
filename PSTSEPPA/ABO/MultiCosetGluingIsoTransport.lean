import PSTSEPPA.ABO.LabelledIsoTaggedCosetTransport
import PSTSEPPA.ABO.ExactQuotientEquivTransport

/-!
# Genuine intersection-support gluing transport

A coset extension is glued along common points in the *intersection*
alphabet.  Two attached points with the same ambient group coordinate
are not necessarily related: they may carry distinct intrinsic
B-component tags.

We prove that a family of bijections between the actual component-tagged
B-cosets, natural under EVERY alphabet inclusion, preserves and reflects
the literal ABO (3.10) intersection-support relation.  Consequently
it induces an equivalence of the complete raw disjoint unions and, when
the source relation is an equivalence, of the EXACT quotient vertex
sets.  Importantly, the target's gluing relation is certified from the
source: we do not assume global retractability of its ambient group.

No signed edge equivalence, legal completion or augmented Z-stage
isomorphism is asserted by this vertex-level transport.
-/

namespace PSTSEPPA
namespace ABO
namespace CayleySubgraphSpec

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}
variable (L : CayleySubgraphSpec genΓ A)
variable (K : CayleySubgraphSpec genΔ A)

/-- Transport data for every alphabet, INCLUDING the empty alphabet:
an equivalence of actual component-tagged attached cosets. -/
abbrev TaggedCosetEquivFamily :=
  ∀ B : Finset ι, L.AttachedCosetVertex B ≃ K.AttachedCosetVertex B

/-- Natural transport data: all maps B→C commute with the
attached-coset equivalences, rather than merely with their ambient
group-coordinate projections. -/
def TaggedCosetEquivFamily.Natural
    (e : L.TaggedCosetEquivFamily K) : Prop :=
  ∀ (B C : Finset ι) (hBC : B ⊆ C)
    (p : L.AttachedCosetVertex B),
    e C (L.attachedSubalphabetMap B C hBC p) =
      K.attachedSubalphabetMap B C hBC (e B p)

/-- Equivalences natural for all subalphabet inclusions preserve
AND REFLECT the actual common-(B∩C)-support witness in ABO (3.10).

The backward implication uses the inverse of the equivalence at
B∩C, not an arbitrary ambient group element or representative of a
component-index quotient. -/
theorem shareIntersectionSupport_iff_of_naturalEquivs
    (e : L.TaggedCosetEquivFamily K)
    (hnat : e.Natural)
    (B C : Finset ι)
    (p : L.AttachedCosetVertex B)
    (q : L.AttachedCosetVertex C) :
    L.ShareIntersectionSupport B C p q ↔
      K.ShareIntersectionSupport B C (e B p) (e C q) := by
  constructor
  · rintro ⟨r, hrp, hrq⟩
    refine ⟨e (B ∩ C) r, ?_, ?_⟩
    · calc
        K.attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left (e (B ∩ C) r) =
          e B (L.attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left r) :=
              (hnat (B ∩ C) B Finset.inter_subset_left r).symm
        _ = e B p := congrArg (e B) hrp
    · calc
        K.attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right (e (B ∩ C) r) =
          e C (L.attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right r) :=
              (hnat (B ∩ C) C Finset.inter_subset_right r).symm
        _ = e C q := congrArg (e C) hrq
  · rintro ⟨r, hrp, hrq⟩
    refine ⟨(e (B ∩ C)).symm r, ?_, ?_⟩
    · apply (e B).injective
      calc
        e B (L.attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left ((e (B ∩ C)).symm r)) =
          K.attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left
              (e (B ∩ C) ((e (B ∩ C)).symm r)) :=
                hnat (B ∩ C) B Finset.inter_subset_left _
        _ = K.attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left r := by simp
        _ = e B p := hrp
    · apply (e C).injective
      calc
        e C (L.attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right ((e (B ∩ C)).symm r)) =
          K.attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right
              (e (B ∩ C) ((e (B ∩ C)).symm r)) :=
                hnat (B ∩ C) C Finset.inter_subset_right _
        _ = K.attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right r := by simp
        _ = e C q := hrq

/-- A bijection on the ENTIRE disjoint union, preserving its alphabet
tag and mapping both coordinates of each attached-coset point. -/
noncomputable def multiCosetRawEquivOfNatural
    (P : CosetFamilySpec A)
    (e : L.TaggedCosetEquivFamily K) :
    L.MultiCosetRawVertex P ≃ K.MultiCosetRawVertex P where
  toFun := fun p => ⟨p.1, e p.1.1 p.2⟩
  invFun := fun p => ⟨p.1, (e p.1.1).symm p.2⟩
  left_inv := by
    rintro ⟨B, p⟩
    change (⟨B, (e B.1).symm (e B.1 p)⟩ :
      L.MultiCosetRawVertex P) = ⟨B, p⟩
    simp
  right_inv := by
    rintro ⟨B, p⟩
    change (⟨B, e B.1 ((e B.1).symm p)⟩ :
      K.MultiCosetRawVertex P) = ⟨B, p⟩
    simp

/-- Exact preservation and reflection of the RAW vertex gluing
relation. Component tags are never replaced by ambient coordinates. -/
theorem multiCosetRawRelated_iff_ofNatural
    (P : CosetFamilySpec A)
    (e : L.TaggedCosetEquivFamily K)
    (hnat : e.Natural)
    (p q : L.MultiCosetRawVertex P) :
    L.MultiCosetRawRelated P p q ↔
      K.MultiCosetRawRelated P
        (L.multiCosetRawEquivOfNatural K P e p)
        (L.multiCosetRawEquivOfNatural K P e q) := by
  rcases p with ⟨B, p⟩
  rcases q with ⟨C, q⟩
  change L.ShareIntersectionSupport B.1 C.1 p q ↔
    K.ShareIntersectionSupport B.1 C.1 (e B.1 p) (e C.1 q)
  exact L.shareIntersectionSupport_iff_of_naturalEquivs
    K e hnat B.1 C.1 p q

/-- Whenever the source's TRUE (B∩C)-gluing relation is a setoid,
the literal target relation is itself a setoid.  This intentionally
requires NO global retractability assumption on the target group. -/
noncomputable def transportedMultiCosetSetoid
    (P : CosetFamilySpec A)
    (e : L.TaggedCosetEquivFamily K)
    (hnat : e.Natural)
    (sL : Setoid (L.MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔ L.MultiCosetRawRelated P p q) :
    Setoid (K.MultiCosetRawVertex P) :=
  setoidOfEquivRelation (L.multiCosetRawEquivOfNatural K P e)
    sL (K.MultiCosetRawRelated P)
    (by
      intro p q
      exact (hL p q).trans
        (L.multiCosetRawRelated_iff_ofNatural K P e hnat p q))

/-- Exact quotient-vertex equivalence for ABO (3.10).
The target is quotiented by ITS REAL intersection-support relation,
not by coordinate equality or by a new transitive closure. -/
noncomputable def multiCosetQuotientEquivOfNatural
    (P : CosetFamilySpec A)
    (e : L.TaggedCosetEquivFamily K)
    (hnat : e.Natural)
    (sL : Setoid (L.MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔ L.MultiCosetRawRelated P p q) :
    Quotient sL ≃
      Quotient (L.transportedMultiCosetSetoid K P e hnat sL hL) :=
  quotientEquivOfEquivRelation
    (L.multiCosetRawEquivOfNatural K P e) sL
    (K.MultiCosetRawRelated P)
    (by
      intro p q
      exact (hL p q).trans
        (L.multiCosetRawRelated_iff_ofNatural K P e hnat p q))

/-- On each raw point, the induced quotient equivalence is literally
the class of its transported, STILL COMPONENT-TAGGED point. -/
theorem multiCosetQuotientEquivOfNatural_mk
    (P : CosetFamilySpec A)
    (e : L.TaggedCosetEquivFamily K)
    (hnat : e.Natural)
    (sL : Setoid (L.MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔ L.MultiCosetRawRelated P p q)
    (p : L.MultiCosetRawVertex P) :
    L.multiCosetQuotientEquivOfNatural K P e hnat sL hL
      (Quotient.mk sL p) =
      Quotient.mk (L.transportedMultiCosetSetoid K P e hnat sL hL)
        (L.multiCosetRawEquivOfNatural K P e p) := rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
