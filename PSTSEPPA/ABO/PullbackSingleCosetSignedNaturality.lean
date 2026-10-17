import PSTSEPPA.ABO.PullbackMultiCosetTaggedVertexNaturality
import PSTSEPPA.ABO.SingleCosetEGraph
import PSTSEPPA.ABO.LabelledQuotientSkeletonPullback
import PSTSEPPA.ABO.KStablePullbackAdmissibility

/-!
# Full signed naturality for an individual genuine tagged B-coset extension

Given ANY real original INCOMPLETE H-Cayley A-skeleton K and a
generator-preserving labelled Q:G↠H, we already have the true
signed old-edge pullback L=Q^-1(K), its genuine signed old
L→K morphism and component-tagged attached B-coset map.

We extend these to a genuine LABELLED GRAPH MORPHISM
  CE(G,L;B) → CE(H,K;B)
on EVERY directed formally signed edge token, not just
vertices and underlying group values.

The two edge classes are preserved separately:
  * actual OLD signed edges whose labels lie OUTSIDE B,
    transported by the exact Q old signed graph covering;
  * newly completed full B-coset signed edges, transported
    together with their TRUE intrinsic B-component tag.

Preservation of source, both orientations of formal edge
reversal and full signed labels is checked, with no use
of ambient coordinate equality across different B-tags,
no global injectivity, and no insertion of missing original
old edges. The crucial coset step naturality follows
from actual Q.map_mul and Q.map_evalGroupLetter.

This is the needed oriented signed constituent ingredient
for a true full G-multiCE→H-multiCE EGraph morphism,
whose OLD H vertex images the type-(2) detector of
corrected ABO 4.7(iii) needs.

No whole-pullback connectedness, bridge freeness,
R8, higher rank, Condition 5.2 or PSTS EPPA is claimed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- The REAL group quotient preserves every signed B-edge
step WITH ITS ORIGINAL B-COMPONENT TAG, including inverses,
trivial generators and genuine geometric old signed loops. -/
theorem pullbackQuotient_attachedCosetToBase_step
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B)
    (s : {s : SignedLabel ι // signedBase s ∈ B}) :
    K.pullbackQuotient_attachedCosetToBase Q B
      ((K.pullbackQuotient Q).cosetStep B p s) =
      K.cosetStep B
        (K.pullbackQuotient_attachedCosetToBase Q B p) s := by
  apply K.attachedValue_injective_of_same_index B
  · rfl
  · change Q.hom
        (p.2.1 * PSTS.SignedWord.evalGroupLetter genΓ s.1) =
      Q.hom p.2.1 * PSTS.SignedWord.evalGroupLetter genΔ s.1
    rw [map_mul, Q.map_evalGroupLetter]

/-- Actual OLD outside-B signed edge token transport under Q.
The source and FULL signed label remain unchanged; the edge
itself is a real edge of the original incomplete H graph. -/
noncomputable def pullbackQuotient_outsideEdgeToBase
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (e : (K.pullbackQuotient Q).OutsideEdge B) :
    K.OutsideEdge B :=
  ⟨(K.pullbackQuotientHom Q).onEdge e.1, by
    change signedBase e.1.1.2 ∉ B at e
    exact e.2⟩

/-- The entire signed single-B EGraph map, including ALL actual
original-old outside-B signed edge tokens and all fresh full
tagged B edges. Both edge classes keep their own tags.
This construction does not require B-stability. -/
noncomputable def pullbackQuotient_singleCosetHom
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) :
    LabelledGraphHom
      ((K.pullbackQuotient Q).singleCosetEGraph B).toLabelledGraph
      (K.singleCosetEGraph B).toLabelledGraph where
  onVertex := K.pullbackQuotient_attachedCosetToBase Q B
  onEdge
    | .inl e => .inl (K.pullbackQuotient_outsideEdgeToBase Q B e)
    | .inr e =>
        .inr (K.pullbackQuotient_attachedCosetToBase Q B e.1, e.2)
  map_source := by
    intro e
    cases e with
    | inl e =>
        change K.pullbackQuotient_attachedCosetToBase Q B
            ( (K.pullbackQuotient Q).attachedOfSkeletonVertex B
                ((K.pullbackQuotient Q).toEGraph.source e.1)) =
          K.attachedOfSkeletonVertex B
            (K.toEGraph.source ((K.pullbackQuotientHom Q).onEdge e.1))
        rw [K.pullbackQuotient_attachedCosetToBase_skeleton]
        exact congrArg (K.attachedOfSkeletonVertex B)
          ((K.pullbackQuotientHom Q).map_source e.1).symm
    | inr e =>
        rfl
  map_inv := by
    intro e
    cases e with
    | inl e =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact (K.pullbackQuotientHom Q).map_inv e.1
    | inr e =>
        apply congrArg Sum.inr
        apply Prod.ext
        · exact K.pullbackQuotient_attachedCosetToBase_step Q B e.1 e.2
        · rfl
  map_label := by
    intro e
    cases e <;> rfl

/-- Exact formula for the mapping of each old, truly PRESENT,
formally oriented outside-B signed edge token. No missing
old edge is manufactured. -/
@[simp] theorem pullbackQuotient_singleCosetHom_oldEdge
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (e : (K.pullbackQuotient Q).OutsideEdge B) :
    (K.pullbackQuotient_singleCosetHom Q B).onEdge (.inl e) =
      .inl (K.pullbackQuotient_outsideEdgeToBase Q B e) :=
  rfl

/-- Exact formula for each genuinely completed full B-edge
including the old-component tag, its signed direction
and the actual preimage coset point. -/
@[simp] theorem pullbackQuotient_singleCosetHom_freshEdge
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B)
    (s : {s : SignedLabel ι // signedBase s ∈ B}) :
    (K.pullbackQuotient_singleCosetHom Q B).onEdge
        (.inr (p,s)) =
      .inr (K.pullbackQuotient_attachedCosetToBase Q B p,s) :=
  rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
