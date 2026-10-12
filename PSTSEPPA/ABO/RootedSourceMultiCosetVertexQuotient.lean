import PSTSEPPA.ABO.RootedCosetGluingRelationNaturality
import PSTSEPPA.ABO.ExactQuotientEquivTransport
import PSTSEPPA.ABO.MultiCosetVertexQuotient

/-!
# Actual SOURCE H1-component coset-extension vertex quotient from local H1[A]

The source H1 group constructed in the corrected first-rank tower is
only 2-retractable. It would be INVALID to apply the pre-existing
multiCosetSetoid theorem to H1 itself, because that theorem demands
GLOBAL retractability. Moreover the actual coset extension retains
intrinsic D-component tags: equality of ambient group coordinates
cannot be substituted for the gluing relation.

For any genuine incomplete Γ-Cayley skeleton K, parent alphabet A
of CARDINALITY TWO, genuine rooted A-connected component M, and
2-retractable ambient generator family, translate the old component
to its true local Γ[A]-Cayley skeleton L. The local trivially
completed generator family is GLOBALLY retractable, so the actual
proper-coset multi-extension quotient of L exists.

We use the source/local component-tagged coset equivalences (#367)
and reflection of exact (B∩C)-intersection gluing support (#368) to
construct a bijection of the entire DISJOINT UNION of tagged raw
attached-coset points for any family P of proper subalphabets.
That bijection preserves/refects the LITERAL ABO raw-gluing
relation. Hence the gluing relation on the ORIGINAL rooted ambient
component M is itself a certified Setoid, WITHOUT global
retractability of Γ. By exact quotient transport (#370), the
local proper-coset quotient and this source quotient of M are
genuinely EQUIVALENT.

This is a precise source-facing VERTEX quotient theorem. The
directed signed-edge quotient/EGraph morphism, whole completion,
augmented B-coset stages and source Condition 5.2 remain open,
as do later rank history and PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The exact raw (alphabet tag, component tag, coset point)
bijection from a genuinely rooted local Γ[A] coset extension
to the original rooted Γ-Cayley component's coset extension.
The outer alphabet index is retained literally. -/
noncomputable def rootedLocalMultiCosetRawVertexEquiv
    (A : Finset ι) (root : K.Vertex) (P : CosetFamilySpec A) :
    (K.intrinsicComponentLocalSlice A root).MultiCosetRawVertex P ≃
      (K.subalphabetComponentSubgraph A root).MultiCosetRawVertex P where
  toFun p :=
    ⟨p.1,
      K.rootedLocalAttachedCosetMap A p.1.1
        (P.proper p.1.1 p.1.2).subset root p.2⟩
  invFun p :=
    ⟨p.1,
      (K.rootedLocalAttachedCosetEquiv A p.1.1
        (P.proper p.1.1 p.1.2).subset root).symm p.2⟩
  left_inv := by
    rintro ⟨b, p⟩
    let e := K.rootedLocalAttachedCosetEquiv A b.1
      (P.proper b.1 b.2).subset root
    change
      (⟨b, e.symm (e p)⟩ :
        (K.intrinsicComponentLocalSlice A root).MultiCosetRawVertex P) =
      ⟨b, p⟩
    rw [e.symm_apply_apply]
  right_inv := by
    rintro ⟨b, p⟩
    let e := K.rootedLocalAttachedCosetEquiv A b.1
      (P.proper b.1 b.2).subset root
    change
      (⟨b, e (e.symm p)⟩ :
        (K.subalphabetComponentSubgraph A root).MultiCosetRawVertex P) =
      ⟨b, p⟩
    rw [e.apply_symm_apply]

/-- The raw point map preserves and REFLECTS the genuine ABO
intersection-supported coset gluing relation, not ambient
coordinate equality. Includes B=∅ and C=∅. -/
theorem rootedLocalMultiCosetRawRelated_iff
    (A : Finset ι) (root : K.Vertex) (P : CosetFamilySpec A)
    (p q :
      (K.intrinsicComponentLocalSlice A root).MultiCosetRawVertex P) :
    (K.intrinsicComponentLocalSlice A root).MultiCosetRawRelated P p q ↔
      (K.subalphabetComponentSubgraph A root).MultiCosetRawRelated P
        (K.rootedLocalMultiCosetRawVertexEquiv A root P p)
        (K.rootedLocalMultiCosetRawVertexEquiv A root P q) := by
  rcases p with ⟨b, p⟩
  rcases q with ⟨c, q⟩
  change
    (K.intrinsicComponentLocalSlice A root).ShareIntersectionSupport
        b.1 c.1 p q ↔
      (K.subalphabetComponentSubgraph A root).ShareIntersectionSupport
        b.1 c.1
        (K.rootedLocalAttachedCosetMap A b.1
          (P.proper b.1 b.2).subset root p)
        (K.rootedLocalAttachedCosetMap A c.1
          (P.proper c.1 c.2).subset root q)
  exact K.rootedLocal_shareIntersectionSupport_iff
    A b.1 c.1 (P.proper b.1 b.2).subset
    (P.proper c.1 c.2).subset root p q

/-- The literal gluing relation on the TRUE ambient root
component is an equivalence relation, certified by translation
from its local Γ[A] representative. This DOES NOT require
globally retractable ambient Γ. The relation is precisely
the source MultiCosetRawRelated, not a coarser closure. -/
noncomputable def rootedAmbientMultiCosetSetoid
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
    (P : CosetFamilySpec A) :
    Setoid ((K.subalphabetComponentSubgraph A root).MultiCosetRawVertex P) :=
  setoidOfEquivRelation
    (K.rootedLocalMultiCosetRawVertexEquiv A root P)
    ((K.intrinsicComponentLocalSlice A root).multiCosetSetoid P
      ((K.intrinsicComponentLocalSlice A root).
        admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    ((K.subalphabetComponentSubgraph A root).MultiCosetRawRelated P)
    (K.rootedLocalMultiCosetRawRelated_iff A root P)

/-- The actual local multi-coset quotient and the source
ambient-root-component quotient are EQUIVALENT ON ALL VERTICES.
Both are quotiented by their exact intersection-support relation.
The target ambient Γ itself need not be globally retractable. -/
noncomputable def rootedLocalMultiCosetVertexQuotientEquiv
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
    (P : CosetFamilySpec A) :
    (K.intrinsicComponentLocalSlice A root).MultiCosetVertex P
      ((K.intrinsicComponentLocalSlice A root).
        admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le) ≃
    Quotient (K.rootedAmbientMultiCosetSetoid A hcard hret root P) :=
  quotientEquivOfEquivRelation
    (K.rootedLocalMultiCosetRawVertexEquiv A root P)
    ((K.intrinsicComponentLocalSlice A root).multiCosetSetoid P
      ((K.intrinsicComponentLocalSlice A root).
        admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    ((K.subalphabetComponentSubgraph A root).MultiCosetRawRelated P)
    (K.rootedLocalMultiCosetRawRelated_iff A root P)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
