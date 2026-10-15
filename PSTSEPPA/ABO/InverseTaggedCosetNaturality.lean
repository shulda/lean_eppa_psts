import PSTSEPPA.ABO.MultiCosetGluingIsoTransport

/-!
# Inverse naturality of exact component-tagged coset transport

When equivalences of genuine intrinsic B-path-component-tagged
attached coset copies commute with every alphabet enlargement,
their inverse equivalences also commute with every enlargement.

This is essential when the checked REAL rank-two original H₁
root-component gluing setoid is transported BACKWARDS to the
corresponding literal paper T(Y₁) rooted component: the source
group's rank-two local retractability supplies the setoid, not
an unproved globally retractable paper group assumption.

The result covers B=∅ and all nested/equal alphabets; it never
identifies vertices by ambient group coordinates.
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

/-- The inverses of all exact component-tagged coset equivalences,
retaining the full dependent intrinsic path-component index. -/
noncomputable def inverseTaggedCosetEquivFamily
    (e : L.TaggedCosetEquivFamily K) :
    K.TaggedCosetEquivFamily L :=
  fun B => (e B).symm

/-- Exact naturality for the inverse family at EVERY B⊆C.
The proof uses bijectivity of the *tagged* fibre equivalences,
not ambient left coset coordinate equality. -/
theorem inverseTaggedCosetEquivFamily_natural
    (e : L.TaggedCosetEquivFamily K)
    (hnat : e.Natural) :
    (L.inverseTaggedCosetEquivFamily K e).Natural := by
  intro B C hBC p
  apply (e C).injective
  calc
    e C ((e C).symm (K.attachedSubalphabetMap B C hBC p)) =
        K.attachedSubalphabetMap B C hBC p := (e C).apply_symm_apply _
    _ = K.attachedSubalphabetMap B C hBC (e B ((e B).symm p)) := by
          rw [(e B).apply_symm_apply]
    _ = e C (L.attachedSubalphabetMap B C hBC ((e B).symm p)) :=
          (hnat B C hBC ((e B).symm p)).symm

end CayleySubgraphSpec
end ABO
end PSTSEPPA
