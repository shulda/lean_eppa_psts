import PSTSEPPA.ABO.LabelledMulEquivFullCosetSignedGraphIso

/-!
# Exact fresh-coset and glued-root transport under labelled group equivalences

For the corrected ABO isolated-root B-augmentation, the old root
is IDENTIFIED with the attached full B-coset anchor, while all
other coset points remain genuinely fresh. This is not the same
as identifying group coordinates of unrelated old tagged vertices.

A generator-preserving true group equivalence E : Γ ≃* Δ
transports the full B-coset and its anchor exactly. We verify
the fresh-point equivalence, extend any bijection f of old
vertices across the disjoint old/fresh sum, and prove exact
naturality of the literal gluePoint map. In particular, old
root points stay old and every non-root point stays fresh.

This is vertex-level compatibility needed for the subsequent
real old+new signed augmentation EGraph isomorphism; this
module makes no statement about an old root satisfying the
required absence of signed B-edges.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ V W : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable (genΓ : ι → Γ) (genΔ : ι → Δ)
variable (E : Γ ≃* Δ)
variable (hgen : ∀ i : ι, E (genΓ i) = genΔ i)

/-- Non-anchor points of the NEW full B-coset match bijectively.
No old vertex, even if it shares an ambient group value, is
silently identified with a different tagged new vertex. -/
noncomputable def labelledMulEquivFreshCosetPointEquiv
    (B : Finset ι) (g : Γ) :
    IsolatedCosetGluing.FreshPoint genΓ B g ≃
      IsolatedCosetGluing.FreshPoint genΔ B (E g) where
  toFun p :=
    ⟨E p.1,
      ⟨(labelledMulEquiv_mem_generatedLeftCoset_iff
        genΓ genΔ E hgen B g p.1).mpr p.2.1,
        fun h => p.2.2 (E.injective h)⟩⟩
  invFun p :=
    ⟨E.symm p.1,
      ⟨by
        apply (labelledMulEquiv_mem_generatedLeftCoset_iff
          genΓ genΔ E hgen B g (E.symm p.1)).mp
        simpa only [E.apply_symm_apply] using p.2.1,
       by
        intro h
        apply p.2.2
        have hE := congrArg E h
        simpa only [E.apply_symm_apply] using hE⟩⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact E.symm_apply_apply p.1
  right_inv := by
    intro p
    apply Subtype.ext
    exact E.apply_symm_apply p.1

/-- An arbitrary genuine equivalence on OLD labelled vertices
extends over separately tagged FRESH non-anchor B-coset points. -/
noncomputable def labelledMulEquivAugmentedVertexEquiv
    (f : V ≃ W) (B : Finset ι) (g : Γ) :
    IsolatedCosetGluing.Vertex V genΓ B g ≃
      IsolatedCosetGluing.Vertex W genΔ B (E g) :=
  Equiv.sumCongr f
    (labelledMulEquivFreshCosetPointEquiv genΓ genΔ E hgen B g)

/-- The full B-coset anchor is carried exactly to the new anchor,
and no distinct non-anchor point is treated as the anchor. -/
@[simp] theorem labelledMulEquivFullCosetPointEquiv_value
    (B : Finset ι) (g : Γ)
    (p : IsolatedCosetGluing.CosetPoint genΓ B g) :
    (labelledMulEquivFullCosetPointEquiv
      genΓ genΔ E hgen B g p).1 = E p.1 :=
  rfl

/-- NATURALITY OF THE ACTUAL OLD/NEW GLUING POINT:
the old root maps by f, the entire coset maps by E,
and the unique attached anchor remains the unique old root.

This holds for every full-coset point, not only fresh points,
with no global retractability hypothesis on either group. -/
theorem labelledMulEquiv_gluePoint_natural
    (f : V ≃ W) (B : Finset ι) (g : Γ)
    (oldRoot : V)
    (p : IsolatedCosetGluing.CosetPoint genΓ B g) :
    labelledMulEquivAugmentedVertexEquiv
        genΓ genΔ E hgen f B g
      (IsolatedCosetGluing.gluePoint genΓ B g oldRoot p) =
    IsolatedCosetGluing.gluePoint genΔ B (E g)
      (f oldRoot)
      (labelledMulEquivFullCosetPointEquiv
        genΓ genΔ E hgen B g p) := by
  classical
  by_cases hp : p.1 = g
  · have htarget :
        (labelledMulEquivFullCosetPointEquiv
          genΓ genΔ E hgen B g p).1 = E g := by
      rw [labelledMulEquivFullCosetPointEquiv_value, hp]
    simp [IsolatedCosetGluing.gluePoint, hp, htarget,
      labelledMulEquivAugmentedVertexEquiv]
  · have htarget :
        (labelledMulEquivFullCosetPointEquiv
          genΓ genΔ E hgen B g p).1 ≠ E g := by
      rw [labelledMulEquivFullCosetPointEquiv_value]
      intro h
      exact hp (E.injective h)
    simp only [IsolatedCosetGluing.gluePoint,
      dif_neg hp, dif_neg htarget]
    change Sum.inr
        (labelledMulEquivFreshCosetPointEquiv
          genΓ genΔ E hgen B g ⟨p.1, p.2, hp⟩) =
      Sum.inr
        (⟨(labelledMulEquivFullCosetPointEquiv
            genΓ genΔ E hgen B g p).1,
          (labelledMulEquivFullCosetPointEquiv
            genΓ genΔ E hgen B g p).2, htarget⟩ :
          IsolatedCosetGluing.FreshPoint genΔ B (E g))
    apply congrArg Sum.inr
    apply Subtype.ext
    rfl

end ABO
end PSTSEPPA
