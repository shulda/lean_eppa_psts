import PSTSEPPA.ABO.LabelledGroupSingleCosetGraphIso
import PSTSEPPA.ABO.IsolatedCosetGluing
import PSTSEPPA.ABO.BijectiveGraphPathReflection

/-!
# Entire signed full-B-coset transport under labelled GROUP ISOMORPHISMS

Corrected ABO Definition 5.3 attaches a fresh FULL B-left coset to
a genuinely incomplete old signed stage. The actual paper's first
transition group T(Y₁) is isomorphic, label by label, to the
independent SourceH₁ model. The two groups need not be globally
retractable. This module handles the FULL NEW coset uniformly.

A true generator-preserving group isomorphism E: Γ ≃* Δ carries
g Γ[B] bijectively onto E(g) Δ[B], and carries EVERY signed
oriented B-edge token (x, ±i) with its original sign to
(E(x), ±i). We prove the group map on all full-coset points
and signed edges is bijective and is a genuine labelled EGraph
isomorphism preserving source, formal edge reversal and labels.

This is an independent prerequisite for original paper↔SourceH₁
type-(2) isolated-root augmentation gluing; it is NOT an assertion
that the augmentation is legal at an arbitrary old vertex or that
the selected Z₁ stage family is complete.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable (genΓ : ι → Γ) (genΔ : ι → Δ)
variable (E : Γ ≃* Δ)
variable (hgen : ∀ i : ι, E (genΓ i) = genΔ i)

/-- The actual COMPLETE B-left coset point bijection, including the
coset anchor. No representative of an intrinsic component is chosen. -/
noncomputable def labelledMulEquivFullCosetPointEquiv
    (B : Finset ι) (g : Γ) :
    IsolatedCosetGluing.CosetPoint genΓ B g ≃
      IsolatedCosetGluing.CosetPoint genΔ B (E g) where
  toFun p :=
    ⟨E p.1, (labelledMulEquiv_mem_generatedLeftCoset_iff
      genΓ genΔ E hgen B g p.1).mpr p.2⟩
  invFun p :=
    ⟨E.symm p.1, by
      apply (labelledMulEquiv_mem_generatedLeftCoset_iff
        genΓ genΔ E hgen B g (E.symm p.1)).mp
      simpa only [E.apply_symm_apply] using p.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact E.symm_apply_apply p.1
  right_inv := by
    intro p
    apply Subtype.ext
    exact E.apply_symm_apply p.1

/-- The original signed oriented edge token is transported by
E on its source coordinate and by the identity on its SIGNED label.
Both directions reflect genuine full B-coset membership. -/
noncomputable def labelledMulEquivFullCosetEdgeEquiv
    (B : Finset ι) (g : Γ) :
    IsolatedCosetGluing.CosetEdge genΓ B g ≃
      IsolatedCosetGluing.CosetEdge genΔ B (E g) where
  toFun p :=
    ⟨(E p.1.1, p.1.2), by
      refine ⟨?_, p.2.2⟩
      apply (labelledMulEquiv_mem_generatedLeftCoset_iff
        genΓ genΔ E hgen B g p.1.1).mpr
      exact p.2.1⟩
  invFun p :=
    ⟨(E.symm p.1.1, p.1.2), by
      refine ⟨?_, p.2.2⟩
      apply (labelledMulEquiv_mem_generatedLeftCoset_iff
        genΓ genΔ E hgen B g (E.symm p.1.1)).mp
      simpa only [E.apply_symm_apply] using p.2.1⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · exact E.symm_apply_apply p.1.1
    · rfl
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · exact E.apply_symm_apply p.1.1
    · rfl

/-- A TRUE signed full B-coset graph isomorphism, preserving
OLD group generator labels in both signed orientations and all
formal reverse directed tokens, even for Cayley loops. -/
noncomputable def labelledMulEquivFullCosetSignedGraphHom
    (B : Finset ι) (g : Γ) :
    LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph genΓ B g).toEGraph).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph genΔ B (E g)).toEGraph).toLabelledGraph where
  onVertex := labelledMulEquivFullCosetPointEquiv genΓ genΔ E hgen B g
  onEdge := labelledMulEquivFullCosetEdgeEquiv genΓ genΔ E hgen B g
  map_source := by
    intro e
    apply Subtype.ext
    rfl
  map_label := by
    intro e
    rfl
  map_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · change E ((cayleyGraph genΓ).target e.1) =
        (cayleyGraph genΔ).target (E e.1.1, e.1.2)
      rw [cayleyGraph.target_eq_mul_evalGroupLetter,
        cayleyGraph.target_eq_mul_evalGroupLetter]
      calc
        E (e.1.1 * PSTS.SignedWord.evalGroupLetter genΓ e.1.2) =
            E e.1.1 * E (PSTS.SignedWord.evalGroupLetter genΓ e.1.2) :=
          E.map_mul _ _
        _ = E e.1.1 * PSTS.SignedWord.evalGroupLetter genΔ e.1.2 :=
          congrArg (fun z => E e.1.1 * z)
            (labelledMulEquiv_evalGroupLetter genΓ genΔ E hgen e.1.2)
    · rfl

/-- The full B-coset signed graph comparison is bijective on
all actual coset POINTS and formal signed oriented edge TOKENS. -/
theorem labelledMulEquivFullCosetSignedGraphHom_bijective
    (B : Finset ι) (g : Γ) :
    Function.Bijective
      (labelledMulEquivFullCosetSignedGraphHom
        genΓ genΔ E hgen B g).onVertex ∧
    Function.Bijective
      (labelledMulEquivFullCosetSignedGraphHom
        genΓ genΔ E hgen B g).onEdge :=
  ⟨(labelledMulEquivFullCosetPointEquiv
      genΓ genΔ E hgen B g).bijective,
    (labelledMulEquivFullCosetEdgeEquiv
      genΓ genΔ E hgen B g).bijective⟩

/-- All actually realised chronological signed paths inside the
complete newly attached B-coset are preserved AND REFLECTED. -/
theorem labelledMulEquivFullCosetSignedGraphHom_follows_iff
    (B : Finset ι) (g : Γ)
    (u v : IsolatedCosetGluing.CosetPoint genΓ B g)
    (w : LabelWord ι) :
    ((IsolatedCosetGluing.fullCosetSubgraph genΓ B g).toEGraph).Follows u w v ↔
    ((IsolatedCosetGluing.fullCosetSubgraph genΔ B (E g)).toEGraph).Follows
      ((labelledMulEquivFullCosetSignedGraphHom
        genΓ genΔ E hgen B g).onVertex u) w
      ((labelledMulEquivFullCosetSignedGraphHom
        genΓ genΔ E hgen B g).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (labelledMulEquivFullCosetSignedGraphHom genΓ genΔ E hgen B g)
    (labelledMulEquivFullCosetSignedGraphHom_bijective
      genΓ genΔ E hgen B g).1
    (labelledMulEquivFullCosetSignedGraphHom_bijective
      genΓ genΔ E hgen B g).2 u v w

end ABO
end PSTSEPPA
