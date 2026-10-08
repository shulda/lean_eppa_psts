import PSTSEPPA.ABO.SingleCosetEGraph

/-!
# Complete B-coset connectivity in single-alphabet ABO extensions

Every component-tagged B-coset of CE(G,K;B) is connected by actual
B-labelled paths, not merely equal in the ambient group.

We construct each path letter by letter from the fully attached B-edges
and prove that the endpoint equals right multiplication by the original
word value.  For any two vertices in one component-tagged coset, their
relative group value lies in G[B], hence a B-word connects them inside
the extension.  This is the positive direction of the B-component
classification needed in the coset-extension construction. The converse,
that every B-path preserves the component tag, is a separate lemma in
SingleCosetComponentInvariant; this file does not assume it.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Two points in one component's ambient B-coset differ by a B-group
element.  No choice of representative of the quotient component is needed. -/
theorem componentAmbientCoset_relative_mem
    (B : Finset ι) (c : K.ComponentIndex B)
    {x y : Γ}
    (hx : x ∈ K.componentAmbientCoset B c)
    (hy : y ∈ K.componentAmbientCoset B c) :
    x⁻¹ * y ∈ generatedSubgroup gen B := by
  induction c using Quotient.inductionOn with
  | _ v =>
      change v.1⁻¹ * x ∈ generatedSubgroup gen B at hx
      change v.1⁻¹ * y ∈ generatedSubgroup gen B at hy
      have hmul :=
        (generatedSubgroup gen B).mul_mem
          ((generatedSubgroup gen B).inv_mem hx) hy
      simpa [mul_assoc] using hmul

/-- A B-supported word can be followed from every tagged B-coset
vertex; the path never leaves its component tag, and its group value
is exactly the right action of the original word. -/
theorem singleCosetEGraph_follows_word
    (B : Finset ι) (p : K.AttachedCosetVertex B)
    {w : LabelWord ι} (hw : LabelWord.Uses B w) :
    ∃ q : K.AttachedCosetVertex B,
      (K.singleCosetEGraph B).Follows p w q ∧
      q.1 = p.1 ∧
      q.2.1 = p.2.1 * PSTS.SignedWord.evalGroup gen w := by
  induction w generalizing p with
  | nil =>
      refine ⟨p, EGraph.Follows.nil _, rfl, ?_⟩
      simp
  | cons s w ih =>
      let t : {s : SignedLabel ι // signedBase s ∈ B} :=
        ⟨s, hw.1⟩
      let p' := K.cosetStep B p t
      obtain ⟨q, hpath, hidx, hval⟩ := ih p' hw.2
      refine ⟨q, ?_, ?_, ?_⟩
      · exact EGraph.Follows.cons (Sum.inr (p, t)) rfl rfl hpath
      · exact hidx.trans (K.cosetStep_index B p t)
      · calc
          q.2.1 = p'.2.1 * PSTS.SignedWord.evalGroup gen w := hval
          _ = (p.2.1 * PSTS.SignedWord.evalGroupLetter gen s) *
                PSTS.SignedWord.evalGroup gen w := rfl
          _ = p.2.1 * PSTS.SignedWord.evalGroup gen (s :: w) := by
            simp [PSTS.SignedWord.evalGroup, mul_assoc]

/-- Every two vertices carrying the same intrinsic B-component index
are joined by a genuine B-path inside the single-B coset extension. -/
theorem singleCosetEGraph_connected_on_index
    (B : Finset ι) (p q : K.AttachedCosetVertex B)
    (hidx : p.1 = q.1) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.singleCosetEGraph B).Follows p w q := by
  have hqCoset : q.2.1 ∈ K.componentAmbientCoset B p.1 := by
    rw [hidx]
    exact q.2.2
  have hrelative :
      p.2.1⁻¹ * q.2.1 ∈ generatedSubgroup gen B :=
    K.componentAmbientCoset_relative_mem B p.1 p.2.2 hqCoset
  obtain ⟨w, hw, hval⟩ :=
    exists_word_uses_eq_of_mem_generatedSubgroup gen B hrelative
  obtain ⟨r, hpath, hridx, hrval⟩ :=
    K.singleCosetEGraph_follows_word B p hw
  have hendpoint : r.2.1 = q.2.1 := by
    rw [hrval, hval]
    simp [mul_assoc]
  have hrq : r = q :=
    K.attachedValue_injective_of_same_index B
      (hridx.trans hidx) hendpoint
  exact ⟨w, hw, hrq ▸ hpath⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
