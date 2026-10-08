import PSTSEPPA.ABO.ComponentIndexedCosets
import PSTSEPPA.ABO.AugmentedCluster

/-!
# Single-alphabet ABO coset extension: labelled graph

For a skeleton K and a subalphabet B, CE(G,K;B) consists of a separate
full B-coset over every intrinsic B-component of K, with the old edges
labelled outside B retained. Its vertex set is represented by
`AttachedCosetVertex`, which remembers the component index.

This presentation is isomorphic to the quotient in ABO equation (3.8):
old B-labelled skeleton edges are already represented by the unique
corresponding edge of their attached B-coset, and all non-B-labelled
skeleton edges are retained with their own inverse tokens.

We construct the literal labelled graph and its canonical morphism to
the ambient Cayley graph. No ambient injectivity is claimed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

open ClusterSpec

variable (K : CayleySubgraphSpec gen A)

/-- A step by a B-letter stays inside the ambient B-coset associated
with an intrinsic B-component, independently of its representative. -/
theorem componentAmbientCoset_step
    (B : Finset ι) (s : SignedLabel ι)
    (hs : signedBase s ∈ B) :
    ∀ (c : K.ComponentIndex B) (x : Γ),
      x ∈ K.componentAmbientCoset B c →
      x * PSTS.SignedWord.evalGroupLetter gen s ∈
        K.componentAmbientCoset B c := by
  intro c
  refine Quotient.inductionOn c ?_
  intro v x hx
  change x ∈ generatedLeftCoset gen B v.1 at hx
  change
    x * PSTS.SignedWord.evalGroupLetter gen s ∈
      generatedLeftCoset gen B v.1
  have he : (x, s) ∈ FullCosetEdgeSet gen B v.1 :=
    ⟨hx, hs⟩
  simpa only [cayleyGraph.target_eq_mul_evalGroupLetter] using
    (fullCosetEdge_target_mem gen B v.1 he)

/-- Move along the unique signed B-edge in a component-tagged full coset. -/
def cosetStep
    (B : Finset ι) (p : K.AttachedCosetVertex B)
    (s : {s : SignedLabel ι // signedBase s ∈ B}) :
    K.AttachedCosetVertex B :=
  ⟨p.1,
    ⟨p.2.1 * PSTS.SignedWord.evalGroupLetter gen s.1,
      K.componentAmbientCoset_step B s.1 s.2 p.1 p.2.1 p.2.2⟩⟩

@[simp]
theorem cosetStep_index
    (B : Finset ι) (p : K.AttachedCosetVertex B)
    (s : {s : SignedLabel ι // signedBase s ∈ B}) :
    (K.cosetStep B p s).1 = p.1 :=
  rfl

@[simp]
theorem cosetStep_value
    (B : Finset ι) (p : K.AttachedCosetVertex B)
    (s : {s : SignedLabel ι // signedBase s ∈ B}) :
    (K.cosetStep B p s).2.1 =
      p.2.1 * PSTS.SignedWord.evalGroupLetter gen s.1 :=
  rfl

/-- Reverse the signed edge label without changing its underlying alphabet. -/
def inverseBLabel
    (B : Finset ι)
    (s : {s : SignedLabel ι // signedBase s ∈ B}) :
    {s : SignedLabel ι // signedBase s ∈ B} :=
  ⟨PSTS.SignedLetter.inv s.1, by simpa using s.2⟩

@[simp]
theorem inverseBLabel_inv
    (B : Finset ι)
    (s : {s : SignedLabel ι // signedBase s ∈ B}) :
    inverseBLabel B (inverseBLabel B s) = s := by
  apply Subtype.ext
  exact PSTS.SignedLetter.inv_inv s.1

/-- Two consecutive inverse B-steps return to the same tagged vertex. -/
theorem cosetStep_inverse
    (B : Finset ι) (p : K.AttachedCosetVertex B)
    (s : {s : SignedLabel ι // signedBase s ∈ B}) :
    K.cosetStep B (K.cosetStep B p s) (inverseBLabel B s) = p := by
  rcases p with ⟨c, ⟨x, hx⟩⟩
  simp [cosetStep, inverseBLabel,
    PSTS.SignedWord.evalGroupLetter_inv, mul_assoc]

/-- Old skeleton edges with labels outside the completed B-alphabet. -/
abbrev OutsideEdge (B : Finset ι) :=
  {e : K.Edge // signedBase e.1.2 ∉ B}

/-- The full signed B-edges in all component-tagged coset copies. -/
abbrev CosetEdge (B : Finset ι) :=
  K.AttachedCosetVertex B ×
    {s : SignedLabel ι // signedBase s ∈ B}

/-- All edges of the B-coset extension, without duplicating old B-edges. -/
abbrev SingleCosetEdge (B : Finset ι) :=
  (K.OutsideEdge B) ⊕ (K.CosetEdge B)

/-- The source of an extension edge. -/
noncomputable def singleCosetSource
    (B : Finset ι) : K.SingleCosetEdge B →
        K.AttachedCosetVertex B
  | .inl e => K.attachedOfSkeletonVertex B ((K.toEGraph).source e.1)
  | .inr e => e.1

/-- Label of an extension edge. -/
def singleCosetLabel
    (B : Finset ι) : K.SingleCosetEdge B → SignedLabel ι
  | .inl e => e.1.1.2
  | .inr e => e.2.1

/-- Reverse a directed edge token; the two summands are preserved because
reversal never changes the underlying (unsigned) generator. -/
noncomputable def singleCosetInv
    (B : Finset ι) : K.SingleCosetEdge B → K.SingleCosetEdge B
  | .inl e =>
      .inl
        ⟨⟨(cayleyGraph gen).inv e.1.1,
              K.inv_mem e.1.1 e.1.2⟩,
          by
            change signedBase
              ((cayleyGraph gen).label ((cayleyGraph gen).inv e.1.1)) ∉ B
            rw [(cayleyGraph gen).label_inv_eq]
            change signedBase (PSTS.SignedLetter.inv e.1.1.2) ∉ B
            simpa only [signedBase_inv] using e.2⟩
  | .inr e =>
      .inr (K.cosetStep B e.1 e.2, inverseBLabel B e.2)

theorem singleCosetInv_inv
    (B : Finset ι) (e : K.SingleCosetEdge B) :
    K.singleCosetInv B (K.singleCosetInv B e) = e := by
  cases e with
  | inl e =>
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Subtype.ext
      exact (cayleyGraph gen).inv_inv e.1.1
  | inr e =>
      apply congrArg Sum.inr
      apply Prod.ext
      · exact K.cosetStep_inverse B e.1 e.2
      · exact inverseBLabel_inv B e.2

theorem singleCosetInv_ne
    (B : Finset ι) (e : K.SingleCosetEdge B) :
    K.singleCosetInv B e ≠ e := by
  cases e with
  | inl e =>
      intro h
      have hinv : (cayleyGraph gen).inv e.1.1 = e.1.1 :=
        congrArg (fun q : K.OutsideEdge B => q.1.1) (Sum.inl.inj h)
      exact (cayleyGraph gen).inv_ne e.1.1 hinv
  | inr e =>
      intro h
      have hinv :
          PSTS.SignedLetter.inv e.2.1 = e.2.1 :=
        congrArg (fun q : K.CosetEdge B => q.2.1) (Sum.inr.inj h)
      have hne : PSTS.SignedLetter.inv e.2.1 ≠ e.2.1 := by
        cases e.2.1 <;> simp [PSTS.SignedLetter.inv]
      exact hne hinv

theorem singleCosetLabel_inv
    (B : Finset ι) (e : K.SingleCosetEdge B) :
    K.singleCosetLabel B (K.singleCosetInv B e) =
      PSTS.SignedLetter.inv (K.singleCosetLabel B e) := by
  cases e with
  | inl e =>
      exact (cayleyGraph gen).label_inv_eq e.1.1
  | inr e =>
      rfl

/-- The single-B coset extension as a labelled graph, with literal
component-tagged copies even when the ambient B-cosets overlap. -/
noncomputable def singleCosetLabelledGraph
    (B : Finset ι) :
    LabelledGraph (K.AttachedCosetVertex B) (K.SingleCosetEdge B) ι where
  source := K.singleCosetSource B
  inv := K.singleCosetInv B
  inv_inv := K.singleCosetInv_inv B
  inv_ne := K.singleCosetInv_ne B
  label := K.singleCosetLabel B
  label_inv := K.singleCosetLabel_inv B

/-- Forget tags: the extension has a canonical labelled graph morphism
to the ambient Cayley graph, not asserted to be injective globally. -/
noncomputable def singleCosetAmbientHom
    (B : Finset ι) :
    LabelledGraphHom
      (K.singleCosetLabelledGraph B)
      (cayleyGraph gen).toEGraph.toLabelledGraph where
  onVertex p := p.2.1
  onEdge
    | .inl e => e.1.1
    | .inr e => (e.1.2.1, e.2.1)
  map_source := by
    intro e
    cases e <;> rfl
  map_inv := by
    intro e
    cases e with
    | inl e => rfl
    | inr e =>
        apply Prod.ext
        · change
            e.1.2.1 * PSTS.SignedWord.evalGroupLetter gen e.2.1 =
              (cayleyGraph gen).target (e.1.2.1, e.2.1)
          exact (cayleyGraph.target_eq_mul_evalGroupLetter gen e.1.2.1 e.2.1).symm
        · rfl
  map_label := by
    intro e
    cases e <;> rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
