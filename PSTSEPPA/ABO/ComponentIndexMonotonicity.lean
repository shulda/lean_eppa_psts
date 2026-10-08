import PSTSEPPA.ABO.ComponentIndexedCosets

/-!
# Naturality of intrinsic component indices under subalphabet inclusion

For B ⊆ C, every realised B-path is a C-path, hence each intrinsic
B-component lies in a unique intrinsic C-component. This induces a
canonical map between the corresponding quotient component indices.

The attached B-coset is canonically included in the larger C-coset
associated with that index. The construction is uniform even when
B = C, B = ∅ or a generator acts trivially.

This is the algebraic bookkeeping required for the inclusions
CE(G,K;B) → CE(G,K;C) and the equal-alphabet cases of ABO (3.9)–(3.12).
-/

namespace PSTSEPPA
namespace ABO

namespace LabelWord

variable {ι : Type*}

/-- Support is monotone under alphabet inclusion. -/
theorem Uses.mono
    {B C : Finset ι} (hBC : B ⊆ C)
    {w : LabelWord ι} (hw : Uses B w) :
    Uses C w := by
  induction w with
  | nil =>
      trivial
  | cons s w ih =>
      exact ⟨hBC hw.1, ih hw.2⟩

end LabelWord

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

theorem subalphabetReachable_mono
    (B C : Finset ι) (hBC : B ⊆ C)
    {x y : K.Vertex}
    (hxy : K.SubalphabetReachable B x y) :
    K.SubalphabetReachable C x y := by
  rcases hxy with ⟨w, hw, hp⟩
  exact ⟨w, hw.mono hBC, hp⟩

/-- Every intrinsic B-component has a canonical containing C-component
whenever B ⊆ C. -/
def componentIndexMap
    (B C : Finset ι) (hBC : B ⊆ C) :
    K.ComponentIndex B → K.ComponentIndex C :=
  fun c =>
    Quotient.liftOn c (K.componentClass C)
      (by
        intro x y hxy
        exact (K.componentClass_eq_iff C x y).2
          (K.subalphabetReachable_mono B C hBC hxy))

@[simp]
theorem componentIndexMap_class
    (B C : Finset ι) (hBC : B ⊆ C)
    (x : K.Vertex) :
    K.componentIndexMap B C hBC (K.componentClass B x) =
      K.componentClass C x :=
  rfl

/-- Identity on component indices, including the equal-alphabet case. -/
theorem componentIndexMap_self
    (B : Finset ι) (c : K.ComponentIndex B) :
    K.componentIndexMap B B (subset_rfl) c = c := by
  refine Quotient.inductionOn c ?_
  intro x
  rfl

/-- Refinement of alphabets composes exactly as expected. -/
theorem componentIndexMap_comp
    (B C D : Finset ι)
    (hBC : B ⊆ C) (hCD : C ⊆ D)
    (c : K.ComponentIndex B) :
    K.componentIndexMap C D hCD
        (K.componentIndexMap B C hBC c) =
      K.componentIndexMap B D (hBC.trans hCD) c := by
  refine Quotient.inductionOn c ?_
  intro x
  rfl

/-- The ambient B-coset of an intrinsic B-component lies in the ambient
C-coset of its containing intrinsic C-component. -/
theorem componentAmbientCoset_mono
    (B C : Finset ι) (hBC : B ⊆ C)
    (c : K.ComponentIndex B) :
    K.componentAmbientCoset B c ⊆
      K.componentAmbientCoset C (K.componentIndexMap B C hBC c) := by
  refine Quotient.inductionOn c ?_
  intro x y hy
  change y ∈ generatedLeftCoset gen B x.1 at hy
  change y ∈ generatedLeftCoset gen C x.1
  exact generatedSubgroup_mono gen hBC hy

/-- Canonical enlargement of a tagged B-coset point to the corresponding
tagged C-coset point. Its underlying ambient group value is unchanged. -/
def attachedSubalphabetMap
    (B C : Finset ι) (hBC : B ⊆ C)
    (p : K.AttachedCosetVertex B) :
    K.AttachedCosetVertex C :=
  ⟨K.componentIndexMap B C hBC p.1,
    ⟨p.2.1, K.componentAmbientCoset_mono B C hBC p.1 p.2.2⟩⟩

@[simp]
theorem attachedSubalphabetMap_value
    (B C : Finset ι) (hBC : B ⊆ C)
    (p : K.AttachedCosetVertex B) :
    K.attachedValue C (K.attachedSubalphabetMap B C hBC p) =
      K.attachedValue B p :=
  rfl

@[simp]
theorem attachedSubalphabetMap_index
    (B C : Finset ι) (hBC : B ⊆ C)
    (p : K.AttachedCosetVertex B) :
    K.attachedIndex C (K.attachedSubalphabetMap B C hBC p) =
      K.componentIndexMap B C hBC (K.attachedIndex B p) :=
  rfl

/-- The canonical embeddings of skeleton vertices commute with
alphabet enlargement. -/
theorem attachedSubalphabetMap_ofSkeletonVertex
    (B C : Finset ι) (hBC : B ⊆ C)
    (x : K.Vertex) :
    K.attachedSubalphabetMap B C hBC
        (K.attachedOfSkeletonVertex B x) =
      K.attachedOfSkeletonVertex C x := by
  apply Sigma.ext rfl
  apply Subtype.ext
  rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
