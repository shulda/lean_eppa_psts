import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Component-indexed coset copies for ABO coset extensions

ABO's construction CE(G,K;B) attaches a *separate* copy of the B-coset to
each intrinsic B-component of the skeleton K. Two different B-components
may sit in the very same ambient group coset; they must not accidentally
be identified by the extension.

Here B-components are represented as equivalence classes under actual
B-labelled paths, and their corresponding ambient cosets are defined by
quotient recursion (independent of the chosen representative).  The type
`AttachedCosetVertex` retains the component tag even for overlapping
ambient cosets. This is the bookkeeping foundation for the later gluing
quotient; it is not itself the full coset-extension graph.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The equivalence relation of intrinsic B-reachability in the skeleton. -/
def subalphabetSetoid (B : Finset ι) : Setoid K.Vertex where
  r := K.SubalphabetReachable B
  iseqv := {
    refl := fun x => K.subalphabetReachable_refl B x
    symm := fun h => K.subalphabetReachable_symm B h
    trans := fun hxy hyz =>
      K.subalphabetReachable_trans B hxy hyz
  }

/-- Actual connected B-components, not merely ambient B-cosets. -/
def ComponentIndex (B : Finset ι) :=
  Quotient (K.subalphabetSetoid B)

/-- The B-component containing a skeleton vertex. -/
def componentClass (B : Finset ι) (x : K.Vertex) :
    K.ComponentIndex B :=
  Quotient.mk (K.subalphabetSetoid B) x

/-- Two vertices lie in the same component precisely when they are joined
by an actual path in K with labels from B. -/
theorem componentClass_eq_iff (B : Finset ι) (x y : K.Vertex) :
    K.componentClass B x = K.componentClass B y ↔
      K.SubalphabetReachable B x y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Every intrinsic B-component selects one ambient left B-coset, without
choosing a basepoint.  This is well-defined because B-paths in the skeleton
stay inside ambient B-cosets. -/
def componentAmbientCoset
    (B : Finset ι) (c : K.ComponentIndex B) : Set Γ :=
  Quotient.liftOn c
    (fun x : K.Vertex => generatedLeftCoset gen B x.1)
    (by
      intro x y hxy
      exact generatedLeftCoset_eq_of_mem gen B
        (K.subalphabetReachable_implies_coset B x y hxy))

@[simp]
theorem componentAmbientCoset_class
    (B : Finset ι) (x : K.Vertex) :
    K.componentAmbientCoset B (K.componentClass B x) =
      generatedLeftCoset gen B x.1 :=
  rfl

/-- A B-coset vertex with its component identity retained. Distinct indices
are never identified, even if their ambient cosets overlap. -/
def AttachedCosetVertex (B : Finset ι) :=
  Σ c : K.ComponentIndex B,
    {y : Γ // y ∈ K.componentAmbientCoset B c}

/-- Forget the component tag, retaining the underlying ambient group point. -/
def attachedValue (B : Finset ι)
    (p : K.AttachedCosetVertex B) : Γ :=
  p.2.1

/-- The component tag of an attached point. -/
def attachedIndex (B : Finset ι)
    (p : K.AttachedCosetVertex B) : K.ComponentIndex B :=
  p.1

/-- Canonical embedding of each skeleton vertex into its own component-tagged
coset copy; the quotient used to glue the graph later will identify this
point with the original skeleton vertex. -/
def attachedOfSkeletonVertex (B : Finset ι)
    (x : K.Vertex) : K.AttachedCosetVertex B :=
  ⟨K.componentClass B x, ⟨x.1, by
    change x.1 ∈ generatedLeftCoset gen B x.1
    exact self_mem_generatedLeftCoset gen B x.1⟩⟩

@[simp]
theorem attachedValue_ofSkeletonVertex
    (B : Finset ι) (x : K.Vertex) :
    K.attachedValue B (K.attachedOfSkeletonVertex B x) = x.1 :=
  rfl

@[simp]
theorem attachedIndex_ofSkeletonVertex
    (B : Finset ι) (x : K.Vertex) :
    K.attachedIndex B (K.attachedOfSkeletonVertex B x) =
      K.componentClass B x :=
  rfl

/-- The canonical inclusion into component-tagged copies is injective,
regardless of accidental overlaps between cosets belonging to different
intrinsic components. -/
theorem attachedOfSkeletonVertex_injective
    (B : Finset ι) :
    Function.Injective (K.attachedOfSkeletonVertex B) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (K.attachedValue B) h

/-- The ambient-coordinate projection is injective within one fixed
component-tagged coset.  No stability assumption is needed here. -/
theorem attachedValue_injective_of_same_index
    (B : Finset ι)
    {p q : K.AttachedCosetVertex B}
    (hindex : K.attachedIndex B p = K.attachedIndex B q)
    (hvalue : K.attachedValue B p = K.attachedValue B q) :
    p = q := by
  rcases p with ⟨c, xp⟩
  rcases q with ⟨d, yq⟩
  cases hindex
  have hxy : xp = yq := Subtype.ext hvalue
  cases hxy
  rfl

/-- Source-facing warning following ABO Proposition 3.18.

When two different intrinsic B-components occupy the same ambient B-coset,
the canonical map from the tagged extension to the ambient group is
necessarily *not* globally injective.  This is precisely why the component
tags must be retained throughout the coset-extension construction. -/
theorem attachedValue_not_injective_of_overlapping_components
    (B : Finset ι)
    (x y : K.Vertex)
    (hcomp : K.componentClass B x ≠ K.componentClass B y)
    (hoverlap : x.1 ∈ generatedLeftCoset gen B y.1) :
    ¬ Function.Injective (K.attachedValue B) := by
  intro hinj
  let p : K.AttachedCosetVertex B :=
    K.attachedOfSkeletonVertex B x
  let q : K.AttachedCosetVertex B :=
    ⟨K.componentClass B y, ⟨x.1, hoverlap⟩⟩
  have hval : K.attachedValue B p = K.attachedValue B q := rfl
  have heq := hinj hval
  have hclass :
      K.componentClass B x = K.componentClass B y :=
    congrArg (K.attachedIndex B) heq
  exact hcomp hclass

end CayleySubgraphSpec

end ABO
end PSTSEPPA
