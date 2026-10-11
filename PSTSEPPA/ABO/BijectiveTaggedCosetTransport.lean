import PSTSEPPA.ABO.BijectiveComponentIndexTransport

/-!
# Natural bijections of genuinely component-tagged attached cosets

For an honest signed graph isomorphism between incomplete Cayley
skeletons, the component-index quotients agree (#361). Suppose
also an injective map between their ambient group coordinates
which maps each component-tagged B-coset exactly onto its
corresponding target coset. There is then a canonical BIJECTION
between the actual dependent attached-coset vertex types.

This map preserves the intrinsic component tag, transports
each original skeleton vertex to its correctly tagged copy, and
commutes with every B subset C alphabet enlargement. Separate
component tags are retained EVEN IF their ambient coset values
coincide. No false global coordinate surjectivity is required.

This is constituent-level quotient/gluing naturality. Proving
its explicit coset compatibility assumptions for the translated
source H1-cover components requires #358 and the component
bijection #352. Full coset-extension quotient, augmentations,
Condition 5.2, higher-rank induction and PSTS EPPA remain open.
-/

namespace PSTSEPPA
namespace ABO
namespace CayleySubgraphSpec

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A D : Finset ι}
variable (L : CayleySubgraphSpec genΓ A)
variable (K : CayleySubgraphSpec genΔ D)
variable (f : LabelledGraphHom
  (L.toEGraph).toLabelledGraph
  (K.toEGraph).toLabelledGraph)
variable (hv : Function.Bijective f.onVertex)
variable (he : Function.Bijective f.onEdge)
variable (coord : Γ → Δ)

/-- Forward component-tagged coset membership compatibility. -/
def AttachedCosetForwardCompatible : Prop :=
  ∀ (B : Finset ι) (c : L.ComponentIndex B) (x : Γ),
    x ∈ L.componentAmbientCoset B c →
    coord x ∈ K.componentAmbientCoset B
      ((L.componentIndexEquiv_of_graphIso K f hv he B) c)

/-- The target coset of every true component is the image of
the source coset, with no surjectivity outside those cosets. -/
def AttachedCosetBackwardCompatible : Prop :=
  ∀ (B : Finset ι) (c : L.ComponentIndex B) (y : Δ),
    y ∈ K.componentAmbientCoset B
      ((L.componentIndexEquiv_of_graphIso K f hv he B) c) →
    ∃ x : Γ, x ∈ L.componentAmbientCoset B c ∧ coord x = y

/-- Canonical transfer of tagged B-coset vertices. -/
noncomputable def attachedCosetMapOfGraphIso
    (hforward : L.AttachedCosetForwardCompatible K f hv he coord)
    (B : Finset ι) :
    L.AttachedCosetVertex B → K.AttachedCosetVertex B :=
  fun p =>
    ⟨(L.componentIndexEquiv_of_graphIso K f hv he B) p.1,
      ⟨coord p.2.1, hforward B p.1 p.2.1 p.2.2⟩⟩

@[simp] theorem attachedCosetMapOfGraphIso_index
    (hforward : L.AttachedCosetForwardCompatible K f hv he coord)
    (B : Finset ι) (p : L.AttachedCosetVertex B) :
    K.attachedIndex B
      (L.attachedCosetMapOfGraphIso K f hv he coord hforward B p) =
    (L.componentIndexEquiv_of_graphIso K f hv he B)
      (L.attachedIndex B p) := rfl

@[simp] theorem attachedCosetMapOfGraphIso_value
    (hforward : L.AttachedCosetForwardCompatible K f hv he coord)
    (B : Finset ι) (p : L.AttachedCosetVertex B) :
    K.attachedValue B
      (L.attachedCosetMapOfGraphIso K f hv he coord hforward B p) =
    coord (L.attachedValue B p) := rfl

/-- Two tagged points are equal only when BOTH the original
component tag and its coordinate agree. -/
theorem attachedCosetMapOfGraphIso_injective
    (hcoord : Function.Injective coord)
    (hforward : L.AttachedCosetForwardCompatible K f hv he coord)
    (B : Finset ι) :
    Function.Injective
      (L.attachedCosetMapOfGraphIso K f hv he coord hforward B) := by
  intro p q hpq
  apply L.attachedValue_injective_of_same_index B
  · apply (L.componentIndexEquiv_of_graphIso K f hv he B).injective
    exact congrArg (K.attachedIndex B) hpq
  · apply hcoord
    exact congrArg (K.attachedValue B) hpq

/-- Every target tagged point has a genuine source preimage
inside its CORRECT component-indexed coset copy. -/
theorem attachedCosetMapOfGraphIso_surjective
    (hforward : L.AttachedCosetForwardCompatible K f hv he coord)
    (hback : L.AttachedCosetBackwardCompatible K f hv he coord)
    (B : Finset ι) :
    Function.Surjective
      (L.attachedCosetMapOfGraphIso K f hv he coord hforward B) := by
  intro q
  let F := L.componentIndexEquiv_of_graphIso K f hv he B
  let c : L.ComponentIndex B := F.symm q.1
  have hindex : F c = q.1 := F.apply_symm_apply q.1
  have hq : q.2.1 ∈ K.componentAmbientCoset B (F c) := by
    rw [hindex]
    exact q.2.2
  obtain ⟨x, hx, hval⟩ := hback B c q.2.1 hq
  refine ⟨⟨c, ⟨x, hx⟩⟩, ?_⟩
  apply K.attachedValue_injective_of_same_index B
  · exact hindex
  · exact hval

/-- Equivalence of all genuine attached B-coset quotient tags
and coordinates, without global surjectivity of coord. -/
noncomputable def attachedCosetEquivOfGraphIso
    (hcoord : Function.Injective coord)
    (hforward : L.AttachedCosetForwardCompatible K f hv he coord)
    (hback : L.AttachedCosetBackwardCompatible K f hv he coord)
    (B : Finset ι) :
    L.AttachedCosetVertex B ≃ K.AttachedCosetVertex B :=
  Equiv.ofBijective
    (L.attachedCosetMapOfGraphIso K f hv he coord hforward B)
    ⟨L.attachedCosetMapOfGraphIso_injective K f hv he coord
        hcoord hforward B,
      L.attachedCosetMapOfGraphIso_surjective K f hv he coord
        hforward hback B⟩

/-- Original skeleton vertices remain exactly their correctly
tagged old vertices after transporting the group coordinate. -/
theorem attachedCosetMapOfGraphIso_oldVertex
    (hforward : L.AttachedCosetForwardCompatible K f hv he coord)
    (hvertex : ∀ x : L.Vertex, coord x.1 = (f.onVertex x).1)
    (B : Finset ι) (x : L.Vertex) :
    L.attachedCosetMapOfGraphIso K f hv he coord hforward B
      (L.attachedOfSkeletonVertex B x) =
    K.attachedOfSkeletonVertex B (f.onVertex x) := by
  apply K.attachedValue_injective_of_same_index B
  · exact L.componentIndexEquiv_of_graphIso_class K f hv he B x
  · exact hvertex x

/-- Compatibility of attached coset copies with EVERY
inclusion B subset C, the precursor to gluing naturality. -/
theorem attachedCosetMapOfGraphIso_natural
    (hforward : L.AttachedCosetForwardCompatible K f hv he coord)
    (B C : Finset ι) (hBC : B ⊆ C)
    (p : L.AttachedCosetVertex B) :
    L.attachedCosetMapOfGraphIso K f hv he coord hforward C
      (L.attachedSubalphabetMap B C hBC p) =
    K.attachedSubalphabetMap B C hBC
      (L.attachedCosetMapOfGraphIso K f hv he coord hforward B p) := by
  apply K.attachedValue_injective_of_same_index C
  · exact (L.componentIndexEquiv_of_graphIso_natural
      K f hv he B C hBC p.1).symm
  · rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
