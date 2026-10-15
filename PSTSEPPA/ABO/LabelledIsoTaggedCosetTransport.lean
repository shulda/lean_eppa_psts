import PSTSEPPA.ABO.BijectiveTaggedCosetTransport
import PSTSEPPA.ABO.LabelledGroupSubalphabetCosetTransport

/-!
# Automatic tagged full-coset equivalences under labelled group isomorphisms

The precise original ABO coset extension attaches a DISTINCT copy of
the full B-coset to EACH intrinsic B-connected component of an old
incomplete signed Cayley skeleton. The component tags cannot be
forgotten: two distinct components can meet the SAME ambient coset.

The generic tagged-coset transport theorem already requires two
explicit conditions on a coordinate map between ambient groups:
forward and backward compatibility with each attached B-coset.

We DISCHARGE these conditions for every true same-labelled GROUP
ISOMORPHISM E : Γ ≃* Δ and ANY signed skeleton graph isomorphism
whose vertex map is induced by E. The proof relies on both:
- the previously verified equivalence of real B-path COMPONENT INDEX
  quotient tags under the bijective signed graph morphism; and
- exact preservation and reflection of algebraic LEFT B-coset
  membership under E, for every B and every coset basepoint.

It produces an actual bijection of the full DEPENDENT tagged
AttachedCosetVertex types, preserving their intrinsic component
indices and honest ambient group values. It also preserves old
skeleton embeddings and commutes with every subalphabet enlargement.

This is the exact vertex-tag-level transport prerequisite for
the printed T(Y₁) versus SourceH₁ full proper-alphabet CE and its
intersection-support gluing. No completed quotient-graph isomorphism,
augmentation or higher-rank Condition 5.2 is claimed here.
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
variable (E : Γ ≃* Δ)
variable (hgen : ∀ i : ι, E (genΓ i) = genΔ i)
variable (hcoord : ∀ x : L.Vertex, E x.1 = (f.onVertex x).1)

-- These compatibility hypotheses are used in proof bodies even when
-- the proposition contains only the induced tagged-coset transport.
include hgen hcoord

/-- All component-indexed B-cosets map INTO the matching
tagged target coset. A B-component tag is transported through
actual signed path reflection, NOT ambient coordinate equality. -/
theorem labelledGroupIso_attachedCosetForward :
    L.AttachedCosetForwardCompatible K f hv he E := by
  intro B c x hx
  induction c using Quotient.inductionOn with
  | h u =>
      have hsrc :
          x ∈ generatedLeftCoset genΓ B u.1 := by
        change x ∈ L.componentAmbientCoset B (L.componentClass B u) at hx
        simpa only [L.componentAmbientCoset_class] using hx
      change E x ∈ K.componentAmbientCoset B
        ((L.componentIndexEquiv_of_graphIso K f hv he B)
          (L.componentClass B u))
      rw [L.componentIndexEquiv_of_graphIso_class,
        K.componentAmbientCoset_class]
      rw [← hcoord u]
      exact (labelledMulEquiv_mem_generatedLeftCoset_iff
        genΓ genΔ E hgen B u.1 x).mpr hsrc

/-- Every target coset point in its CORRECT transported
component-tagged copy has a preimage in the matching source
copy. The inverse coordinate is E.symm, not an arbitrary chosen
representative of a quotient or an overlapping ambient coset. -/
theorem labelledGroupIso_attachedCosetBackward :
    L.AttachedCosetBackwardCompatible K f hv he E := by
  intro B c y hy
  induction c using Quotient.inductionOn with
  | h u =>
      have htgt :
          y ∈ generatedLeftCoset genΔ B (E u.1) := by
        change y ∈ K.componentAmbientCoset B
          ((L.componentIndexEquiv_of_graphIso K f hv he B)
            (L.componentClass B u)) at hy
        rw [L.componentIndexEquiv_of_graphIso_class,
          K.componentAmbientCoset_class, ← hcoord u] at hy
        exact hy
      refine ⟨E.symm y, ?_, ?_⟩
      · change E.symm y ∈
          L.componentAmbientCoset B (L.componentClass B u)
        rw [L.componentAmbientCoset_class]
        apply (labelledMulEquiv_mem_generatedLeftCoset_iff
          genΓ genΔ E hgen B u.1 (E.symm y)).mp
        simpa only [E.apply_symm_apply] using htgt
      · exact E.apply_symm_apply y

/-- A genuine equivalence of ACTUAL ATTACHED COSSET VERTICES:
the intrinsic quotient B-component tag and the ambient point are
transported together, so equal group coordinates of different
components are never spuriously identified. -/
noncomputable def attachedCosetEquivOfLabelledGroupIso
    (B : Finset ι) :
    L.AttachedCosetVertex B ≃ K.AttachedCosetVertex B :=
  L.attachedCosetEquivOfGraphIso K f hv he E E.injective
    (L.labelledGroupIso_attachedCosetForward K f hv he E hgen hcoord)
    (L.labelledGroupIso_attachedCosetBackward K f hv he E hgen hcoord) B

/-- Every coordinate of the tagged attached coset bijection
is literally transported by E. The component tag is retained
through the independent signed path-component equivalence. -/
@[simp] theorem attachedCosetEquivOfLabelledGroupIso_value
    (B : Finset ι) (p : L.AttachedCosetVertex B) :
    K.attachedValue B
      (L.attachedCosetEquivOfLabelledGroupIso
        K f hv he E hgen hcoord B p) =
    E (L.attachedValue B p) := by
  exact L.attachedCosetMapOfGraphIso_value
    K f hv he E
    (L.labelledGroupIso_attachedCosetForward K f hv he E hgen hcoord)
    B p

/-- Old original skeleton vertices embed as the correct
COMPONENT-TAGGED points in both coset systems. -/
theorem attachedCosetEquivOfLabelledGroupIso_oldVertex
    (B : Finset ι) (x : L.Vertex) :
    L.attachedCosetEquivOfLabelledGroupIso K f hv he E hgen hcoord B
        (L.attachedOfSkeletonVertex B x) =
      K.attachedOfSkeletonVertex B (f.onVertex x) := by
  exact L.attachedCosetMapOfGraphIso_oldVertex
    K f hv he E
    (L.labelledGroupIso_attachedCosetForward K f hv he E hgen hcoord)
    hcoord B x

/-- Algebraic label-preserving transport commutes exactly with
ALL original tagged-coset enlargements B ⊆ C, including B=C
and the empty alphabet. This is needed for source Equation 3.10
intersection-supported quotient gluing. -/
theorem attachedCosetEquivOfLabelledGroupIso_natural
    (B C : Finset ι) (hBC : B ⊆ C)
    (p : L.AttachedCosetVertex B) :
    L.attachedCosetEquivOfLabelledGroupIso K f hv he E hgen hcoord C
      (L.attachedSubalphabetMap B C hBC p) =
    K.attachedSubalphabetMap B C hBC
      (L.attachedCosetEquivOfLabelledGroupIso K f hv he E hgen hcoord B p) := by
  exact L.attachedCosetMapOfGraphIso_natural
    K f hv he E
    (L.labelledGroupIso_attachedCosetForward K f hv he E hgen hcoord)
    B C hBC p

end CayleySubgraphSpec
end ABO
end PSTSEPPA
