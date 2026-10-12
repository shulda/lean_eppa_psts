import PSTSEPPA.ABO.RootedSourceOffCosetIndexEquiv

/-!
# Exact ambient coordinate on the TRUE source-rooted glued quotient

The source H1 group is only 2-retractable, so the canonical
multiCosetAmbientValue defined using GLOBAL retractability cannot
be applied to its original A-component directly. However the
literal source-rooted coset gluing relation is already a Setoid,
transported from its true Γ[A] normalization (#380).

For two intersecting component-tagged attached coset copies, the
underlying Γ-coordinate is equal even before requiring any global
retractability. Hence the true original glued quotient carries
a well-defined ambient coordinate, without identifying DISTINCT
tagged vertices merely because their ambient values agree.

The exact source/local quotient equivalence translates that
coordinate by the original component root r:
  sourceValue (vertexEquiv z) = r * localValue z.
This is an essential ingredient for the FULL B-coset augmentation:
its attaching coset must be based at the true ambient coordinate
of the selected OFF-B quotient vertex, not an arbitrary Γ[A] lift.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The actual ambient Γ-coordinate of a component-tagged
source-rooted multi-coset quotient vertex. This descends along
the literal intersection-supported gluing Setoid, not an
ambient coordinate equivalence relation. -/
noncomputable def rootedAmbientMultiCosetValue
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A)
    (z : Quotient (K.rootedAmbientMultiCosetSetoid A hcard hret root P)) :
    Γ := by
  let M := K.subalphabetComponentSubgraph A root
  exact Quotient.liftOn z
    (fun p => M.attachedValue p.1.1 p.2)
    (by
      intro p q hpq
      change M.ShareIntersectionSupport p.1.1 q.1.1 p.2 q.2 at hpq
      exact M.shareIntersectionSupport_value_eq p.1.1 q.1.1 hpq)

/-- Every included actual B-coset point retains its OWN ambient
coordinate, even though its component tag remains present in the
quotient and the value map need not be injective. -/
@[simp] theorem rootedAmbientMultiCosetValue_include
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B) :
    K.rootedAmbientMultiCosetValue A hcard hret root P
      (K.rootedAmbientMultiCosetInclude A hcard hret root P B hBP p) =
        (K.subalphabetComponentSubgraph A root).attachedValue B p :=
  rfl

/-- Ambient coordinates of the TRUE original source-rooted and
local normalized multi-coset quotients agree under the exact
left translation by the original component root. Equality here
is a projection property, NOT injectivity of the value maps. -/
theorem rootedAmbientMultiCosetValue_natural
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex P
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le)) :
    K.rootedAmbientMultiCosetValue A hcard hret root P
        (K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root P z) =
    root.1 * ((K.intrinsicComponentLocalSlice A root).multiCosetAmbientValue
      P
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le)
      z : Γ) := by
  induction z using Quotient.inductionOn with
  | h p =>
      rcases p with ⟨b, p⟩
      change
        (K.subalphabetComponentSubgraph A root).attachedValue b.1
          (K.rootedLocalAttachedCosetMap A b.1
            (P.proper b.1 b.2).subset root p) =
        root.1 * ((K.intrinsicComponentLocalSlice A root).attachedValue b.1 p : Γ)
      exact K.rootedLocalAttachedCosetMap_value
        A b.1 (P.proper b.1 b.2).subset root p

end CayleySubgraphSpec
end ABO
end PSTSEPPA
