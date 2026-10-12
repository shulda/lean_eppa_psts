import PSTSEPPA.ABO.RootedSourceMultiCosetVertexQuotient

/-!
# Transport of the genuine off-B augmentation index at source rank two

Corrected ABO Definition 5.3 augments a completed multi-coset EGraph
at an old vertex z lying OUTSIDE the image of an attached full B-coset.
This is a component-tagged, quotient-geometric condition, not a
restriction on the ambient Cayley group coordinate of z.

For each true rooted source A-component and its locally normalized
Γ[A] skeleton, #380 already proves a bijection of the full glued
vertex quotients. We check that this bijection transports the exact
B-summand inclusion, using the previously proved equivalence of
full component-tagged attached B-coset points. Therefore the
property of being off the entire selected B constituent is
preserved AND REFLECTED, and the correct type of B-augmentation roots
is itself equivalent across source and local models.

This does NOT yet attach a new B-coset or identify the augmented
signed EGraphs, but it eliminates one required stage-indexing gate,
without imposing global retractability on the original Γ.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The literal inclusion of the ORIGINAL ambient rooted
component's component-tagged B-coset vertices into its
glued source quotient. No arbitrary group-coordinate collapse. -/
noncomputable def rootedAmbientMultiCosetInclude
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
    (P : CosetFamilySpec A)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B) :
    Quotient (K.rootedAmbientMultiCosetSetoid A hcard hret root P) :=
  Quotient.mk (K.rootedAmbientMultiCosetSetoid A hcard hret root P)
    (⟨⟨B, hBP⟩, p⟩ :
      (K.subalphabetComponentSubgraph A root).MultiCosetRawVertex P)

/-- Actual local B-summand inclusion COMMUTES with the complete
source-rooted glued vertex quotient equivalence. The map includes
the component INDEX and its B-coset coordinate; it does not simply
compare ambient Γ values. -/
@[simp] theorem rootedLocalMultiCosetInclude_natural
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
    (P : CosetFamilySpec A)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex B) :
    K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret root P
        ((K.intrinsicComponentLocalSlice A root).multiCosetInclude P
          ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
            hcard.le)
          (isGenerated_trivialCompletionGenerator gen A)
          (retractable_trivialCompletionGenerator_of_kRetractable
            gen 2 hret A hcard.le)
          B hBP p) =
      K.rootedAmbientMultiCosetInclude A hcard hret root P B hBP
        (K.rootedLocalAttachedCosetMap A B
          (P.proper B hBP).subset root p) :=
  rfl

/-- The source and local quotients agree EXACTLY on whether a
chosen old point lies outside ALL points of the selected B-coset
constituent. This is the real source Definition 5.3 off-component
condition, not ambient Γ-coset nonmembership. -/
theorem rootedLocalMultiCosetOffCoset_iff
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
    (P : CosetFamilySpec A)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex P
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le)) :
    (¬ ∃ p : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex B,
      (K.intrinsicComponentLocalSlice A root).multiCosetInclude P
        ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
          hcard.le)
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le)
        B hBP p = z) ↔
    (¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
      K.rootedAmbientMultiCosetInclude A hcard hret root P B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root P z) := by
  let e := K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret root P
  let f := K.rootedLocalAttachedCosetMap A B
    (P.proper B hBP).subset root
  constructor
  · intro hOff ⟨q, hq⟩
    obtain ⟨p, hp⟩ := K.rootedLocalAttachedCosetMap_surjective
      A B (P.proper B hBP).subset root q
    have hEq : e
        ((K.intrinsicComponentLocalSlice A root).multiCosetInclude P
          ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
            hcard.le)
          (isGenerated_trivialCompletionGenerator gen A)
          (retractable_trivialCompletionGenerator_of_kRetractable
            gen 2 hret A hcard.le)
          B hBP p) = e z := by
      calc
        e ((K.intrinsicComponentLocalSlice A root).multiCosetInclude P
            ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
              hcard.le)
            (isGenerated_trivialCompletionGenerator gen A)
            (retractable_trivialCompletionGenerator_of_kRetractable
              gen 2 hret A hcard.le)
            B hBP p) =
          K.rootedAmbientMultiCosetInclude A hcard hret root P B hBP (f p) :=
            K.rootedLocalMultiCosetInclude_natural A hcard hret root P B hBP p
        _ = K.rootedAmbientMultiCosetInclude
            A hcard hret root P B hBP q := congrArg _ hp
        _ = e z := hq
    exact hOff ⟨p, e.injective hEq⟩
  · intro hOff ⟨p, hp⟩
    apply hOff
    refine ⟨f p, ?_⟩
    calc
      K.rootedAmbientMultiCosetInclude A hcard hret root P B hBP (f p) =
        e ((K.intrinsicComponentLocalSlice A root).multiCosetInclude P
          ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
            hcard.le)
          (isGenerated_trivialCompletionGenerator gen A)
          (retractable_trivialCompletionGenerator_of_kRetractable
            gen 2 hret A hcard.le)
          B hBP p) :=
            (K.rootedLocalMultiCosetInclude_natural
              A hcard hret root P B hBP p).symm
      _ = e z := congrArg e hp

end CayleySubgraphSpec
end ABO
end PSTSEPPA
