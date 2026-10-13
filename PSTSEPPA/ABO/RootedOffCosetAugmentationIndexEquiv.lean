import PSTSEPPA.ABO.RootedSourceOffCosetIndexEquiv
import PSTSEPPA.ABO.RootedSourceMultiCosetVertexQuotient

/-!
# Exact source/local index equivalence for ALL rooted B-augmentations

A corrected ABO type-(2) augmentation is indexed by BOTH a selected
proper subalphabet B⊂A and an old multi-coset quotient vertex z
whose entire component-tagged B-summand has EMPTY preimage.
The off-B condition is NOT ambient Γ-coordinate nonmembership.

For any true rooted A-component of an incomplete Γ-Cayley source
skeleton, |A|=2, and Γ merely 2-retractable, the certified local
Γ[A] ↔ original-source exact vertex-quotient equivalence preserves
and REFLECTS this predicate for every selected proper B (#389).

We assemble the ENTIRE dependent index universe, with the literal
alphabet B retained and the exact glued quotient vertex transported,
into a genuine equivalence. This includes empty alphabets and an
empty family and makes NO assumption of nonempty off-B choices.

The result is the stage-INDEX half of the promised inclusion of
every genuine source Z1 B-augmentation into the finite local
rank-two G2 supercatalogue. Constructing all corresponding
augmented completed EGraphs and their action iso is separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- All genuine LOCAL B-augmentation choices: a proper
alphabet tag B and an exact component-tagged glued vertex
outside the complete selected B-constituent. -/
abbrev rootedLocalOffCosetAugmentationIndex
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (P : CosetFamilySpec A) :=
  Σ B : {B : Finset ι // B ∈ P.alphabets},
    {z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex P
        ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
          hcard.le)
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le) //
      ¬ ∃ p : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex B.1,
        (K.intrinsicComponentLocalSlice A root).multiCosetInclude
          P
          ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
            hcard.le)
          (isGenerated_trivialCompletionGenerator gen A)
          (retractable_trivialCompletionGenerator_of_kRetractable
            gen 2 hret A hcard.le)
          B.1 B.2 p = z}

/-- ALL ORIGINAL source-rooted B-augmentation choices,
including their genuine alphabet tag, with old vertices glued
only by intersection-supported component-tagged equivalence. -/
abbrev rootedAmbientOffCosetAugmentationIndex
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (P : CosetFamilySpec A) :=
  Σ B : {B : Finset ι // B ∈ P.alphabets},
    {z : Quotient (K.rootedAmbientMultiCosetSetoid
        A hcard hret root P) //
      ¬ ∃ p : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B.1,
        K.rootedAmbientMultiCosetInclude
          A hcard hret root P B.1 B.2 p = z}

/-- The exact full proper-alphabet B-augmentation INDEX set
is EQUIVALENT between genuine original-source components
and their local Γ[A] models. Preserves the literal B tag,
not just ambient Γ-values or total numbers of vertices. -/
noncomputable def rootedOffCosetAugmentationIndexEquiv
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (P : CosetFamilySpec A) :
    K.rootedLocalOffCosetAugmentationIndex A hcard hret root P ≃
      K.rootedAmbientOffCosetAugmentationIndex A hcard hret root P where
  toFun j :=
    ⟨j.1, ⟨K.rootedLocalMultiCosetVertexQuotientEquiv
        A hcard hret root P j.2.1,
      (K.rootedLocalMultiCosetOffCoset_iff
        A hcard hret root P j.1.1 j.1.2 j.2.1).mp j.2.2⟩⟩
  invFun j :=
    ⟨j.1, ⟨(K.rootedLocalMultiCosetVertexQuotientEquiv
        A hcard hret root P).symm j.2.1,
      (K.rootedLocalMultiCosetOffCoset_iff A hcard hret root P
        j.1.1 j.1.2
        ((K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root P).symm j.2.1)).mpr
        (by
          simpa only [Equiv.apply_symm_apply]
            using j.2.2)⟩⟩
  left_inv := by
    rintro ⟨B, ⟨z, hz⟩⟩
    let ev := K.rootedLocalMultiCosetVertexQuotientEquiv
      A hcard hret root P
    change
      (⟨B, ⟨ev.symm (ev z), _⟩⟩ :
        K.rootedLocalOffCosetAugmentationIndex A hcard hret root P) =
        ⟨B, ⟨z, hz⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨B, ⟨z, hz⟩⟩
    let ev := K.rootedLocalMultiCosetVertexQuotientEquiv
      A hcard hret root P
    change
      (⟨B, ⟨ev (ev.symm z), _⟩⟩ :
        K.rootedAmbientOffCosetAugmentationIndex A hcard hret root P) =
        ⟨B, ⟨z, hz⟩⟩
    simp only [Equiv.apply_symm_apply]

/-- The stage-index equivalence retains the genuine
selected alphabet B exactly, including B=∅. -/
@[simp] theorem rootedOffCosetAugmentationIndexEquiv_alphabet
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (P : CosetFamilySpec A)
    (j : K.rootedLocalOffCosetAugmentationIndex A hcard hret root P) :
    (K.rootedOffCosetAugmentationIndexEquiv
      A hcard hret root P j).1 = j.1 :=
  rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
