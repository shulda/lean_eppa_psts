import PSTSEPPA.ABO.MultiCosetVertexSupport
import PSTSEPPA.ABO.MaximalProperAlphabets
import Mathlib.Data.Finset.Card

/-!
# Cofinality of codimension-one constituents in a full coset extension

The beginning of the common-core argument in ABO Lemma 4.3 covers
an off-skeleton B-component by constituent cosets whose alphabets
are maximal proper subalphabets of A. This reduction must respect
component tags, not merely ambient Cayley coordinates.

Every proper D⊊A is contained in an explicit coatom A\{a},
choosing a missing letter a∈A\D. Every tagged D-coset point
maps to a tagged coatom point under attachedSubalphabetMap,
and the resulting point has the exact same image in the global
vertex quotient, by the already checked gluing laws.

Thus every quotient vertex admits a coatom-supported presentation.
No global injectivity of the ambient Cayley projection is assumed.
No cluster property, bridge-freeness or A-rank lower bound is used:
when A is empty the vertex universe of the full proper extension
is empty and the quantified assertion is vacuous.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Every proper finite alphabet D⊊A is contained in a maximal proper
alphabet C of cardinality exactly |A|-1. The construction is A.erase a. -/
theorem exists_coatom_containing_proper_alphabet
    (A D : Finset ι) (hDA : D ⊂ A) :
    ∃ C : Finset ι,
      D ⊆ C ∧ C ⊂ A ∧ C.card + 1 = A.card := by
  classical
  have hMissing : ∃ a : ι, a ∈ A ∧ a ∉ D := by
    by_contra hn
    apply hDA.2
    intro x hxA
    by_contra hxD
    exact hn ⟨x, hxA, hxD⟩
  obtain ⟨a, haA, haD⟩ := hMissing
  have hDsub : D ⊆ A.erase a := by
    intro x hxD
    apply Finset.mem_erase.mpr
    constructor
    · intro hxa
      apply haD
      simpa [hxa] using hxD
    · exact hDA.1 hxD
  have hEstrict : A.erase a ⊂ A := by
    refine ⟨Finset.erase_subset a A, ?_⟩
    intro hAE
    have haErase : a ∈ A.erase a := hAE haA
    simp at haErase
  exact ⟨A.erase a, hDsub, hEstrict,
    Finset.card_erase_add_one haA⟩

variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An exact tagged D-coset presentation of a quotient vertex extends to
a selected codimension-one C-coset presentation of the SAME vertex.
The tag is transported by the canonical attached-subalphabet map.
No injectivity of the global ambient-coordinate projection is used. -/
theorem allProperCoset_constituent_extend_to_coatom
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D : Finset ι)
    (hDP : D ∈ (allProperCosetFamily A).alphabets)
    (p : K.AttachedCosetVertex D) :
    ∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (hDC : D ⊆ C),
      C.card + 1 = A.card ∧
      K.multiCosetInclude (allProperCosetFamily A) hadm hgen hret
        C hCP (K.attachedSubalphabetMap D C hDC p) =
      K.multiCosetInclude (allProperCosetFamily A) hadm hgen hret
        D hDP p := by
  obtain ⟨C, hDC, hCA, hcard⟩ :=
    exists_coatom_containing_proper_alphabet A D
      ((mem_allProperCosetFamily A D).mp hDP)
  have hCP : C ∈ (allProperCosetFamily A).alphabets :=
    (mem_allProperCosetFamily A C).mpr hCA
  refine ⟨C, hCP, hDC, hcard, ?_⟩
  exact (K.multiCosetInclude_alphabet_mono
    (allProperCosetFamily A) hadm hgen hret
    D C hDC hDP hCP p).symm

/-- Vertex coatom cover, a source-facing prerequisite for the finite
maximal-constituent decomposition in ABO Lemma 4.3. For every quotient
vertex, the presentation retains the correct intrinsic component tag. -/
theorem allProperCosetVertex_exists_coatom_support
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    ∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets),
      C.card + 1 = A.card ∧
      K.MultiCosetVertexSupported (allProperCosetFamily A)
        hadm hgen hret C z := by
  obtain ⟨D, hDP, p, hp⟩ :=
    K.multiCosetVertex_exists_support
      (allProperCosetFamily A) hadm hgen hret z
  obtain ⟨C, hCP, hDC, hcard, hInclude⟩ :=
    K.allProperCoset_constituent_extend_to_coatom
      hadm hgen hret D hDP p
  refine ⟨C, hCP, hcard, hCP,
    K.attachedSubalphabetMap D C hDC p, ?_⟩
  exact hInclude.trans hp

end CayleySubgraphSpec
end ABO
end PSTSEPPA
