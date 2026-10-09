import PSTSEPPA.ABO.MultiCosetFullComponentFromSuperset
import PSTSEPPA.ABO.MultiCosetComponentSupportDichotomy

/-!
# Singleton-or-full B-components for rank-one B in arbitrary ambient rank

The rank-two *ambient* base (#172) is not enough to analyse
higher-rank induction: A can be arbitrarily large even when a
component alphabet B is tiny. The strict lower-patch theorem
supplies a better base at |B|≤1, independent of |A|.

If a B-component contains no point of any selected completed
C-coset with B⊆C, every B-edge would have to be completed
over a strict subalphabet C∩B ⊊ B. When B has at most one
letter, this is impossible for any B-labelled edge. Hence
the actual B-component is a singleton.

Otherwise, the previously proved selected-superset theorem
identifies the *entire* B-component with a full tagged
B-coset inside a selected C-copy. We state the genuine
path-component iff, not just containment in ambient G[B].

No whole-component cluster property, bridge-freeness,
global Cayley injectivity or extra low-rank admissibility
assumptions are used.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A B-component with no support by a selected C⊇B is a singleton
whenever |B|≤1, regardless of the size of the ambient alphabet A. -/
theorem allProperCoset_rank_one_no_large_component_singleton
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hcard : B.card ≤ 1)
    (z y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoLargeZ :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C z)
    (hzy : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w y) :
    y = z := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨w, hw, hpath⟩ := hzy
  cases hpath with
  | nil _ => rfl
  | @cons _ _ t tail e hsource hlabel hrest =>
      have htB : signedBase (G.label e) ∈ B := by
        rw [hlabel]
        exact hw.1
      have hzRefl :
          ∃ u : LabelWord ι, LabelWord.Uses B u ∧
            G.Follows z u z :=
        ⟨[], LabelWord.uses_nil B, G.follows_nil_iff.mpr rfl⟩
      obtain ⟨C, hCP, p, s, hStrict, hletter, he⟩ :=
        K.allProperCoset_B_component_pointwise_no_large_strict_patches
          hadm hgen hret B hBP z hNoLargeZ
          z hzRefl e hsource htB
      have hsB : signedBase s.1 ∈ B :=
        (Finset.mem_inter.mp hletter).2
      have hBsub : B ⊆ C ∩ B := by
        intro t ht
        have hts : t = signedBase s.1 :=
          (Finset.card_le_one.mp hcard) t ht (signedBase s.1) hsB
        subst t
        exact hletter
      exact False.elim (hStrict.2 hBsub)

/-- At any ambient rank, each actual B-component for |B|≤1
is either a tagged full B-coset inside some selected C⊇B,
or a singleton. The first disjunct identifies all reachable
vertices by an exact iff and therefore includes completeness
of the entire component, not merely a local edge statement. -/
theorem allProperCoset_rank_one_B_component_full_or_singleton
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hcard : B.card ≤ 1)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    (∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (p : K.AttachedCosetVertex C),
      B ⊆ C ∧
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP p = z ∧
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows z w y) ↔
        ∃ q : K.AttachedCosetVertex C,
          q.1 = p.1 ∧
          q.2.1 ∈ generatedLeftCoset gen B p.2.1 ∧
          y = K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP q) ∨
    (∀ y : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret,
      (∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows z w y) → y = z) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  by_cases hLarge :
      ∃ (C : Finset ι) (hCP : C ∈ P.alphabets),
        B ⊆ C ∧
          K.MultiCosetVertexSupported P hadm hgen hret C z
  · left
    obtain ⟨C, hCP, hBC, _, p, hp⟩ := hLarge
    refine ⟨C, hCP, p, hBC, hp, ?_⟩
    intro y
    apply K.multiCoset_B_component_full_if_meets_selected_superset
      P hadm hgen hret C hCP B hBC p z
    exact ⟨[], LabelWord.uses_nil B,
      G.follows_nil_iff.mpr hp⟩
  · right
    intro y hzy
    apply K.allProperCoset_rank_one_no_large_component_singleton
      hadm hgen hret B hBP hcard z y
    · intro C hCP hBC hsupport
      exact hLarge ⟨C, hCP, hBC, hsupport⟩
    · exact hzy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
