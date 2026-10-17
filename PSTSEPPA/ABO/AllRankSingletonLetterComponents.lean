import PSTSEPPA.ABO.MultiCosetComponentSupportDichotomy
import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents

/-!
# Genuine singleton-letter components at arbitrary parent rank

Corrected ABO's higher-rank cluster induction requires a classification
of *entire* B-components in full proper-subalphabet coset extensions.
The rank-two base (Proposition 4.4) proves singleton off-skeleton
components using the assumption |A| <= 2. We can obtain a
different, rank-INDEPENDENT base: assume only |B| <= 1, while
the parent alphabet A and its incomplete old skeleton are arbitrary.

For a vertex z, either some actual selected complete C-coset
with B ⊆ C contains z, in which case the ENTIRE genuine signed
B-component is exactly the corresponding full B-left coset in
that same tagged C-constituent; or NO selected C ⊇ B supports z.

In the latter case our certified strict-lower-patch theorem says
that any genuine outgoing signed B-edge at z would have to live
in a patch over C ∩ B ⊊ B. With |B| <= 1, this intersection
has no letters. Hence no such edge exists and z is B-isolated.

All claims are made for the ORIGINAL incomplete signed EGraph
and the actual quotient of tagged coset constituents; there is
no new edge from trivial completion, no identification by ambient
group coordinates, and no assumption of global coset embeddedness.
For |B| >= 2 the off-skeleton component can genuinely have
multiple vertices and the cluster-common-core induction remains open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- No outgoing REAL signed B-edge can start at z if z is unsupported
by every selected complete C-constituent with B ⊆ C and |B| <= 1.

This works at ARBITRARY parent rank |A|: the strict-lower support
of any would-be B-labelled edge is impossible for a singleton
(or empty) B. The argument concerns original edge tokens. -/
theorem allProperCoset_small_B_no_large_no_signed_edges
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hSmall : B.card ≤ 1)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoLarge :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C z)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (heSource :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source e = z)
    (heB :
      signedBase ((K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).label e) ∈ B) :
    False := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨C, hCP, p, s, hStrict, hs, he⟩ :=
    K.allProperCoset_B_component_pointwise_no_large_strict_patches
      hadm hgen hret B hBP z hNoLarge
      z ⟨[], LabelWord.uses_nil B, EGraph.Follows.nil z⟩
      e heSource heB
  have hPositive : 0 < (C ∩ B).card :=
    Finset.card_pos.mpr ⟨signedBase s.1, hs⟩
  have hStrictCard : (C ∩ B).card < B.card :=
    Finset.card_lt_card hStrict
  omega

/-- If |B| <= 1 and z has no tagged full C-coset support
with B ⊆ C, its ENTIRE original signed B-connected component
is exactly the singleton {z}; not merely a statement about
missing old skeleton vertices or about ambient Cayley cosets. -/
theorem allProperCoset_small_B_no_large_isolated
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hSmall : B.card ≤ 1)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoLarge :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C z)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hPath :
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows z w y) :
    y = z := by
  obtain ⟨w, hw, hFollows⟩ := hPath
  cases hFollows with
  | nil _ =>
      rfl
  | @cons _ _ s tail e hsrc hlabel hrest =>
      have hmem :
          signedBase ((K.multiCosetEGraph
            (allProperCosetFamily A) hadm hgen hret).label e) ∈ B := by
        rw [hlabel]
        exact hw.1
      exact False.elim
        (K.allProperCoset_small_B_no_large_no_signed_edges
          hadm hgen hret B hBP hSmall z hNoLarge
          e hsrc hmem)

/-- The full higher-parent-rank singleton-letter dichotomy.

For *any* admissible original signed Cayley A-skeleton in a
generated retractable ambient group, even when |A| is large,
and *every* selected B ⊊ A with |B| <= 1, an intrinsic signed
B-component is EITHER a full B-left coset inside one actual
component-tagged selected C-copy (C ⊇ B), with exact B-word
reachability, OR an isolated singleton.

This is the genuine |B| <= 1 induction base for the higher-rank
cluster-property analysis. It does not resolve genuine
multi-patch B-clusters for |B| >= 2. -/
theorem allProperCoset_small_B_component_full_or_singleton
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hSmall : B.card ≤ 1)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    (∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (hBC : B ⊆ C)
      (p : K.AttachedCosetVertex C),
      z = K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP p ∧
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
          hadm hgen hret).Follows z w y) →
        y = z) := by
  classical
  let P := allProperCosetFamily A
  by_cases hLarge :
      ∃ (C : Finset ι) (hCP : C ∈ P.alphabets),
        B ⊆ C ∧ K.MultiCosetVertexSupported
          P hadm hgen hret C z
  · obtain ⟨C, hCP, hBC, ⟨_, p, hpz⟩⟩ := hLarge
    left
    refine ⟨C, hCP, hBC, p, hpz.symm, ?_⟩
    intro y
    rw [← hpz]
    exact K.multiCoset_selected_C_subalphabet_B_component_exact
      P hadm hgen hret C hCP B hBC p y
  · right
    have hNoLarge :
        ∀ (C : Finset ι) (hCP : C ∈ P.alphabets),
          B ⊆ C →
            ¬ K.MultiCosetVertexSupported P hadm hgen hret C z := by
      intro C hCP hBC hSupported
      exact hLarge ⟨C, hCP, hBC, hSupported⟩
    intro y hy
    exact K.allProperCoset_small_B_no_large_isolated
      hadm hgen hret B hBP hSmall z hNoLarge y hy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
