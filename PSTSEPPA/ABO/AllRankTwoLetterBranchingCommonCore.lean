import PSTSEPPA.ABO.MultiCosetComponentSupportDichotomy
import PSTSEPPA.ABO.MultiCosetVertexSupport
import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents

/-!
# The first genuine higher-rank common core: two transverse B-steps

The source's higher-rank whole-component cluster proof requires a
common core when *different proper constituent patches* meet.

For the first genuinely new case, |B| = 2, start at an original
old+fresh multiCE vertex z NOT lying in any selected complete
C-constituent whose alphabet contains B. The accepted lower-patch
theorem guarantees that each real signed B-edge from the B-component
of z has a completed C-patch with C∩B ⊊ B.

We prove: if two outgoing real signed edges from one B-component
vertex y have DIFFERENT underlying B-letters, their two completed
patches meet at y over an ACTUAL component-tagged common support
D = C∩E which
  (1) is disjoint from B, and
  (2) contains some alphabet letter outside B.

This is not merely an equality of ambient group coordinates.
It uses the literal source/label edge quotient and exact
intersection of tagged quotient-vertex supports. The nonempty
outside-B core follows from exclusion of all larger C⊇B
constituents and genuine support monotonicity, rather than
being asserted as an extra assumption.

It is a local common-core / branching lemma valid at arbitrary
parent rank |A|. It does NOT claim that one such core governs
every vertex of an off-skeleton B-component. That entire-component
coherence is the still-open higher-rank Proposition 3.23 / Lemma 4.3
induction step.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If no actual selected full C-copy with B⊆C supports z,
then NO support alphabet D of z can be contained in B:
a D-copy would embed into the selected complete B-copy
via the genuine component-indexed attached-subalphabet map. -/
theorem allProperCoset_no_large_support_not_subset_B
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoLarge :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C z)
    (D : Finset ι)
    (hD : K.MultiCosetVertexSupported
      (allProperCosetFamily A) hadm hgen hret D z) :
    ¬ D ⊆ B := by
  let P := allProperCosetFamily A
  intro hDB
  obtain ⟨hDP, p, hp⟩ := hD
  let q : K.AttachedCosetVertex B :=
    K.attachedSubalphabetMap D B hDB p
  have hB : K.MultiCosetVertexSupported
      P hadm hgen hret B z := by
    refine ⟨hBP, q, ?_⟩
    calc
      K.multiCosetInclude P hadm hgen hret B hBP q =
          K.multiCosetInclude P hadm hgen hret D hDP p :=
        (K.multiCosetInclude_alphabet_mono
          P hadm hgen hret D B hDB hDP hBP p).symm
      _ = z := hp
  exact hNoLarge B hBP (subset_rfl) hB

/-- If |B| <= 2, two REAL oriented signed B-edges of distinct
underlying letters leaving the same no-large vertex y force
a COMMON tagged support D of their sources with no B-letter,
but D itself is not contained in B.

In particular D contains a genuine outside-B core letter.
Both input edges retain their original source/label tokens,
including formal inverses and geometric loops. -/
theorem allProperCoset_two_transverse_B_edges_common_outside_core
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hBcard : B.card ≤ 2)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoLarge :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C y)
    (e f : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (heSource :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source e = y)
    (hfSource :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source f = y)
    (heB : signedBase ((K.multiCosetEGraph
      (allProperCosetFamily A) hadm hgen hret).label e) ∈ B)
    (hfB : signedBase ((K.multiCosetEGraph
      (allProperCosetFamily A) hadm hgen hret).label f) ∈ B)
    (hDifferent :
      signedBase ((K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).label e) ≠
      signedBase ((K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).label f)) :
    ∃ D : Finset ι,
      K.MultiCosetVertexSupported
        (allProperCosetFamily A) hadm hgen hret D y ∧
      (∀ i : ι, i ∈ D → i ∉ B) ∧
      ¬ D ⊆ B := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  have hRefl : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      G.Follows y w y :=
    ⟨[], LabelWord.uses_nil B, EGraph.Follows.nil y⟩
  obtain ⟨C, hCP, p, s, hStrictC, hsC, he⟩ :=
    K.allProperCoset_B_component_pointwise_no_large_strict_patches
      hadm hgen hret B hBP y hNoLarge y hRefl
      e heSource heB
  obtain ⟨E, hEP, q, t, hStrictE, hsE, hf⟩ :=
    K.allProperCoset_B_component_pointwise_no_large_strict_patches
      hadm hgen hret B hBP y hNoLarge y hRefl
      f hfSource hfB
  have hSupportC : K.MultiCosetVertexSupported
      P hadm hgen hret C y := by
    refine ⟨hCP, p, ?_⟩
    have hSource :
        G.source e =
          K.multiCosetInclude P hadm hgen hret C hCP p := by
      rw [he]
      rfl
    exact hSource.symm.trans heSource
  have hSupportE : K.MultiCosetVertexSupported
      P hadm hgen hret E y := by
    refine ⟨hEP, q, ?_⟩
    have hSource :
        G.source f =
          K.multiCosetInclude P hadm hgen hret E hEP q := by
      rw [hf]
      rfl
    exact hSource.symm.trans hfSource
  have hSupportInter :
      K.MultiCosetVertexSupported P hadm hgen hret (C ∩ E) y :=
    K.allProperCosetVertex_support_inter
      hadm hgen hret y C E hSupportC hSupportE
  have hCCard : (C ∩ B).card ≤ 1 :=
    Nat.lt_succ_iff.mp
      (lt_of_lt_of_le (Finset.card_lt_card hStrictC) hBcard)
  have hECard : (E ∩ B).card ≤ 1 :=
    Nat.lt_succ_iff.mp
      (lt_of_lt_of_le (Finset.card_lt_card hStrictE) hBcard)
  have hNoB : ∀ i : ι, i ∈ C ∩ E → i ∉ B := by
    intro i hi hiB
    have hiC : i ∈ C ∩ B :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1, hiB⟩
    have hiE : i ∈ E ∩ B :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).2, hiB⟩
    have hEqC : i = signedBase s.1 :=
      (Finset.card_le_one.mp hCCard) i hiC (signedBase s.1) hsC
    have hEqE : i = signedBase t.1 :=
      (Finset.card_le_one.mp hECard) i hiE (signedBase t.1) hsE
    apply hDifferent
    calc
      signedBase (G.label e) = signedBase s.1 := by
        rw [he]
        rfl
      _ = i := hEqC.symm
      _ = signedBase t.1 := hEqE
      _ = signedBase (G.label f) := by
        rw [hf]
        rfl
  exact ⟨C ∩ E, hSupportInter, hNoB,
    K.allProperCoset_no_large_support_not_subset_B
      hadm hgen hret B hBP y hNoLarge (C ∩ E) hSupportInter⟩

/-- Genuine first nontrivial CLUSTER-BRANCH local common core
at ANY vertex y of a B-component initially based at z.

The no-large condition is required ONLY AT z. Its invariance along
the realised signed B-word path z→y ensures that the two transverse
outgoing B-edge patches at y have a common, tagged, outside-B
support. Neither ambient group equality nor fake completion
edges enter the argument. -/
theorem allProperCoset_B_component_transverse_edges_common_outside_core
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hBcard : B.card ≤ 2)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoLargeZ :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C z)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hzy : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w y)
    (e f : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (heSource :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source e = y)
    (hfSource :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source f = y)
    (heB : signedBase ((K.multiCosetEGraph
      (allProperCosetFamily A) hadm hgen hret).label e) ∈ B)
    (hfB : signedBase ((K.multiCosetEGraph
      (allProperCosetFamily A) hadm hgen hret).label f) ∈ B)
    (hDifferent :
      signedBase ((K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).label e) ≠
      signedBase ((K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).label f)) :
    ∃ D : Finset ι,
      K.MultiCosetVertexSupported
        (allProperCosetFamily A) hadm hgen hret D y ∧
      (∀ i : ι, i ∈ D → i ∉ B) ∧
      ¬ D ⊆ B := by
  let P := allProperCosetFamily A
  have hNoLargeY :
      ∀ (C : Finset ι) (hCP : C ∈ P.alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported P hadm hgen hret C y := by
    intro C hCP hBC hSupportedY
    have hSupportedZ :
        K.MultiCosetVertexSupported P hadm hgen hret C z :=
      (K.multiCoset_selected_superset_support_invariant
        P hadm hgen hret B C hBC z y hzy).mpr hSupportedY
    exact hNoLargeZ C hCP hBC hSupportedZ
  exact K.allProperCoset_two_transverse_B_edges_common_outside_core
    hadm hgen hret B hBP hBcard
    y hNoLargeY e f heSource hfSource heB hfB hDifferent

end CayleySubgraphSpec
end ABO
end PSTSEPPA
