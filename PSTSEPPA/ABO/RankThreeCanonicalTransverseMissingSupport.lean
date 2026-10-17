import PSTSEPPA.ABO.AllRankTwoLetterBranchingCommonCore
import Mathlib.Data.Finset.Card

/-!
# Canonical missing-letter support at the first higher parent rank

The first genuinely higher-rank cluster case has parent |A| = 3
and proper B of size two, so A \\ B is a singleton {c}.
The certified arbitrary-rank transverse-step lemma shows that
whenever a genuine B-cluster vertex has two different outgoing
B-letter edges, some actual component-tagged support D exists
which has no letters from B but does have a letter outside B.

At this first higher rank there is ONLY ONE possible
nonempty such support alphabet: precisely A \\ B.
Thus every genuine two-direction switching vertex carries
the CANONICAL missing-letter support, not merely some
choice of a lower-alphabet patch.

This is a precise local common-core statement in the
three-vertex C₂³ off-skeleton cluster benchmark
{c,ac,bc}: the central switching vertex is supported
over the missing letter c. It holds for EVERY admissible
original incomplete signed A-skeleton and EVERY generated
retractable Γ, not just that example.

No statement is made that *all* switching vertices share
the same intrinsic component tag, or that a common core
of the entire B-component has already been constructed.
Those are separate higher-rank Lemma 4.3/Prop. 3.23 gates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

/-- Elementary finite-support principle: if D⊆A contains no
B-letter, has at least one actual outside-B letter, and
A\\B has at most one letter, then D is EXACTLY A\\B.
The explicit non-B-containment prevents a false empty-core
argument. -/
theorem outsideCore_eq_singleton_complement
    (D A B : Finset ι)
    (hDA : D ⊆ A)
    (hNoB : ∀ i : ι, i ∈ D → i ∉ B)
    (hNotContained : ¬ D ⊆ B)
    (hComplSmall : (A \\ B).card ≤ 1) :
    D = A \\ B := by
  classical
  have hSubset : D ⊆ A \\ B := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hDA hi, hNoB i hi⟩
  have hWitness : ∃ c : ι, c ∈ D ∧ c ∉ B := by
    by_contra hn
    apply hNotContained
    intro i hi
    by_contra hiNot
    exact hn ⟨i, hi, hiNot⟩
  obtain ⟨c, hcD, _hcNotB⟩ := hWitness
  have hcCompl : c ∈ A \\ B := hSubset hcD
  apply Finset.Subset.antisymm hSubset
  intro i hi
  have heq : i = c :=
    (Finset.card_le_one.mp hComplSmall) i hi c hcCompl
  rw [heq]
  exact hcD

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- THE canonical first higher-rank transverse patch core.

For |A|=3 and |B|=2, if a selected genuine old+fresh
B-component is on the CLUSTER branch (no full C⊇B
constituent at its root z), and a vertex y reached by
an actual signed B-word has outgoing REAL oriented signed
B-edges with different base letters, then y has an actual
TAGGED constituent presentation supported by the exact
singleton complement A\\B.

This is a theorem about the source gluing quotient's
actual vertices/edges and their true old component tags.
It does not assume global Cayley ambient injectivity or
artificial stationary-loop completion. -/
theorem allProperCoset_rank_three_transverse_B_edges_missing_support
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : A.card = 3)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hBcard : B.card = 2)
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
    K.MultiCosetVertexSupported
      (allProperCosetFamily A) hadm hgen hret (A \\ B) y := by
  let P := allProperCosetFamily A
  obtain ⟨D, hD, hNoB, hDNotB⟩ :=
    K.allProperCoset_B_component_transverse_edges_common_outside_core
      hadm hgen hret B hBP hBcard.le
      z hNoLargeZ y hzy
      e f heSource hfSource heB hfB hDifferent
  obtain ⟨hDP, p, hp⟩ := hD
  have hDA : D ⊆ A :=
    ((mem_allProperCosetFamily A D).mp hDP).subset
  have hBA : B ⊆ A :=
    ((mem_allProperCosetFamily A B).mp hBP).subset
  have hComplCard : (A \\ B).card ≤ 1 := by
    have hDiff : (A \\ B).card = A.card - B.card :=
      Finset.card_sdiff_of_subset hBA
    omega
  have hExact : D = A \\ B :=
    outsideCore_eq_singleton_complement D A B
      hDA hNoB hDNotB hComplCard
  simpa only [hExact] using
    (show K.MultiCosetVertexSupported P hadm hgen hret D y
      from ⟨hDP, p, hp⟩)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
