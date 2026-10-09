import PSTSEPPA.ABO.SelectedCosetSliceConnectivity
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Simultaneous refinement of true paths across finitely many tagged cosets

ABO Lemma 4.3 assembles whole components from finite families of
maximal-constituent slices. The already proved selected-C-slice theorem
says that when two vertices belong to the SAME exact C-component tag,
global B-reachability between them refines to B ∩ C-reachability.

Here we iterate this principle across an arbitrary finite LIST of
selected coset alphabets. The same pair of quotient vertices must be
represented in one common tagged C-copy for EACH alphabet in the list.
A global B-word path can then be replaced by an actual signed-word path
over the intersection of B with all those alphabets, without changing
either endpoint or using the ambient Cayley projection injectively.

The resulting lemma is deliberately conditional on the existence of
the simultaneous tagged presentations of BOTH vertices. Proving that
every vertex of a whole B-component belongs to the intersection of
all its constituent cosets, as required in the later common-core
argument, is a strictly stronger and still-open assertion.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Two multi-coset quotient vertices lie in the SAME intrinsically
component-tagged complete C-copy. Equality merely of their ambient
Cayley coordinates is not sufficient. -/
def MultiCosetSameTaggedConstituent
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι)
    (z t : K.MultiCosetVertex P hadm hgen hret) : Prop :=
  ∃ (hCP : C ∈ P.alphabets)
    (p q : K.AttachedCosetVertex C),
      p.1 = q.1 ∧
      K.multiCosetInclude P hadm hgen hret C hCP p = z ∧
      K.multiCosetInclude P hadm hgen hret C hCP q = t

/-- If two vertices are in the same selected tagged C-copy,
global B-reachability between them can be refined to a real
(B ∩ C)-labelled path, including incomparable B and C. -/
theorem multiCoset_sameTagged_reachable_iff_inter
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (z t : K.MultiCosetVertex P hadm hgen hret)
    (hSame :
      K.MultiCosetSameTaggedConstituent P hadm hgen hret C z t) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows z w t) ↔
    (∃ w : LabelWord ι, LabelWord.Uses (B ∩ C) w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows z w t) := by
  obtain ⟨hCP, p, q, hpq, hpz, hqt⟩ := hSame
  have hSlice :=
    K.multiCoset_selected_C_slice_B_reachable_iff_inter_reachable
      P hadm hgen hret B C hCP p q hpq
  constructor
  · rintro ⟨w, hw, hp⟩
    have hpath :
        (K.multiCosetEGraph P hadm hgen hret).Follows
          (K.multiCosetInclude P hadm hgen hret C hCP p) w
          (K.multiCosetInclude P hadm hgen hret C hCP q) := by
      rw [hpz, hqt]
      exact hp
    obtain ⟨u, hu, huPath⟩ := hSlice.mp ⟨w, hw, hpath⟩
    rw [hpz, hqt] at huPath
    exact ⟨u, hu, huPath⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw.mono Finset.inter_subset_left, hp⟩

/-- Fold an alphabet down by a finite list of other alphabets.
Using a list, rather than a finite set, avoids any arbitrary choice
of a total order on alphabets; duplicates and the empty list are
harmless. -/
def taggedIntersectionAlphabet (B : Finset ι) :
    List (Finset ι) → Finset ι
  | [] => B
  | C :: Cs => taggedIntersectionAlphabet (B ∩ C) Cs

/-- Finite-fold intersection theorem: provided z and t lie in the
same component-tagged constituent for every C in Cs, their true
B-connectivity equals true connectivity over the iterated alphabet
B ∩ C₁ ∩ ··· ∩ Cₙ.

Unlike a naked ambient coset intersection claim, both sides are
proved as existences of ACTUAL signed-word EGraph paths. -/
theorem multiCoset_simultaneousTagged_reachable_iff_intersections
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (Cs : List (Finset ι))
    (B : Finset ι)
    (z t : K.MultiCosetVertex P hadm hgen hret)
    (hSame : ∀ C ∈ Cs,
      K.MultiCosetSameTaggedConstituent P hadm hgen hret C z t) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows z w t) ↔
    (∃ w : LabelWord ι,
      LabelWord.Uses (taggedIntersectionAlphabet B Cs) w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows z w t) := by
  induction Cs generalizing B with
  | nil =>
      rfl
  | cons C Cs ih =>
      have hC :
          K.MultiCosetSameTaggedConstituent
            P hadm hgen hret C z t :=
        hSame C (List.mem_cons_self)
      have hTail : ∀ D ∈ Cs,
          K.MultiCosetSameTaggedConstituent
            P hadm hgen hret D z t := by
        intro D hD
        exact hSame D (List.mem_cons_of_mem C hD)
      have hFirst :=
        K.multiCoset_sameTagged_reachable_iff_inter
          P hadm hgen hret B C z t hC
      have hRest :=
        ih (B := B ∩ C) hTail
      exact hFirst.trans hRest

end CayleySubgraphSpec
end ABO
end PSTSEPPA
