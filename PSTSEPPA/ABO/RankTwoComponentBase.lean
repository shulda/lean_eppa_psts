import PSTSEPPA.ABO.MultiCosetSupportSkeletonMeet
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Rank-two base case for the source ABO cluster property

At |A| ≤ 2, distinct proper subalphabets of A cannot share a
letter. In the full proper-alphabet coset extension this has
a strong *graph* consequence: every B-labelled oriented edge
starts in a vertex of an attached full B-coset, hence in a
B-component meeting the skeleton.

Therefore any genuine B-component disjoint from the skeleton
is a singleton. Such a singleton has the already verified
unique least component-tagged support, giving the geometric
part of the rank-two induction base (ABO Proposition 4.4).

No ambient Cayley projection injectivity or bridge freeness
is assumed in these results.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

/-- At rank at most two, any two proper subalphabets with
a shared letter coincide. Includes A of size 0 or 1 vacuously. -/
theorem proper_alphabets_shared_letter_eq_rank_two
    (A B C : Finset ι)
    (hcard : A.card ≤ 2)
    (hBA : B ⊂ A) (hCA : C ⊂ A)
    (s : ι) (hsB : s ∈ B) (hsC : s ∈ C) :
    B = C := by
  classical
  have hBcard : B.card ≤ 1 :=
    Nat.lt_succ_iff.mp
      (lt_of_lt_of_le (Finset.card_lt_card hBA) hcard)
  have hCcard : C.card ≤ 1 :=
    Nat.lt_succ_iff.mp
      (lt_of_lt_of_le (Finset.card_lt_card hCA) hcard)
  have hBs : B = {s} := by
    apply Finset.Subset.antisymm
    · intro t ht
      have hts := (Finset.card_le_one.mp hBcard) t ht s hsB
      simpa using hts
    · exact Finset.singleton_subset_iff.mpr hsB
  have hCs : C = {s} := by
    apply Finset.Subset.antisymm
    · intro t ht
      have hts := (Finset.card_le_one.mp hCcard) t ht s hsC
      simpa using hts
    · exact Finset.singleton_subset_iff.mpr hsC
  exact hBs.trans hCs.symm

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every actual B-labelled oriented edge of the full rank-two
coset-extension E-graph starts in the image of one selected
complete B-coset. Completed edges use the shared-letter
rank-two combinatorics; surviving old skeleton edges are
included using the alphabet-independent skeleton morphism. -/
theorem rank_two_B_edge_source_has_selected_support
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : A.card ≤ 2)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (hB : signedBase
      ((K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).label e) ∈ B) :
    ∃ q : K.AttachedCosetVertex B,
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret B hBP q =
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source e := by
  induction e using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨C, edge⟩
      cases edge with
      | inl old =>
          let x : K.Vertex := (K.toEGraph).source old.1
          refine ⟨K.attachedOfSkeletonVertex B x, ?_⟩
          change
            K.multiCosetInclude (allProperCosetFamily A)
              hadm hgen hret B hBP
              (K.attachedOfSkeletonVertex B x) =
            K.multiCosetInclude (allProperCosetFamily A)
              hadm hgen hret C.1 C.2
              (K.attachedOfSkeletonVertex C.1 x)
          exact K.skeletonToMultiCosetHom_vertex_independent
            (allProperCosetFamily A) hadm hgen hret
            B C.1 hBP C.2 x
      | inr completed =>
          change signedBase completed.2.1 ∈ B at hB
          have hCB : C.1 = B :=
            proper_alphabets_shared_letter_eq_rank_two
              A C.1 B hcard
              ((mem_allProperCosetFamily A C.1).mp C.2)
              ((mem_allProperCosetFamily A B).mp hBP)
              (signedBase completed.2.1) completed.2.2 hB
          rcases C with ⟨D, hDP⟩
          dsimp at hCB
          subst D
          exact ⟨completed.1, rfl⟩

/-- Rank-two off-skeleton B-components have no nontrivial
B-paths: if the chosen starting point is not in any selected
tagged B-coset, each realised B-path from it is empty. -/
theorem rank_two_off_selected_B_component_singleton
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : A.card ≤ 2)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hOff :
      ¬ ∃ q : K.AttachedCosetVertex B,
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret B hBP q = z)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hpath : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w y) :
    y = z := by
  obtain ⟨w, hw, hFollows⟩ := hpath
  cases hFollows with
  | nil _ => rfl
  | @cons _ _ s tail e hsrc hlabel hrest =>
      have hmem :
          signedBase ((K.multiCosetEGraph
            (allProperCosetFamily A) hadm hgen hret).label e) ∈ B := by
        rw [hlabel]
        exact hw.1
      obtain ⟨q, hq⟩ :=
        K.rank_two_B_edge_source_has_selected_support
          hadm hgen hret hcard B hBP e hmem
      apply False.elim (hOff ⟨q, hq.trans hsrc⟩)

/-- Rank at most two: the actual B-component of *every* vertex
is either a selected full tagged B-coset, or a singleton
not containing any B-supported point. The genuine
path-component criterion is part of the statement. -/
theorem rank_two_B_component_full_or_singleton
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : A.card ≤ 2)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    (∃ p : K.AttachedCosetVertex B,
      z = K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret B hBP p ∧
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows z w y) ↔
        ∃ q : K.AttachedCosetVertex B,
          q.1 = p.1 ∧
          y = K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret B hBP q) ∨
    (∀ y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret,
      (∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows z w y) →
      y = z) := by
  by_cases hPresent :
      ∃ p : K.AttachedCosetVertex B,
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret B hBP p = z
  · left
    obtain ⟨p, hp⟩ := hPresent
    refine ⟨p, hp.symm, ?_⟩
    intro y
    rw [← hp]
    exact K.multiCoset_selected_B_component_exact
      (allProperCosetFamily A) hadm hgen hret B hBP p y
  · right
    intro y hy
    exact K.rank_two_off_selected_B_component_singleton
      hadm hgen hret hcard B hBP z hPresent y hy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
