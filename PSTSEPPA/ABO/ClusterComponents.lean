import PSTSEPPA.ABO.Cluster
import PSTSEPPA.ABO.ClusterCore

/-!
# Subalphabet slices of clusters

This file isolates the main set-theoretic step behind ABO Corollary 3.12.

For a cluster CL(G[A], P), a subalphabet B, and a left B-coset vG[B],
we identify the cluster slice inside that coset.  The active constituents are
exactly those G[C] meeting the coset.  Retractability supplies one common
basepoint z in all active constituents, and the slice is then the union of the
cosets zG[C ∩ B].
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

@[simp]
theorem generatedLeftCoset_one
    (gen : ι → Γ) (A : Finset ι) :
    generatedLeftCoset gen A (1 : Γ) =
      (generatedSubgroup gen A : Set Γ) := by
  ext x
  simp [generatedLeftCoset]

namespace ClusterSpec

variable {A : Finset ι}

/-- The part of a cluster lying in one ambient B-coset. -/
def ComponentSlice
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) : Set Γ :=
  P.VertexSet gen ∩ generatedLeftCoset gen B v

/-- Constituents which actually meet the chosen B-coset. -/
noncomputable def ActivePieces
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) : Finset (Finset ι) := by
  classical
  exact P.pieces.filter fun C =>
    ((generatedSubgroup gen C : Set Γ) ∩
      generatedLeftCoset gen B v).Nonempty

theorem mem_activePieces_iff
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) (C : Finset ι) :
    C ∈ P.ActivePieces gen B v ↔
      C ∈ P.pieces ∧
      ((generatedSubgroup gen C : Set Γ) ∩
        generatedLeftCoset gen B v).Nonempty := by
  classical
  simp [ActivePieces]

/-- Active constituents admit one common point in the chosen B-coset.  This is
the cluster form of the common-core argument underlying ABO Lemma 3.11. -/
theorem activePieces_common_point
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ) :
    ∃ z : Γ,
      z ∈ generatedLeftCoset gen B v ∧
      ∀ C ∈ P.ActivePieces gen B v,
        z ∈ generatedSubgroup gen C := by
  apply subgroup_family_inter_coset_nonempty
    gen hgen hret (P.ActivePieces gen B v) B v
  intro C hC
  exact (P.mem_activePieces_iff gen B v C).1 hC |>.2

/-- Once z lies in both an active constituent and the ambient B-coset,
the constituent/coset intersection is exactly the (C ∩ B)-coset based at z. -/
theorem constituent_inter_coset_eq
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (C B : Finset ι) (v z : Γ)
    (hzC : z ∈ generatedSubgroup gen C)
    (hzB : z ∈ generatedLeftCoset gen B v) :
    (generatedSubgroup gen C : Set Γ) ∩
        generatedLeftCoset gen B v =
      generatedLeftCoset gen (C ∩ B) z := by
  have hzC' : z ∈ generatedLeftCoset gen C (1 : Γ) := by
    simpa [generatedLeftCoset] using hzC
  have h :=
    generatedLeftCoset_inter
      gen hgen hret C B (1 : Γ) v z hzC' hzB
  simpa using h

/-- Exact decomposition of the cluster slice into its active constituent
intersections, all based at the same canonical point z. -/
theorem componentSlice_eq_activeCosets
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzPieces :
      ∀ C ∈ P.ActivePieces gen B v,
        z ∈ generatedSubgroup gen C) :
    P.ComponentSlice gen B v =
      {x : Γ |
        ∃ C ∈ P.ActivePieces gen B v,
          x ∈ generatedLeftCoset gen (C ∩ B) z} := by
  ext x
  constructor
  · rintro ⟨⟨C, hCP, hxC⟩, hxB⟩
    have hactive : C ∈ P.ActivePieces gen B v := by
      apply (P.mem_activePieces_iff gen B v C).2
      exact ⟨hCP, ⟨x, hxC, hxB⟩⟩
    refine ⟨C, hactive, ?_⟩
    have hinter :=
      P.constituent_inter_coset_eq
        gen hgen hret C B v z (hzPieces C hactive) hzB
    rw [← hinter]
    exact ⟨hxC, hxB⟩
  · rintro ⟨C, hactive, hx⟩
    have hinfo :=
      (P.mem_activePieces_iff gen B v C).1 hactive
    have hinter :=
      P.constituent_inter_coset_eq
        gen hgen hret C B v z (hzPieces C hactive) hzB
    have hxinter :
        x ∈ (generatedSubgroup gen C : Set Γ) ∩
          generatedLeftCoset gen B v := by
      rw [hinter]
      exact hx
    exact
      ⟨⟨C, hinfo.1, hxinter.1⟩, hxinter.2⟩

/-- Source-facing form: every cluster/coset slice admits a common basepoint
at which it is the union of the intersection-alphabet cosets. -/
theorem exists_componentSlice_activeCosets
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ) :
    ∃ z : Γ,
      z ∈ generatedLeftCoset gen B v ∧
      P.ComponentSlice gen B v =
        {x : Γ |
          ∃ C ∈ P.ActivePieces gen B v,
            x ∈ generatedLeftCoset gen (C ∩ B) z} := by
  rcases P.activePieces_common_point gen hgen hret B v with
    ⟨z, hzB, hzPieces⟩
  refine ⟨z, hzB, ?_⟩
  exact
    P.componentSlice_eq_activeCosets
      gen hgen hret B v z hzB hzPieces

end ClusterSpec

end ABO
end PSTSEPPA
