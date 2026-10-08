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

/-- Left translate of a vertex set, written in the same convention as our
left subalphabet cosets. -/
def LeftTranslateSet (z : Γ) (S : Set Γ) : Set Γ :=
  {x | z⁻¹ * x ∈ S}

/-- The intersection alphabets of all active constituents. -/
noncomputable def LowerPieces
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) : Finset (Finset ι) := by
  classical
  exact (P.ActivePieces gen B v).image (fun C => C ∩ B)

/-- If no active constituent contains all of B, the active intersection
alphabets form a genuine B-cluster specification. -/
noncomputable def lowerSpec
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (hproper :
      ∀ C ∈ P.ActivePieces gen B v, ¬ B ⊆ C) :
    ClusterSpec B where
  pieces := P.LowerPieces gen B v
  proper := by
    classical
    intro D hD
    rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (Finset.mem_inter.mp hi).2
    · intro hback
      apply hproper C hC
      intro i hiB
      have hiCB : i ∈ C ∩ B := hback hiB
      exact (Finset.mem_inter.mp hiCB).1

/-- If an active constituent contains B, the whole B-coset lies in the
cluster slice. -/
theorem componentSlice_eq_fullCoset_of_active_superset
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ)
    (hfull :
      ∃ C ∈ P.ActivePieces gen B v, B ⊆ C) :
    P.ComponentSlice gen B v =
      generatedLeftCoset gen B v := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxB
    rcases hfull with ⟨C, hactive, hBC⟩
    have hinfo := (P.mem_activePieces_iff gen B v C).1 hactive
    rcases hinfo.2 with ⟨y, hyC, hyB⟩
    have hcosetEq :
        generatedLeftCoset gen B v =
          generatedLeftCoset gen B y :=
      generatedLeftCoset_eq_of_mem gen B hyB
    have hstepB : y⁻¹ * x ∈ generatedSubgroup gen B := by
      have hxBy : x ∈ generatedLeftCoset gen B y := by
        rw [← hcosetEq]
        exact hxB
      exact hxBy
    have hstepC : y⁻¹ * x ∈ generatedSubgroup gen C :=
      generatedSubgroup_mono gen hBC hstepB
    have hxC : x ∈ generatedSubgroup gen C := by
      have hmul :=
        (generatedSubgroup gen C).mul_mem hyC hstepC
      simpa [mul_assoc] using hmul
    exact ⟨⟨C, hinfo.1, hxC⟩, hxB⟩

/-- In the absence of a full-B constituent, the cluster slice is a left
translate of the lower B-cluster formed by the intersection alphabets C ∩ B. -/
theorem componentSlice_eq_lowerCluster
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v z : Γ)
    (hproper :
      ∀ C ∈ P.ActivePieces gen B v, ¬ B ⊆ C)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzPieces :
      ∀ C ∈ P.ActivePieces gen B v,
        z ∈ generatedSubgroup gen C) :
    P.ComponentSlice gen B v =
      LeftTranslateSet z
        ((P.lowerSpec gen B v hproper).VertexSet gen) := by
  rw [P.componentSlice_eq_activeCosets gen hgen hret B v z hzB hzPieces]
  ext x
  constructor
  · rintro ⟨C, hC, hx⟩
    change z⁻¹ * x ∈ (P.lowerSpec gen B v hproper).VertexSet gen
    refine ⟨C ∩ B, ?_, ?_⟩
    · classical
      exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
    · exact hx
  · intro hx
    change z⁻¹ * x ∈ (P.lowerSpec gen B v hproper).VertexSet gen at hx
    rcases hx with ⟨D, hD, hxD⟩
    classical
    rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
    exact ⟨C, hC, hxD⟩

/-- Vertex-set form of ABO Corollary 3.12.

Every B-coset slice of an A-cluster is either the full B-coset, or a left
translate of a lower B-cluster whose constituent alphabets are intersections
C ∩ B.  The statement also handles an empty slice: then the lower cluster may
have no constituents. -/
theorem componentSlice_fullCoset_or_lowerCluster
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ) :
    P.ComponentSlice gen B v = generatedLeftCoset gen B v ∨
      ∃ z : Γ, ∃ Q : ClusterSpec B,
        P.ComponentSlice gen B v =
          LeftTranslateSet z (Q.VertexSet gen) := by
  classical
  by_cases hfull :
      ∃ C ∈ P.ActivePieces gen B v, B ⊆ C
  · exact Or.inl
      (P.componentSlice_eq_fullCoset_of_active_superset
        gen hgen hret B v hfull)
  · have hproper :
        ∀ C ∈ P.ActivePieces gen B v, ¬ B ⊆ C := by
      intro C hC hBC
      exact hfull ⟨C, hC, hBC⟩
    rcases P.activePieces_common_point gen hgen hret B v with
      ⟨z, hzB, hzPieces⟩
    refine Or.inr ⟨z, P.lowerSpec gen B v hproper, ?_⟩
    exact
      P.componentSlice_eq_lowerCluster
        gen hgen hret B v z hproper hzB hzPieces

end ClusterSpec

end ABO
end PSTSEPPA
