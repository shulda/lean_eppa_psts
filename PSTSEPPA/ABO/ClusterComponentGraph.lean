import PSTSEPPA.ABO.ClusterComponents

/-!
# Graph-level subalphabet components of ABO clusters

Corollary 3.12 is a statement about labelled graph components, not merely
their vertex sets.  We therefore record the directed-edge slice as well and
prove the full-coset / lower-cluster dichotomy simultaneously on vertices and
edges.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- B-labelled cluster edges whose source lies in the chosen B-coset. -/
def ComponentEdgeSlice
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) : Set (ActionEdge Γ ι) :=
  {e |
    e ∈ P.EdgeSet gen ∧
    (cayleyGraph gen).source e ∈ generatedLeftCoset gen B v ∧
    signedBase ((cayleyGraph gen).label e) ∈ B}

/-- The directed edges of the full B-coset component. -/
def FullCosetEdgeSet
    (gen : ι → Γ) (B : Finset ι) (v : Γ) :
    Set (ActionEdge Γ ι) :=
  {e |
    (cayleyGraph gen).source e ∈ generatedLeftCoset gen B v ∧
    signedBase ((cayleyGraph gen).label e) ∈ B}

/-- Left translation of an edge set.  Labels are unchanged. -/
def LeftTranslateEdgeSet
    (z : Γ) (S : Set (ActionEdge Γ ι)) :
    Set (ActionEdge Γ ι) :=
  {e | (z⁻¹ * e.1, e.2) ∈ S}

/-- In the full-coset case the edge slice is exactly the full B-coset edge
set. -/
theorem componentEdgeSlice_eq_fullCoset_of_active_superset
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ)
    (hfull :
      ∃ C ∈ P.ActivePieces gen B v, B ⊆ C) :
    P.ComponentEdgeSlice gen B v =
      FullCosetEdgeSet gen B v := by
  ext e
  constructor
  · rintro ⟨_, hs, hl⟩
    exact ⟨hs, hl⟩
  · rintro ⟨hsB, hlB⟩
    rcases hfull with ⟨C, hactive, hBC⟩
    have hinfo := (P.mem_activePieces_iff gen B v C).1 hactive
    rcases hinfo.2 with ⟨y, hyC, hyB⟩
    have hcosetEq :
        generatedLeftCoset gen B v =
          generatedLeftCoset gen B y :=
      generatedLeftCoset_eq_of_mem gen B hyB
    have hsBy :
        (cayleyGraph gen).source e ∈ generatedLeftCoset gen B y := by
      rw [← hcosetEq]
      exact hsB
    have hstepB :
        y⁻¹ * (cayleyGraph gen).source e ∈ generatedSubgroup gen B :=
      hsBy
    have hstepC :
        y⁻¹ * (cayleyGraph gen).source e ∈ generatedSubgroup gen C :=
      generatedSubgroup_mono gen hBC hstepB
    have hsC :
        (cayleyGraph gen).source e ∈ generatedSubgroup gen C := by
      have hmul :=
        (generatedSubgroup gen C).mul_mem hyC hstepC
      simpa [mul_assoc] using hmul
    have hlC :
        signedBase ((cayleyGraph gen).label e) ∈ C :=
      hBC hlB
    exact
      ⟨P.constituent_edge_mem gen hinfo.1 hsC hlC, hsB, hlB⟩

/-- In the proper case the directed-edge slice is the left translate of the
edge set of the lower B-cluster. -/
theorem componentEdgeSlice_eq_lowerCluster
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v z : Γ)
    (hproper :
      ∀ C ∈ P.ActivePieces gen B v, ¬ B ⊆ C)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzPieces :
      ∀ C ∈ P.ActivePieces gen B v,
        z ∈ generatedSubgroup gen C) :
    P.ComponentEdgeSlice gen B v =
      LeftTranslateEdgeSet z
        ((P.lowerSpec gen B v hproper).EdgeSet gen) := by
  ext e
  rcases e with ⟨x, s⟩
  constructor
  · rintro ⟨⟨C, hCP, hxC, hsC⟩, hxB, hsB⟩
    have hactive : C ∈ P.ActivePieces gen B v := by
      apply (P.mem_activePieces_iff gen B v C).2
      exact ⟨hCP, ⟨x, hxC, hxB⟩⟩
    have hinter :=
      P.constituent_inter_coset_eq
        gen hgen hret C B v z (hzPieces C hactive) hzB
    have hxInter :
        x ∈ (generatedSubgroup gen C : Set Γ) ∩
          generatedLeftCoset gen B v :=
      ⟨hxC, hxB⟩
    have hxLower :
        z⁻¹ * x ∈ generatedSubgroup gen (C ∩ B) := by
      have hxCoset :
          x ∈ generatedLeftCoset gen (C ∩ B) z := by
        rw [← hinter]
        exact hxInter
      exact hxCoset
    change
      (z⁻¹ * x, s) ∈
        (P.lowerSpec gen B v hproper).EdgeSet gen
    refine ⟨C ∩ B, ?_, ?_, ?_⟩
    · classical
      exact Finset.mem_image.mpr ⟨C, hactive, rfl⟩
    · exact hxLower
    · exact Finset.mem_inter.mpr ⟨hsC, hsB⟩
  · intro htranslated
    change
      (z⁻¹ * x, s) ∈
        (P.lowerSpec gen B v hproper).EdgeSet gen at htranslated
    rcases htranslated with ⟨D, hD, hxD, hsD⟩
    classical
    rcases Finset.mem_image.mp hD with ⟨C, hactive, rfl⟩
    have hzC := hzPieces C hactive
    have hxCstep :
        z⁻¹ * x ∈ generatedSubgroup gen C :=
      generatedSubgroup_mono gen
        (by
          intro i hi
          exact (Finset.mem_inter.mp hi).1)
        hxD
    have hxC : x ∈ generatedSubgroup gen C := by
      have hmul :=
        (generatedSubgroup gen C).mul_mem hzC hxCstep
      simpa [mul_assoc] using hmul
    have hxBstep :
        z⁻¹ * x ∈ generatedSubgroup gen B :=
      generatedSubgroup_mono gen
        (by
          intro i hi
          exact (Finset.mem_inter.mp hi).2)
        hxD
    have hxBz : x ∈ generatedLeftCoset gen B z := hxBstep
    have hcosetEq :
        generatedLeftCoset gen B v =
          generatedLeftCoset gen B z :=
      generatedLeftCoset_eq_of_mem gen B hzB
    have hxB : x ∈ generatedLeftCoset gen B v := by
      rw [hcosetEq]
      exact hxBz
    have hsC : signedBase s ∈ C :=
      (Finset.mem_inter.mp hsD).1
    have hsB : signedBase s ∈ B :=
      (Finset.mem_inter.mp hsD).2
    have hpiece :=
      (P.mem_activePieces_iff gen B v C).1 hactive |>.1
    exact
      ⟨P.constituent_edge_mem gen hpiece hxC hsC, hxB, hsB⟩

/-- Graph-data form of ABO Corollary 3.12.

A B-component slice of an A-cluster is either the full B-coset graph or,
after left translation, a lower B-cluster.  Both vertex and directed-edge
sets are identified literally. -/
theorem componentGraph_fullCoset_or_lowerCluster
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A) (B : Finset ι) (v : Γ) :
    (P.ComponentSlice gen B v = generatedLeftCoset gen B v ∧
      P.ComponentEdgeSlice gen B v = FullCosetEdgeSet gen B v) ∨
    ∃ z : Γ, ∃ Q : ClusterSpec B,
      P.ComponentSlice gen B v =
          LeftTranslateSet z (Q.VertexSet gen) ∧
      P.ComponentEdgeSlice gen B v =
          LeftTranslateEdgeSet z (Q.EdgeSet gen) := by
  classical
  by_cases hfull :
      ∃ C ∈ P.ActivePieces gen B v, B ⊆ C
  · exact Or.inl
      ⟨P.componentSlice_eq_fullCoset_of_active_superset
          gen hgen hret B v hfull,
        P.componentEdgeSlice_eq_fullCoset_of_active_superset
          gen hgen hret B v hfull⟩
  · have hproper :
        ∀ C ∈ P.ActivePieces gen B v, ¬ B ⊆ C := by
      intro C hC hBC
      exact hfull ⟨C, hC, hBC⟩
    rcases P.activePieces_common_point gen hgen hret B v with
      ⟨z, hzB, hzPieces⟩
    refine Or.inr
      ⟨z, P.lowerSpec gen B v hproper,
        P.componentSlice_eq_lowerCluster
          gen hgen hret B v z hproper hzB hzPieces,
        P.componentEdgeSlice_eq_lowerCluster
          gen hgen hret B v z hproper hzB hzPieces⟩

end ClusterSpec

end ABO
end PSTSEPPA
