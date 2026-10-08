import PSTSEPPA.ABO.ClusterComponentGraph

/-!
# Intersections of subalphabet components of ABO clusters

This file formalizes ABO Corollary 3.13.  The key point is more precise than
the stated classification: whenever the ambient B- and C-cosets meet at z,
the intersection of the corresponding cluster slices is literally the
(B ∩ C)-slice based at z.  The same identity holds for directed edge data.
Corollary 3.12 then supplies the full-coset / lower-cluster classification.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- Vertex-level form of the elementary identity behind ABO Corollary 3.13. -/
theorem componentSlice_inter_eq
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A)
    (B C : Finset ι) (v w z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C w) :
    P.ComponentSlice gen B v ∩ P.ComponentSlice gen C w =
      P.ComponentSlice gen (B ∩ C) z := by
  have hcoset :=
    generatedLeftCoset_inter
      gen hgen hret B C v w z hzB hzC
  ext x
  constructor
  · rintro ⟨⟨hxP, hxB⟩, ⟨_, hxC⟩⟩
    refine ⟨hxP, ?_⟩
    rw [← hcoset]
    exact ⟨hxB, hxC⟩
  · rintro ⟨hxP, hxBC⟩
    have hx :
        x ∈ generatedLeftCoset gen B v ∩
          generatedLeftCoset gen C w := by
      rw [hcoset]
      exact hxBC
    exact ⟨⟨hxP, hx.1⟩, ⟨hxP, hx.2⟩⟩

/-- Directed-edge form of the same intersection identity. -/
theorem componentEdgeSlice_inter_eq
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A)
    (B C : Finset ι) (v w z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C w) :
    P.ComponentEdgeSlice gen B v ∩ P.ComponentEdgeSlice gen C w =
      P.ComponentEdgeSlice gen (B ∩ C) z := by
  have hcoset :=
    generatedLeftCoset_inter
      gen hgen hret B C v w z hzB hzC
  ext e
  constructor
  · rintro ⟨⟨heP, hsB, hlB⟩, ⟨_, hsC, hlC⟩⟩
    refine ⟨heP, ?_, Finset.mem_inter.mpr ⟨hlB, hlC⟩⟩
    rw [← hcoset]
    exact ⟨hsB, hsC⟩
  · rintro ⟨heP, hsBC, hlBC⟩
    have hs :
        (cayleyGraph gen).source e ∈
          generatedLeftCoset gen B v ∩
            generatedLeftCoset gen C w := by
      rw [hcoset]
      exact hsBC
    have hl := Finset.mem_inter.mp hlBC
    exact
      ⟨⟨heP, hs.1, hl.1⟩,
        ⟨heP, hs.2, hl.2⟩⟩

/-- Graph-data form of ABO Corollary 3.13.

If a B-component slice and a C-component slice of an A-cluster meet, their
intersection is exactly one (B ∩ C)-component slice.  Consequently it is
either the full (B ∩ C)-coset or a translated lower (B ∩ C)-cluster, on both
vertices and directed edges. -/
theorem componentGraph_inter_fullCoset_or_lowerCluster
    (gen : ι → Γ) (hgen : IsGenerated gen) (hret : Retractable gen)
    (P : ClusterSpec A)
    (B C : Finset ι) (v w : Γ)
    (hne :
      (P.ComponentSlice gen B v ∩
        P.ComponentSlice gen C w).Nonempty) :
    ∃ z : Γ,
      z ∈ P.ComponentSlice gen B v ∩
        P.ComponentSlice gen C w ∧
      (((P.ComponentSlice gen B v ∩
            P.ComponentSlice gen C w =
          generatedLeftCoset gen (B ∩ C) z) ∧
        (P.ComponentEdgeSlice gen B v ∩
            P.ComponentEdgeSlice gen C w =
          FullCosetEdgeSet gen (B ∩ C) z)) ∨
       ∃ t : Γ, ∃ Q : ClusterSpec (B ∩ C),
        (P.ComponentSlice gen B v ∩
            P.ComponentSlice gen C w =
          LeftTranslateSet t (Q.VertexSet gen)) ∧
        (P.ComponentEdgeSlice gen B v ∩
            P.ComponentEdgeSlice gen C w =
          LeftTranslateEdgeSet t (Q.EdgeSet gen))) := by
  rcases hne with ⟨z, hzB, hzC⟩
  refine ⟨z, ⟨hzB, hzC⟩, ?_⟩
  have hV :=
    P.componentSlice_inter_eq
      gen hgen hret B C v w z hzB.2 hzC.2
  have hE :=
    P.componentEdgeSlice_inter_eq
      gen hgen hret B C v w z hzB.2 hzC.2
  rcases
      P.componentGraph_fullCoset_or_lowerCluster
        gen hgen hret (B ∩ C) z with hfull | hlower
  · exact Or.inl ⟨hV.trans hfull.1, hE.trans hfull.2⟩
  · rcases hlower with ⟨t, Q, hQV, hQE⟩
    exact Or.inr ⟨t, Q, hV.trans hQV, hE.trans hQE⟩

end ClusterSpec

end ABO
end PSTSEPPA
