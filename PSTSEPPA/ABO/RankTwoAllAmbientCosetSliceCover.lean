import PSTSEPPA.ABO.RankTwoIndexedAmbientStageCover
import PSTSEPPA.ABO.LocalCosetCayleySlice

/-!
# One finite global cover for all rank-two ambient Cayley coset slices

Earlier rank-two assembly theorems (#313/#314) assumed an externally
given family of Cayley skeletons over each local group Γ[A].
The local-coset translation theorem (#315) produces such an ACTUAL
skeleton from any ordinary A-labelled ambient Γ-skeleton K and
any representative g ∈ Γ. The translation is injective on real
vertices and formal signed edges and covers precisely the vertices
of K in the left coset g Γ[A].

This file assembles ALL those slices for EVERY two-letter
alphabet A and EVERY coset representative g, without selecting
coset transversals and without needing global retractability.

For any prescribed A-labelled skeleton K[A], the completed
three-family stages of all translated slices form ONE actual
dependent disjoint action. Its synchronized transition group
surjects generator-preservingly onto the ORIGINAL ambient Γ,
is 1-stable and 2-retractable, and is finite for finite Γ.

This supplies an explicit, uniform source of the local rank-two
skeleton family required at the assembly stage of corrected ABO.
It is deliberately a REDUNDANT finite superfamily indexed by all
g ∈ Γ. We do NOT claim this is exactly the paper's H₁-cover/Z₁
catalogue, nor that it already meets all of the higher-rank
cluster/reflecting-group requirements.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ}

/-- All rank-two subalphabets together with ALL representatives
g ∈ Γ. We do not use a noncanonical transversal of Γ / Γ[A]. -/
abbrev RankTwoAmbientCosetIndex (ι Γ : Type*) [Fintype ι] :=
  {A : Finset ι // A.card = 2} × Γ

/-- The actual dependent family of local Cayley skeletons,
obtained by translating arbitrary given ambient skeletons
K[A] into the generated subgroup Γ[A]. -/
noncomputable abbrev rankTwoAmbientCosetSkeletons
    (K : ∀ a : {A : Finset ι // A.card = 2},
      CayleySubgraphSpec gen a.1) :
    ∀ j : RankTwoAmbientCosetIndex ι Γ,
      CayleySubgraphSpec (trivialCompletionGenerator gen j.1.1) j.1.1 :=
  fun j => (K j.1).leftCosetSlice j.2

/-- One concrete dependent-disjoint completed stage simultaneously
realizing the real THREE-family rank-two stages of EVERY ambient
two-letter coset slice, with all tags intact. -/
noncomputable abbrev rankTwoAllAmbientCosetsStage
    (K : ∀ a : {A : Finset ι // A.card = 2},
      CayleySubgraphSpec gen a.1)
    (hret : KRetractable gen 2) :=
  rankTwoIndexedAmbientStage (gen := gen)
    (fun j : RankTwoAmbientCosetIndex ι Γ => j.1.1)
    (fun j => j.1.2)
    (rankTwoAmbientCosetSkeletons K) hret

/-- This real completed action on all ambient rank-two coset
slices has the full signed singleton-word kernel AGAINST Γ,
even when Γ itself is not globally retractable. -/
theorem rankTwoAllAmbientCosetsStage_rankOne_wordValue_eq_one
    (K : ∀ a : {A : Finset ι // A.card = 2},
      CayleySubgraphSpec gen a.1)
    (hret : KRetractable gen 2)
    (C : Finset ι) (hC : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (rankTwoAllAmbientCosetsStage K hret).wordValue w = 1 := by
  exact rankTwoIndexedAmbientStage_rankOne_wordValue_eq_one
    (gen := gen)
    (fun j : RankTwoAmbientCosetIndex ι Γ => j.1.1)
    (fun j => j.1.2)
    (rankTwoAmbientCosetSkeletons K) hret C hC w hw hval

/-- A real generator-preserving SURJECTIVE group quotient
from the synchronized group of all coset-slice stages
onto the ORIGINAL labelled Γ. -/
noncomputable def rankTwoAllAmbientCosetsCoverQuotient
    (K : ∀ a : {A : Finset ι // A.card = 2},
      CayleySubgraphSpec gen a.1)
    (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    LabelledGroupQuotient
      (SynchronizedProduct.generator gen
        (rankTwoAllAmbientCosetsStage K hret).transitionSubgroupGenerator)
      gen :=
  rankTwoIndexedAmbientCoverQuotient (gen := gen)
    (fun j : RankTwoAmbientCosetIndex ι Γ => j.1.1)
    (fun j => j.1.2)
    (rankTwoAmbientCosetSkeletons K) hret hgen

/-- Every original Γ-relation using at most one label is
reflected by the actual global synchronized cover. -/
theorem rankTwoAllAmbientCosetsCoverQuotient_oneStable
    (K : ∀ a : {A : Finset ι // A.card = 2},
      CayleySubgraphSpec gen a.1)
    (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    (rankTwoAllAmbientCosetsCoverQuotient K hret hgen).KStable 1 := by
  exact rankTwoIndexedAmbientCoverQuotient_oneStable (gen := gen)
    (fun j : RankTwoAmbientCosetIndex ι Γ => j.1.1)
    (fun j => j.1.2)
    (rankTwoAmbientCosetSkeletons K) hret hgen

/-- The actual synchronized group of ALL two-letter coset-slice
stages is two-retractable under merely KRetractable gen 2;
this is corrected ABO R1, not an assumed group property. -/
theorem rankTwoAllAmbientCosetsCover_twoRetractable
    (K : ∀ a : {A : Finset ι // A.card = 2},
      CayleySubgraphSpec gen a.1)
    (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    KRetractable
      (SynchronizedProduct.generator gen
        (rankTwoAllAmbientCosetsStage K hret).transitionSubgroupGenerator)
      2 := by
  exact rankTwoIndexedAmbientCover_twoRetractable (gen := gen)
    (fun j : RankTwoAmbientCosetIndex ι Γ => j.1.1)
    (fun j => j.1.2)
    (rankTwoAmbientCosetSkeletons K) hret hgen

variable [Finite Γ]

/-- Finite Γ and finite alphabet imply finitely many real
rank-two ambient-skeleton coset slices, and therefore
a FINITE generated synchronized group over all of them. -/
theorem finite_rankTwoAllAmbientCosetsCover
    (K : ∀ a : {A : Finset ι // A.card = 2},
      CayleySubgraphSpec gen a.1)
    (hret : KRetractable gen 2) :
    Finite (SynchronizedProduct.stageCover gen
      (rankTwoAllAmbientCosetsStage K hret)) := by
  classical
  letI : Finite (RankTwoAmbientCosetIndex ι Γ) := inferInstance
  exact finite_rankTwoIndexedAmbientCover (gen := gen)
    (fun j : RankTwoAmbientCosetIndex ι Γ => j.1.1)
    (fun j => j.1.2)
    (rankTwoAmbientCosetSkeletons K) hret

/-- Each actual old vertex of any ambient rank-two skeleton
is represented in the local coset-slice constituent rooted
at that very vertex, even if the original graph is incomplete
and the intrinsic component is disconnected from other slices. -/
theorem rankTwoAllAmbientCosets_root_vertex_realized
    (K : ∀ a : {A : Finset ι // A.card = 2},
      CayleySubgraphSpec gen a.1)
    (a : {A : Finset ι // A.card = 2})
    (y : (K a).Vertex) :
    ∃ x : ((K a).leftCosetSlice y.1).Vertex,
      ((K a).leftCosetSliceHom y.1).onVertex x = y := by
  apply ((K a).leftCosetSliceHom_vertex_range_iff y.1 y).2
  exact self_mem_generatedLeftCoset gen a.1 y.1

end ABO
end PSTSEPPA
