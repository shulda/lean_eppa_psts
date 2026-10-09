import PSTSEPPA.ABO.ClusterCayleySkeleton
import PSTSEPPA.ABO.CayleySubgraphFullCosetPaths
import PSTSEPPA.ABO.ComponentIndexMonotonicity

/-!
# Actual C-paths inside the added coset slice of an augmented cluster

The attachment of a full B-coset vG[B] in an augmented cluster
contributes a full (B∩C)-coset zG[B∩C] to any ambient C-coset
that meets it, where z is a common point.

We prove that this intersection is genuinely C-connected in the
augmented graph, using only the actual added B-labelled edge tokens.
This is the connectivity half of the augmented-cluster
component analysis; it does not depend on the old cluster slice
being nonempty or on ambient projection injectivity.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- Every signed (B∩C)-edge of the intersection coset lies literally
in the augmented cluster. Source-in-coset and signed-label restrictions
are checked separately, including C=∅ and nested parameters. -/
theorem augmented_intersectionCoset_edge_mem
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C u)
    (e : ActionEdge Γ ι)
    (he : e ∈ FullCosetEdgeSet gen (B ∩ C) z) :
    e ∈ (P.augmentedCayleySubgraph gen B hBA v).edges := by
  have hcoset :=
    generatedLeftCoset_inter gen hgen hret B C v u z hzB hzC
  have hs :
      (cayleyGraph gen).source e ∈
        generatedLeftCoset gen B v ∩
          generatedLeftCoset gen C u := by
    rw [hcoset]
    exact he.1
  exact Or.inr ⟨hs.1, Finset.inter_subset_left he.2⟩

/-- Two vertices in the attached (B∩C)-coset are joined by a
realised C-labelled path of the augmented Cayley skeleton.
In fact the constructed word only uses B∩C. -/
theorem augmented_intersectionCoset_reachable
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (C : Finset ι) (u z : Γ)
    (hzB : z ∈ generatedLeftCoset gen B v)
    (hzC : z ∈ generatedLeftCoset gen C u)
    (x y : (P.augmentedCayleySubgraph gen B hBA v).Vertex)
    (hx : x.1 ∈ generatedLeftCoset gen (B ∩ C) z)
    (hy : y.1 ∈ generatedLeftCoset gen (B ∩ C) z) :
    (P.augmentedCayleySubgraph gen B hBA v).SubalphabetReachable
      C x y := by
  let K := P.augmentedCayleySubgraph gen B hBA v
  have hfull :
      ∀ e : ActionEdge Γ ι,
        e ∈ FullCosetEdgeSet gen (B ∩ C) z → e ∈ K.edges := by
    intro e he
    exact P.augmented_intersectionCoset_edge_mem
      gen hgen hret B hBA v C u z hzB hzC e he
  have hr :=
    K.reachable_in_fullCoset (B ∩ C) z hfull x y hx hy
  exact K.subalphabetReachable_mono
    (B ∩ C) C Finset.inter_subset_right hr

/-- In particular, the entire attached B-coset is genuinely
B-connected inside the augmented cluster, without needing
retractability or any nonempty old cluster. -/
theorem augmented_attachedCoset_reachable
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (hBA : B ⊆ A) (v : Γ)
    (x y : (P.augmentedCayleySubgraph gen B hBA v).Vertex)
    (hx : x.1 ∈ generatedLeftCoset gen B v)
    (hy : y.1 ∈ generatedLeftCoset gen B v) :
    (P.augmentedCayleySubgraph gen B hBA v).SubalphabetReachable
      B x y := by
  let K := P.augmentedCayleySubgraph gen B hBA v
  exact K.reachable_in_fullCoset B v
    (fun e he => Or.inr he) x y hx hy

end ClusterSpec
end ABO
end PSTSEPPA
