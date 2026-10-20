import PSTSEPPA.ABO.ComponentSubgraphAdmissibility
import PSTSEPPA.ABO.ForwardInductionLocalSignedPathReflection
import PSTSEPPA.ABO.LocalSubgroupCosetNaturality

/-!
# ABO Theorem 4.5: source admissibility actually passes to normalized H[C]

The source forward induction needs the genuine rooted C-component's
local signed OLD skeleton over H[C] to satisfy Definition 3.16.
It is not enough that the ORIGINAL C-component over the ambient
group Γ is admissible: the coset predicates are computed in two
DIFFERENT groups, and the source only assumes bounded retractability.

This file removes that missing assumption.  If the original incomplete
A-labelled Γ-Cayley skeleton is admissible, then for EACH C ⊆ A,
including C=A, its TRUE original rooted signed C-component remains
admissible, and its normalized H[C] skeleton is admissible as well.

The proof does not silently replace a genuine old edge by a complete
Cayley edge.  It uses actual path lifting into the rooted old
component, the bijection on original/local directed signed old
edge tokens, and the exact equality of local and ambient proper
D-cosets under inclusion H[C] ↪ Γ.  It works with repeated or
trivial generators and does not require global Γ-retractability.

This is the source geometry needed to discharge the explicit local
admissibility premise of the arbitrary-rank completed signed EGraph
normalization; bridge freeness remains a separate obligation.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Strengthen the already proved strict-lower-component admissibility:
for ANY C⊆A (also C=A), each literal rooted old C-component
inherits the original skeleton's admissibility.  The ambient
C-component is a genuine signed-edge SUBGRAPH, not a coset. -/
theorem subalphabetComponentSubgraph_admissible_of_subset
    (hadm : K.AdmissibleForCosetExtension)
    (C : Finset ι) (hCA : C ⊆ A) (root : K.Vertex) :
    (K.subalphabetComponentSubgraph C root).AdmissibleForCosetExtension := by
  intro D D₁ D₂ hDC hD₁ hD₂ x y hxy hcoset
  let ix : K.Vertex :=
    (K.subalphabetComponentSubgraphHom C root).onVertex x
  let iy : K.Vertex :=
    (K.subalphabetComponentSubgraphHom C root).onVertex y
  have hxRoot : K.SubalphabetReachable C root ix :=
    K.componentSubgraph_vertex_reachable C root x
  have hyRoot : K.SubalphabetReachable C root iy :=
    K.componentSubgraph_vertex_reachable C root y
  obtain ⟨w, hw, hp⟩ := hxy
  have hparent : K.SubalphabetReachable D ix iy :=
    ⟨w, hw, hp.map (K.subalphabetComponentSubgraphHom C root)⟩
  have hDA : D ⊂ A := lt_of_lt_of_le hDC hCA
  have hparentCoset :
      (generatedLeftCoset gen D₁ ix.1 ∩
        generatedLeftCoset gen D₂ iy.1).Nonempty :=
    hcoset
  obtain ⟨z, hxz, hyz⟩ :=
    hadm D D₁ D₂ hDA hD₁ hD₂ ix iy hparent hparentCoset
  have hD₁C : D₁ ⊆ C := hD₁.subset.trans hDC.subset
  have hD₂C : D₂ ⊆ C := hD₂.subset.trans hDC.subset
  have hzRoot : K.SubalphabetReachable C root z :=
    K.subalphabetReachable_trans C hxRoot
      (K.subalphabetReachable_mono D₁ C hD₁C hxz)
  let zSub : (K.subalphabetComponentSubgraph C root).Vertex :=
    K.componentLiftVertex C root z hzRoot
  obtain ⟨hzX, hxzSub⟩ :=
    K.reachable_lift_component C D₁ hD₁C root ix z hxRoot hxz
  obtain ⟨hzY, hyzSub⟩ :=
    K.reachable_lift_component C D₂ hD₂C root iy z hyRoot hyz
  refine ⟨zSub, ?_, ?_⟩
  · have hStart : K.componentLiftVertex C root ix hxRoot = x := by
      apply Subtype.ext
      rfl
    have hEnd : K.componentLiftVertex C root z hzX = zSub := by
      apply Subtype.ext
      rfl
    rw [hStart, hEnd] at hxzSub
    exact hxzSub
  · have hStart : K.componentLiftVertex C root iy hyRoot = y := by
      apply Subtype.ext
      rfl
    have hEnd : K.componentLiftVertex C root z hzY = zSub := by
      apply Subtype.ext
      rfl
    rw [hStart, hEnd] at hyzSub
    exact hyzSub

/-- Main source-facing missing input: admissibility of the ACTUAL
locally normalized signed H[C]-skeleton follows from admissibility
of the ORIGINAL A-skeleton for every C⊆A, even C=A.

A common local D₁/D₂-coset point is translated by root into a
common ambient Γ-coset point.  The parent admissibility gives
a genuine old vertex witness in the ORIGINAL rooted component;
the signed graph bijection lifts BOTH original witness paths
back into the local H[C]-skeleton.  No global Γ-retractability. -/
theorem intrinsicComponentLocalSlice_admissible_of_parent
    (hadm : K.AdmissibleForCosetExtension)
    (C : Finset ι) (hCA : C ⊆ A) (root : K.Vertex) :
    (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension := by
  let M := K.subalphabetComponentSubgraph C root
  let f := K.intrinsicComponentLocalHom C root
  have hMadm : M.AdmissibleForCosetExtension :=
    K.subalphabetComponentSubgraph_admissible_of_subset hadm C hCA root
  intro D D₁ D₂ hDC hD₁ hD₂ x y hxy hcoset
  have hD₁C : D₁ ⊆ C := hD₁.subset.trans hDC.subset
  have hD₂C : D₂ ⊆ C := hD₂.subset.trans hDC.subset
  have hxyM : M.SubalphabetReachable D (f.onVertex x) (f.onVertex y) :=
    (K.intrinsicComponentLocalHom_reachable_iff
      C D root x y).mpr hxy
  obtain ⟨t, ht₁, ht₂⟩ := hcoset
  have htAmbient₁ :
      (t : Γ) ∈ generatedLeftCoset gen D₁ (x.1 : Γ) :=
    (mem_localGeneratedLeftCoset_iff_ambient
      gen D₁ C hD₁C x.1 t).mp ht₁
  have htAmbient₂ :
      (t : Γ) ∈ generatedLeftCoset gen D₂ (y.1 : Γ) :=
    (mem_localGeneratedLeftCoset_iff_ambient
      gen D₂ C hD₂C y.1 t).mp ht₂
  have htRoot₁ :
      root.1 * (t : Γ) ∈
        generatedLeftCoset gen D₁ (f.onVertex x).1 := by
    change (root.1 * (t : Γ)) ∈
      generatedLeftCoset gen D₁ (root.1 * (x.1 : Γ))
    change (root.1 * (x.1 : Γ))⁻¹ *
      (root.1 * (t : Γ)) ∈ generatedSubgroup gen D₁
    change (x.1 : Γ)⁻¹ * (t : Γ) ∈ generatedSubgroup gen D₁ at htAmbient₁
    simpa [mul_assoc] using htAmbient₁
  have htRoot₂ :
      root.1 * (t : Γ) ∈
        generatedLeftCoset gen D₂ (f.onVertex y).1 := by
    change (root.1 * (t : Γ)) ∈
      generatedLeftCoset gen D₂ (root.1 * (y.1 : Γ))
    change (root.1 * (y.1 : Γ))⁻¹ *
      (root.1 * (t : Γ)) ∈ generatedSubgroup gen D₂
    change (y.1 : Γ)⁻¹ * (t : Γ) ∈ generatedSubgroup gen D₂ at htAmbient₂
    simpa [mul_assoc] using htAmbient₂
  have hCosetM :
      (generatedLeftCoset gen D₁ (f.onVertex x).1 ∩
       generatedLeftCoset gen D₂ (f.onVertex y).1).Nonempty :=
    ⟨root.1 * (t : Γ), htRoot₁, htRoot₂⟩
  obtain ⟨z, hxz, hyz⟩ :=
    hMadm D D₁ D₂ hDC hD₁ hD₂
      (f.onVertex x) (f.onVertex y) hxyM hCosetM
  obtain ⟨zl, hzl⟩ :=
    (K.intrinsicComponentLocalHom_bijective C root).1.2 z
  refine ⟨zl, ?_, ?_⟩
  · apply (K.intrinsicComponentLocalHom_reachable_iff
      C D₁ root x zl).mp
    simpa only [hzl] using hxz
  · apply (K.intrinsicComponentLocalHom_reachable_iff
      C D₂ root y zl).mp
    simpa only [hzl] using hyz

end CayleySubgraphSpec
end ABO
end PSTSEPPA
