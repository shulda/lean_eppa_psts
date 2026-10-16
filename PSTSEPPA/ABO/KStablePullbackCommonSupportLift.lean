import PSTSEPPA.ABO.KStablePullbackComponentGraphEquiv
import PSTSEPPA.ABO.KStableTranslatedCosetEquiv
import PSTSEPPA.ABO.CosetIntersections

/-!
# The common OLD intersection-support witness lifts through stable G/H covers

This is the essential TWO-GROUP geometry behind corrected
Auinger–Bitterlich–Otto Theorem 4.7(ii). Let Q:G↠H be a
generator-preserving group quotient stable on BOTH B and C,
K an arbitrary genuine INCOMPLETE H-Cayley skeleton, and
L=Q⁻¹(K) the actual old-edge G-pullback.

Suppose selected real old vertices x,y of L have a COMMON
ambient group point g in their respective translated
G[B] and G[C] cosets. Suppose the two projected old
H-vertices Q(x),Q(y) can reach a COMMON true old H-vertex
z by signed B and C paths, and Q(g) lies in the exact
translated H[B∩C] coset of z.

Then there EXISTS a single actual old vertex t of L
reachable from x by a TRUE signed B path and from y
by a TRUE signed C path, and its ambient (B∩C)-coset
contains the SAME original group point g.

The construction is essential: the two projected paths
first lift to (a priori different) old G-points t_B,t_C.
The H intersection support identifies z with a point
of Q(g)·H[B∩C]. Lift z inside g·G[B∩C] using
generator-preserving subgroup surjectivity. This unique
group value lies in both x·G[B] and y·G[C], and
B/C-stability forces it to equal BOTH old path endpoints.
Thus the component support is genuine and shared upstairs.

No global group injectivity, retractability, equality
of differently tagged cosets, or fictitious old completion
is assumed. This is the hard local witness-lifting step,
NOT YET the full glued multi-coset quotient embedding:
the latter must connect these old paths with the exact
component-indexed attached-coset maps.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- A common exact OLD signed intersection support of
two H-level B/C-connected root components lifts to
a common old G-level vertex, provided their two
translated full cosets share the original G-point g
and Q is stable separately on B and C.

Crucially, the conclusion includes g ∈ tG[B∩C]:
the old vertex is not merely an abstract common
path endpoint, but a witness for the TRUE ABO
component-tagged gluing relation at group value g. -/
theorem pullbackQuotient_commonIntersectionSupport_lift
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B C : Finset ι)
    (hB : Q.StableAt B) (hC : Q.StableAt C)
    (x y : (K.pullbackQuotient Q).Vertex)
    (g : Γ)
    (hgB : g ∈ generatedLeftCoset genΓ B x.1)
    (hgC : g ∈ generatedLeftCoset genΓ C y.1)
    (z : K.Vertex)
    (hzB : K.SubalphabetReachable B
      ((K.pullbackQuotientHom Q).onVertex x) z)
    (hzC : K.SubalphabetReachable C
      ((K.pullbackQuotientHom Q).onVertex y) z)
    (hzD : Q.hom g ∈ generatedLeftCoset genΔ (B ∩ C) z.1) :
    ∃ t : (K.pullbackQuotient Q).Vertex,
      (K.pullbackQuotient Q).SubalphabetReachable B x t ∧
      (K.pullbackQuotient Q).SubalphabetReachable C y t ∧
      g ∈ generatedLeftCoset genΓ (B ∩ C) t.1 := by
  let L := K.pullbackQuotient Q
  let F := K.pullbackQuotientHom Q
  have hzD' :
      z.1 ∈ generatedLeftCoset genΔ (B ∩ C) (Q.hom g) := by
    have hEq :=
      generatedLeftCoset_eq_of_mem genΔ (B ∩ C) hzD
    rw [← hEq]
    exact self_mem_generatedLeftCoset genΔ (B ∩ C) z.1
  obtain ⟨d, hdD, hdMap⟩ :=
    Q.exists_generatedLeftCoset_preimage (B ∩ C) g z.1 hzD'
  have hdB : d ∈ generatedLeftCoset genΓ B g := by
    change g⁻¹ * d ∈ generatedSubgroup genΓ B
    exact generatedSubgroup_mono genΓ Finset.inter_subset_left hdD
  have hdC : d ∈ generatedLeftCoset genΓ C g := by
    change g⁻¹ * d ∈ generatedSubgroup genΓ C
    exact generatedSubgroup_mono genΓ Finset.inter_subset_right hdD
  have hdInXB : d ∈ generatedLeftCoset genΓ B x.1 := by
    rw [generatedLeftCoset_eq_of_mem genΓ B hgB]
    exact hdB
  have hdInYC : d ∈ generatedLeftCoset genΓ C y.1 := by
    rw [generatedLeftCoset_eq_of_mem genΓ C hgC]
    exact hdC
  obtain ⟨wb, hwb, hpathB⟩ := hzB
  obtain ⟨wc, hwc, hpathC⟩ := hzC
  obtain ⟨tb, htbPath, htbMap⟩ :=
    K.pullbackQuotientHom_follows_lift Q hpathB x rfl
  obtain ⟨tc, htcPath, htcMap⟩ :=
    K.pullbackQuotientHom_follows_lift Q hpathC y rfl
  have htbCoset : tb.1 ∈ generatedLeftCoset genΓ B x.1 :=
    L.subalphabetReachable_implies_coset B x tb
      ⟨wb, hwb, htbPath⟩
  have htcCoset : tc.1 ∈ generatedLeftCoset genΓ C y.1 :=
    L.subalphabetReachable_implies_coset C y tc
      ⟨wc, hwc, htcPath⟩
  have hDtB : d = tb.1 := by
    apply Q.injective_on_generatedLeftCoset_of_stableAt
      B hB x.1 hdInXB htbCoset
    exact hdMap.trans
      (congrArg (fun u : K.Vertex => u.1) htbMap).symm
  have hDtC : d = tc.1 := by
    apply Q.injective_on_generatedLeftCoset_of_stableAt
      C hC y.1 hdInYC htcCoset
    exact hdMap.trans
      (congrArg (fun u : K.Vertex => u.1) htcMap).symm
  have hCommon : tb = tc :=
    Subtype.ext (hDtB.symm.trans hDtC)
  have hgD : g ∈ generatedLeftCoset genΓ (B ∩ C) d := by
    have hEq := generatedLeftCoset_eq_of_mem genΓ (B ∩ C) hdD
    rw [← hEq]
    exact self_mem_generatedLeftCoset genΓ (B ∩ C) g
  refine ⟨tb, ⟨wb, hwb, htbPath⟩, ?_, ?_⟩
  · rw [hCommon]
    exact ⟨wc, hwc, htcPath⟩
  · rw [← hDtB]
    exact hgD

end CayleySubgraphSpec
end ABO
end PSTSEPPA
