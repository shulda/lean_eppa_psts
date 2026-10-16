import PSTSEPPA.ABO.PullbackAttachedCosetSupportTransport
import PSTSEPPA.ABO.KStablePullbackCommonSupportLift

/-!
# Mixed B/C component-tagged support REFLECTION across stable G/H pullbacks

Let Q:G↠H be labelled, stable separately on B and C,
K any genuinely INCOMPLETE H-Cayley A-skeleton, and
L=Q⁻¹(K) its exact old-edge G-pullback.

Let p and q be genuine component-tagged attached full
B- and C-coset vertices of L, NOT ambient group points.
Assume they have the SAME ambient original G-coordinate g,
and their canonically mapped attached H points share a TRUE
component-tagged (B∩C)-support in H (ABO relation (3.10)).

Then p and q ALREADY share one ACTUAL OLD G
(B∩C)-component-tagged support. This is the NONTRIVIAL
reverse direction missing from simple forward transport.

Proof strategy:
* choose genuine OLD B/C-component representatives x,y for p,q;
* choose an OLD H-(B∩C)-component representative z of
  the given H common-support witness;
* exact index equality yields TRUE B/C signed paths
  from Q(x)/Q(y) to z; the H support has ambient value Q(g);
* use certified cross-group common-support lifting to
  produce ONE actual old G point t reached by real B/C
  paths from x/y and satisfying g∈t G[B∩C];
* take the component-tagged G coset point
  r=(componentClass(B∩C,t),g) and prove its image
  under both enlargement maps is EXACTLY p and q.

This proves precisely the same-ambient-G-coordinate
mixed-support reflection used to establish the
G-level multi-CE embedding in corrected Theorem 4.7(ii).
There is NO claim that arbitrary H-supports lift when
p and q do NOT share a G ambient coordinate, nor a
global injection G↠H, nor G-level bridge-freeness.

All source input signed inverse edges, old component tags,
possible nonfaithful/trivial generator values and B∩C=∅
are retained. This is the local quotient-gluing gate; the
next stage is to package it into the ACTUAL full multi-CE
ambient vertex embedding under the correct source geometry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- GENUINE exact intersection-support gluing relation
reflects through a stable quotient Q:G↠H for two
attached points with the SAME original G group coordinate.
Both component tags are retained; stability is required
only for B and C, not the whole group nor B∪C. -/
theorem pullbackQuotient_shareIntersectionSupport_reflect_of_equal_value
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B C : Finset ι)
    (hB : Q.StableAt B) (hC : Q.StableAt C)
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B)
    (q : (K.pullbackQuotient Q).AttachedCosetVertex C)
    (hValue :
      (K.pullbackQuotient Q).attachedValue B p =
        (K.pullbackQuotient Q).attachedValue C q)
    (hShare :
      K.ShareIntersectionSupport B C
        (K.pullbackQuotient_attachedCosetToBase Q B p)
        (K.pullbackQuotient_attachedCosetToBase Q C q)) :
    (K.pullbackQuotient Q).ShareIntersectionSupport B C p q := by
  let L := K.pullbackQuotient Q
  let F := K.pullbackQuotientHom Q
  let g : Γ := p.2.1
  let D : Finset ι := B ∩ C
  obtain ⟨x, hx⟩ :
      ∃ x : L.Vertex, L.componentClass B x = p.1 := by
    induction p.1 using Quotient.inductionOn with
    | h x => exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ :
      ∃ y : L.Vertex, L.componentClass C y = q.1 := by
    induction q.1 using Quotient.inductionOn with
    | h y => exact ⟨y, rfl⟩
  obtain ⟨rH, hrB, hrC⟩ := hShare
  obtain ⟨z, hz⟩ :
      ∃ z : K.Vertex, K.componentClass D z = rH.1 := by
    induction rH.1 using Quotient.inductionOn with
    | h z => exact ⟨z, rfl⟩
  have hIdxB :
      K.pullbackQuotient_componentIndexToBase Q B p.1 =
        K.componentIndexMap D B Finset.inter_subset_left rH.1 :=
    (congrArg (K.attachedIndex B) hrB).symm
  have hIdxC :
      K.pullbackQuotient_componentIndexToBase Q C q.1 =
        K.componentIndexMap D C Finset.inter_subset_right rH.1 :=
    (congrArg (K.attachedIndex C) hrC).symm
  have hFIndexB :
      K.componentClass B (F.onVertex x) =
        K.componentClass B z := by
    calc
      K.componentClass B (F.onVertex x) =
          K.pullbackQuotient_componentIndexToBase Q B
            (L.componentClass B x) := rfl
      _ = K.pullbackQuotient_componentIndexToBase Q B p.1 :=
        congrArg (K.pullbackQuotient_componentIndexToBase Q B) hx
      _ = K.componentIndexMap D B Finset.inter_subset_left rH.1 :=
        hIdxB
      _ = K.componentClass B z := by rw [← hz]; rfl
  have hFIndexC :
      K.componentClass C (F.onVertex y) =
        K.componentClass C z := by
    calc
      K.componentClass C (F.onVertex y) =
          K.pullbackQuotient_componentIndexToBase Q C
            (L.componentClass C y) := rfl
      _ = K.pullbackQuotient_componentIndexToBase Q C q.1 :=
        congrArg (K.pullbackQuotient_componentIndexToBase Q C) hy
      _ = K.componentIndexMap D C Finset.inter_subset_right rH.1 :=
        hIdxC
      _ = K.componentClass C z := by rw [← hz]; rfl
  have hPathB : K.SubalphabetReachable B (F.onVertex x) z :=
    (K.componentClass_eq_iff B (F.onVertex x) z).mp hFIndexB
  have hPathC : K.SubalphabetReachable C (F.onVertex y) z :=
    (K.componentClass_eq_iff C (F.onVertex y) z).mp hFIndexC
  have hgB : g ∈ generatedLeftCoset genΓ B x.1 := by
    have hpCoset : g ∈ L.componentAmbientCoset B p.1 := p.2.2
    rw [← hx] at hpCoset
    exact hpCoset
  have hqValue : g = q.2.1 := hValue
  have hgC : g ∈ generatedLeftCoset genΓ C y.1 := by
    have hqCoset : q.2.1 ∈ L.componentAmbientCoset C (L.componentClass C y) := by
      simpa only [hy] using q.2.2
    change q.2.1 ∈ generatedLeftCoset genΓ C y.1 at hqCoset
    simpa only [hqValue] using hqCoset
  have hrValue : rH.2.1 = Q.hom g := by
    have hv := congrArg (K.attachedValue B) hrB
    change rH.2.1 = Q.hom g at hv
    exact hv
  have hzD : Q.hom g ∈ generatedLeftCoset genΔ D z.1 := by
    have hrCoset : rH.2.1 ∈ K.componentAmbientCoset D (K.componentClass D z) := by
      simpa only [hz] using rH.2.2
    change rH.2.1 ∈ generatedLeftCoset genΔ D z.1 at hrCoset
    simpa only [hrValue] using hrCoset
  obtain ⟨t, htB, htC, htD⟩ :=
    K.pullbackQuotient_commonIntersectionSupport_lift
      Q B C hB hC x y g hgB hgC z hPathB hPathC hzD
  let rG : L.AttachedCosetVertex D :=
    ⟨L.componentClass D t, ⟨g, htD⟩⟩
  refine ⟨rG, ?_, ?_⟩
  · apply L.attachedValue_injective_of_same_index B
    · change L.componentClass B t = p.1
      exact ((L.componentClass_eq_iff B x t).mpr htB).symm.trans hx
    · rfl
  · apply L.attachedValue_injective_of_same_index C
    · change L.componentClass C t = q.1
      exact ((L.componentClass_eq_iff C y t).mpr htC).symm.trans hy
    · exact hqValue

end CayleySubgraphSpec
end ABO
end PSTSEPPA
