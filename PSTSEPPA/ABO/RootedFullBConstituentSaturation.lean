import PSTSEPPA.ABO.RootedMultiCosetAComponentExact
import PSTSEPPA.ABO.SourceLiteralY1RootedBridgeTagObstruction
import PSTSEPPA.ABO.SingleCosetConnectivity
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.ComponentIndexedCosets

/-!
# Saturation of full tagged B-cosets inside a genuinely embedded rooted region

The accepted corrected ABO first-rank theorem gives an INJECTIVE
ambient G[A]-coordinate map on a whole old-root selected full
old+fresh multi-coset region. We prove an important additional
consequence with no augmented-stage hypothesis.

If a TRUE completed B-constituent contains a vertex u of that
selected rooted region, then EVERY other selected vertex v whose
ambient coordinates lie in the same G[B]-coset as u is necessarily
a point of the SAME intrinsically B-component-tagged full
B-constituent. Consequently u and v are connected by an ACTUAL
signed B-word path within the ORIGINAL uncompleted multiCE.

The subtle step is that the new point q of this tagged B-copy
must itself lie in the selected old-root A-component. The
certified exact parent-A-index characterisation of #648
supplies this, and the certified rooted ambient injectivity of
#646 identifies q with the proposed v. Neither ambient
group-coordinate equality across different tags nor global
pullback connectedness is assumed.

Thus no external proper-B bridge can have its START in an
already completed selected full B-constituent.

For |A| <= 2, the rank-two dichotomy of #647 yields a SHARPER
exact reduction: rooted proper-B bridge reflection is equivalent
to the sole assertion that an OFF-B vertex u has an ambient
G[B]-coset meeting the selected A-component only in u itself.
This does NOT establish that remaining off-B isolation;
it isolates the precise part to be controlled by the source
type-(2) augmented full B-coset stages.

Signed edges, true old/fresh tags, and actual path components
are preserved throughout. Theorem 4.7(iii), its separate R8
full-B-coset repair, higher stages and PSTS EPPA remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If an actual point g lies inside an intrinsically
component-tagged B-coset, its underlying ambient coset is
EXACTLY gG[B], even if other intrinsic B-components may
occupy the same group coset with distinct tags. -/
theorem componentAmbientCoset_eq_generatedLeftCoset_of_member
    (B : Finset ι)
    (c : K.ComponentIndex B)
    (g : Γ)
    (hg : g ∈ K.componentAmbientCoset B c) :
    K.componentAmbientCoset B c = generatedLeftCoset gen B g := by
  induction c using Quotient.inductionOn with
  | h x =>
      change g ∈ generatedLeftCoset gen B x.1 at hg
      change generatedLeftCoset gen B x.1 =
        generatedLeftCoset gen B g
      exact generatedLeftCoset_eq_of_mem gen B hg

/-- Under injectivity on ONE selected old-root A-component,
the full B-constituent is saturated inside that rooted region
with respect to its underlying ambient B-coset.

An arbitrary selected v sharing the ambient B-coset of a
tagged p has a matching point q WITH THE SAME B-COMPONENT
TAG, and the genuine quotient vertices are exactly equal.
The ambient map is NEVER assumed injective elsewhere. -/
theorem rootedMultiCoset_full_B_constituent_saturated
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex)
    (hInj : Set.InjOn
      (K.multiCosetAmbientValue P hadm hgen hret)
      (K.rootedMultiCosetImage P hadm hgen hret root))
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : K.AttachedCosetVertex B)
    (hp : K.multiCosetInclude P hadm hgen hret B hBP p ∈
      K.rootedMultiCosetImage P hadm hgen hret root)
    (v : K.MultiCosetVertex P hadm hgen hret)
    (hv : v ∈ K.rootedMultiCosetImage P hadm hgen hret root)
    (hvB :
      K.multiCosetAmbientValue P hadm hgen hret v ∈
        generatedLeftCoset gen B (K.attachedValue B p)) :
    ∃ q : K.AttachedCosetVertex B,
      q.1 = p.1 ∧
      K.multiCosetInclude P hadm hgen hret B hBP q = v := by
  let hBA : B ⊆ A := (P.proper B hBP).subset
  let g : Γ := K.multiCosetAmbientValue P hadm hgen hret v
  have hgB : g ∈ K.componentAmbientCoset B p.1 := by
    have hSameCoset :=
      K.componentAmbientCoset_eq_generatedLeftCoset_of_member
        B p.1 p.2.1 p.2.2
    rw [hSameCoset]
    exact hvB
  let q : K.AttachedCosetVertex B := ⟨p.1, ⟨g, hgB⟩⟩
  have hpParent :
      K.componentIndexMap B A hBA p.1 =
        K.componentClass A root := by
    have h := (K.rootedMultiCosetImage_iff_parent_A_index
      P hadm hgen hret root
      (K.multiCosetInclude P hadm hgen hret B hBP p)).mp hp
    change K.componentIndexMap B A hBA p.1 =
      K.componentClass A root at h
    exact h
  have hqRegion :
      K.multiCosetInclude P hadm hgen hret B hBP q ∈
        K.rootedMultiCosetImage P hadm hgen hret root := by
    apply (K.rootedMultiCosetImage_iff_parent_A_index
      P hadm hgen hret root
      (K.multiCosetInclude P hadm hgen hret B hBP q)).mpr
    change K.componentIndexMap B A hBA q.1 =
      K.componentClass A root
    exact hpParent
  have hValue :
      K.multiCosetAmbientValue P hadm hgen hret
        (K.multiCosetInclude P hadm hgen hret B hBP q) =
      K.multiCosetAmbientValue P hadm hgen hret v := by
    rfl
  refine ⟨q, rfl, ?_⟩
  exact hInj hqRegion hv hValue

/-- A genuine FULL tagged B-constituent endpoint has NO
external B-bridge to another vertex of the same selected
root A-region. This gives a REAL signed B-path in the
original multi-coset EGraph, not just in its completion. -/
theorem rootedMultiCoset_full_B_endpoint_reachable
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex)
    (hInj : Set.InjOn
      (K.multiCosetAmbientValue P hadm hgen hret)
      (K.rootedMultiCosetImage P hadm hgen hret root))
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (u v : K.MultiCosetVertex P hadm hgen hret)
    (hu : u ∈ K.rootedMultiCosetImage P hadm hgen hret root)
    (hv : v ∈ K.rootedMultiCosetImage P hadm hgen hret root)
    (hFull :
      ∃ p : K.AttachedCosetVertex B,
        K.multiCosetInclude P hadm hgen hret B hBP p = u)
    (hCoset :
      K.multiCosetAmbientValue P hadm hgen hret v ∈
        generatedLeftCoset gen B
          (K.multiCosetAmbientValue P hadm hgen hret u)) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows u w v := by
  obtain ⟨p, hp⟩ := hFull
  have hpRegion :
      K.multiCosetInclude P hadm hgen hret B hBP p ∈
        K.rootedMultiCosetImage P hadm hgen hret root := by
    rw [hp]
    exact hu
  have hpCoset :
      K.multiCosetAmbientValue P hadm hgen hret v ∈
        generatedLeftCoset gen B (K.attachedValue B p) := by
    rw [← hp] at hCoset
    simpa only [K.multiCosetAmbientValue_include] using hCoset
  obtain ⟨q, hqp, hqv⟩ :=
    K.rootedMultiCoset_full_B_constituent_saturated
      P hadm hgen hret root hInj B hBP p hpRegion v hv hpCoset
  have hPath :=
    (K.multiCoset_selected_B_component_exact
      P hadm hgen hret B hBP p v).mpr
      ⟨q, hqp.symm, hqv⟩
  simpa only [hp] using hPath

/-- The TRUE remaining off-B orbit obstruction on the
selected old-root component: a selected quotient point u
outside EVERY genuine attached B-constituent cannot have
any other selected quotient point in its ambient G[B]-coset.

This is an explicit PREDICATE to be proved by source type-(2)
augmented B-coset stages; it is NOT assumed to hold. -/
def RootedProperOffBOrbitIsolated
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex) : Prop :=
  ∀ (B : Finset ι) (hBA : B ⊂ A),
    ∀ (u v : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret),
      u ∈ K.rootedMultiCosetImage (allProperCosetFamily A)
        hadm hgen hret root →
      v ∈ K.rootedMultiCosetImage (allProperCosetFamily A)
        hadm hgen hret root →
      (¬ ∃ p : K.AttachedCosetVertex B,
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret B
          ((mem_allProperCosetFamily A B).mpr hBA) p = u) →
      K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret v ∈ generatedLeftCoset gen B
          (K.multiCosetAmbientValue (allProperCosetFamily A)
            hadm hgen hret u) →
      u = v

/-- SHARP rank-two reduction: given the actually certified
rooted ambient embedding, full B-cosets are automatically
saturated, so the COMPLETE remaining proper-B bridge-reflection
obligation is exactly isolation of individual off-B
vertices in their own ambient B-orbits.

For the forward implication use the independently checked
rank-two full-B-coset / off-B isolated singleton
classification; for the converse use genuine signed
B-paths inside each saturated full B-constituent.

This theorem does NOT prove the off-B-orbit predicate. -/
theorem rootedProperBridgeReflection_iff_offBOrbitIsolated
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : A.card ≤ 2)
    (root : K.Vertex)
    (hInj : Set.InjOn
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret)
      (K.rootedMultiCosetImage (allProperCosetFamily A)
        hadm hgen hret root)) :
    K.RootedProperBridgeReflection hadm hgen hret root ↔
      K.RootedProperOffBOrbitIsolated hadm hgen hret root := by
  let P := allProperCosetFamily A
  constructor
  · intro hBridge B hBA u v hu hv hOff hCoset
    have hBP : B ∈ P.alphabets :=
      (mem_allProperCosetFamily A B).mpr hBA
    obtain ⟨w, hw, hpath⟩ :=
      hBridge B hBA u v hu hv hCoset
    have hEq : v = u :=
      K.rank_two_off_selected_B_component_singleton
        hadm hgen hret hcard B hBP u hOff v
          ⟨w, hw, hpath⟩
    exact hEq.symm
  · intro hOff B hBA u v hu hv hCoset
    have hBP : B ∈ P.alphabets :=
      (mem_allProperCosetFamily A B).mpr hBA
    by_cases hFull :
        ∃ p : K.AttachedCosetVertex B,
          K.multiCosetInclude P hadm hgen hret B hBP p = u
    · exact K.rootedMultiCoset_full_B_endpoint_reachable
        P hadm hgen hret root hInj B hBP
        u v hu hv hFull hCoset
    · have hEq : u = v :=
        hOff B hBA u v hu hv hFull hCoset
      subst v
      exact ⟨[], by trivial, EGraph.Follows.nil _⟩

end CayleySubgraphSpec

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- TRUE literal first-rank specialization: for the
genuine G=T(X₂^all)[A] old-root A-component, the entire
proper-B bridge-reflection problem is equivalent to
isolation of its genuine off-B points in their ambient
singleton G[B]-orbits. All full B-constituent endpoints
are ALREADY solved by the accepted rooted ambient
embedding. The empty B case was independently solved
in #647. -/
theorem sourceLiteralY1SelectedLocal_rootedBridgeReflection_iff_offBOrbitIsolated
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).RootedProperBridgeReflection
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root) ↔
    (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).RootedProperOffBOrbitIsolated
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root) := by
  let K := sourceLiteralY1SelectedLocalGOldPullback src dst base A root
  exact K.rootedProperBridgeReflection_iff_offBOrbitIsolated
    (sourceLiteralY1SelectedLocalGOld_admissible
      src dst base A hcard root)
    (sourceLiteralY1X2AllLocal_isGenerated src dst A)
    (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
    hcard.le
    (sourceLiteralY1SelectedLocalGOld_identity
      src dst base A root)
    (sourceLiteralY1SelectedLocal_rootedMultiCoset_injOn
      src dst base A hcard root)

end ABO
end PSTSEPPA
