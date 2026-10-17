import PSTSEPPA.ABO.SourceLiteralY1RootedBridgeTagObstruction
import PSTSEPPA.ABO.MultiCosetParentComponentExact
import PSTSEPPA.ABO.MultiCosetSignedParentSupport

/-!
# The genuine selected OLD-root full attached coset region IS an intrinsic A-component

The corrected ABO first-rank source proof already embeds the full
component-tagged old+fresh P_A region selected by ONE original
incomplete old G[A] A-component. We now identify this region with
an intrinsic A-connected component of the ACTUAL multi-coset
signed EGraph, rather than merely using the raw constituent image
definition of the selected region.

The proof uses the independently verified multi-coset fold into
the intrinsic parent A-component index. Every constituent
C⊊A has a canonical A-component parent tag. A glued point
belongs to the selected rooted region IFF this true parent
tag equals the intrinsic old A-component tag of the root.

The already verified parent-index / genuine signed-path equivalence
then identifies that same set with EXACTLY the vertices reached
from the actual old root inside the original old+fresh
multi-coset extension by realised A-labelled words.

Finally the selected region is closed under ALL GENUINE
oriented signed A-edges: source membership implies target
membership. No new edges from legal loop completion or the
ambient Cayley graph are imagined. Distinct parent old A-
components are never identified by ambient G group value.

This turns the previously certified rooted Set.InjOn statement
into an embedding on an honest, A-connected, edge-closed
component, and supplies a clean domain for later B-external
bridge-reflection and corrected ABO 4.7(iii).

No claim that the full G[A] pullback is A-connected, that the
whole multiCE ambient map is injective, or that all external
singleton B bridges have been ruled out.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The ENTIRE root-selected raw old/fresh attached coset
region is exactly one intrinsic A-parent-index fibre.
This statement compares genuine original path components,
not equal ambient G[A] coset coordinates. -/
theorem rootedMultiCosetImage_iff_parent_A_index
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    z ∈ K.rootedMultiCosetImage P hadm hgen hret root ↔
      (K.multiCosetVertexToParent P hadm hgen hret A
        (fun C hCP => (P.proper C hCP).subset) z).1 =
      K.componentClass A root := by
  let hPsub : ∀ C ∈ P.alphabets, C ⊆ A :=
    fun C hCP => (P.proper C hCP).subset
  constructor
  · rintro ⟨⟨⟨C, hCP⟩, p⟩, ⟨x, hIdx, hReach⟩, hEq⟩
    rw [← hEq]
    change K.componentIndexMap C A (hPsub C hCP) p.1 =
      K.componentClass A root
    rw [hIdx, K.componentIndexMap_class]
    exact (K.componentClass_eq_iff A root x).mpr hReach |>.symm
  · intro hParent
    induction z using Quotient.inductionOn with
    | h raw =>
      rcases raw with ⟨⟨C, hCP⟩, p⟩
      change K.componentIndexMap C A (hPsub C hCP) p.1 =
        K.componentClass A root at hParent
      obtain ⟨x, hx⟩ := K.componentClass_surjective C p.1
      have hAClass :
          K.componentClass A x = K.componentClass A root := by
        calc
          K.componentClass A x =
              K.componentIndexMap C A (hPsub C hCP)
                (K.componentClass C x) :=
            (K.componentIndexMap_class C A (hPsub C hCP) x).symm
          _ = K.componentIndexMap C A (hPsub C hCP) p.1 := by
            rw [hx]
          _ = K.componentClass A root := hParent
      have hReach : K.SubalphabetReachable A root x :=
        (K.componentClass_eq_iff A root x).mp hAClass.symm
      change ∃ raw : K.MultiCosetRawVertex P,
        raw ∈ K.rootedAttachedRawSet P root ∧
        K.multiCosetInclude P hadm hgen hret
          raw.1.1 raw.1.2 raw.2 =
          K.multiCosetInclude P hadm hgen hret C hCP p
      exact ⟨⟨⟨C, hCP⟩, p⟩, ⟨x, hx.symm, hReach⟩, rfl⟩

/-- One ROOTED region is precisely the TRUE intrinsic A-component
of its embedded original old root inside the FULL selected
multiCE EGraph. The selected full family need not be connected
globally; every competing old A-component remains separate. -/
theorem rootedMultiCosetImage_iff_A_reachable
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex)
    (C₀ : Finset ι) (hC₀ : C₀ ∈ P.alphabets)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    z ∈ K.rootedMultiCosetImage P hadm hgen hret root ↔
      ∃ w : LabelWord ι, LabelWord.Uses A w ∧
        (K.multiCosetEGraph P hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom P hadm hgen hret
            C₀ hC₀).onVertex root) w z := by
  let hPsub : ∀ C ∈ P.alphabets, C ⊆ A :=
    fun C hCP => (P.proper C hCP).subset
  let G := K.multiCosetEGraph P hadm hgen hret
  let f := K.multiCosetVertexToParent P hadm hgen hret A hPsub
  let x := (K.skeletonToMultiCosetHom P hadm hgen hret C₀ hC₀).onVertex root
  have hRoot : (f x).1 = K.componentClass A root := by
    have h := K.multiCosetVertexToParent_skeleton
      P hadm hgen hret A hPsub C₀ hC₀ root
    exact congrArg (fun y : K.AttachedCosetVertex A => y.1) h
  have hPath := K.multiCosetEGraph_B_reachable_iff_parent_index
    P hadm hgen hret A hPsub x z
  have hMember := K.rootedMultiCosetImage_iff_parent_A_index
    P hadm hgen hret root z
  constructor
  · intro hz
    have hzIdx : (f z).1 = K.componentClass A root :=
      hMember.mp hz
    apply hPath.mpr
    exact hRoot.trans hzIdx.symm
  · intro hpath
    apply hMember.mpr
    have hSame := hPath.mp hpath
    exact hSame.symm.trans hRoot

/-- The selected old-root full attached region is CLOSED under
EVERY ACTUAL signed edge in the original uncompleted
multi-coset EGraph. An artificial stationary completion
edge is never inferred to exist in the original graph. -/
theorem rootedMultiCosetImage_target_mem_of_source_mem
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      P hadm hgen hret)
    (hSource :
      (K.multiCosetEGraph P hadm hgen hret).source e ∈
        K.rootedMultiCosetImage P hadm hgen hret root) :
    (K.multiCosetEGraph P hadm hgen hret).target e ∈
      K.rootedMultiCosetImage P hadm hgen hret root := by
  let G := K.multiCosetEGraph P hadm hgen hret
  let hPsub : ∀ C ∈ P.alphabets, C ⊆ A :=
    fun C hCP => (P.proper C hCP).subset
  let f := K.multiCosetVertexToParent P hadm hgen hret A hPsub
  have hSrcTag : (f (G.source e)).1 = K.componentClass A root :=
    (K.rootedMultiCosetImage_iff_parent_A_index
      P hadm hgen hret root (G.source e)).mp hSource
  have hLabel : signedBase (G.label e) ∈ A :=
    K.multiCosetEGraph_label_mem_parent P hadm hgen hret e
  have hPath : G.Follows (G.source e) [G.label e] (G.target e) :=
    EGraph.Follows.cons e rfl rfl (EGraph.Follows.nil _)
  have hTag :
      (f (G.source e)).1 = (f (G.target e)).1 :=
    K.multiCoset_follows_parent_B_index P hadm hgen hret
      A hPsub hPath ⟨hLabel, by trivial⟩
  exact (K.rootedMultiCosetImage_iff_parent_A_index
    P hadm hgen hret root (G.target e)).mpr
      (hTag.symm.trans hSrcTag)

/-- Consequently ANY TWO points of the selected old-root full
attached region are A-connected by true original/fresh signed
edges, not just by words in the ambient group G[A]. -/
theorem rootedMultiCosetImage_A_connected
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex)
    (C₀ : Finset ι) (hC₀ : C₀ ∈ P.alphabets)
    (u v : K.MultiCosetVertex P hadm hgen hret)
    (hu : u ∈ K.rootedMultiCosetImage P hadm hgen hret root)
    (hv : v ∈ K.rootedMultiCosetImage P hadm hgen hret root) :
    ∃ w : LabelWord ι, LabelWord.Uses A w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows u w v := by
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨p, hp, hpu⟩ :=
    (K.rootedMultiCosetImage_iff_A_reachable
      P hadm hgen hret root C₀ hC₀ u).mp hu
  obtain ⟨q, hq, hpv⟩ :=
    (K.rootedMultiCosetImage_iff_A_reachable
      P hadm hgen hret root C₀ hC₀ v).mp hv
  refine ⟨PSTS.SignedWord.inv p ++ q, ?_, ?_⟩
  · exact (LabelWord.uses_append A _ _).mpr ⟨hp.inv, hq⟩
  · exact G.follows_append (G.follows_inverse hpu) hpv

end CayleySubgraphSpec

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For the true FIRST-RANK literal G=T(X₂^all)→T(Y₁)
source, the selected rooted region of the actual
incomplete G[A] multiCE equals ONE genuine intrinsic
A-connected component of old/fresh signed vertices. -/
theorem sourceLiteralY1SelectedLocal_rootedImage_iff_A_reachable
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (z : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).MultiCosetVertex
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)) :
    z ∈ (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).rootedMultiCosetImage
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root) ↔
      ∃ w : LabelWord ι, LabelWord.Uses A w ∧
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetEGraph
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)).Follows
        (((sourceLiteralY1SelectedLocalGOldPullback
          src dst base A root).skeletonToMultiCosetHom
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
          ∅
          (empty_mem_allProperCosetFamily A
            (Finset.card_pos.mp (by rw [hcard]; decide)))).onVertex
          (sourceLiteralY1SelectedLocalGOld_identity
            src dst base A root)) w z := by
  let K := sourceLiteralY1SelectedLocalGOldPullback src dst base A root
  exact K.rootedMultiCosetImage_iff_A_reachable
    (allProperCosetFamily A)
    (sourceLiteralY1SelectedLocalGOld_admissible src dst base A hcard root)
    (sourceLiteralY1X2AllLocal_isGenerated src dst A)
    (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
    (sourceLiteralY1SelectedLocalGOld_identity src dst base A root)
    ∅
    (empty_mem_allProperCosetFamily A
      (Finset.card_pos.mp (by rw [hcard]; decide)))
    z

end ABO
end PSTSEPPA
