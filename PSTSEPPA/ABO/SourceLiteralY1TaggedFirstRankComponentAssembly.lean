import PSTSEPPA.ABO.SourceLiteralY1EveryOldRootProperBridgeReflection
import PSTSEPPA.ABO.RootedMultiCosetAComponentExact
import PSTSEPPA.ABO.SourceLiteralY1AllOldRootComponentsEmbedded

/-!
# Component-tagged global first-rank coordinates

The genuine old G[A] pullback in the first nontrivial corrected ABO
construction can have *several* intrinsically disconnected A-components
even if their vertices have equal ambient G[A] values. Thus the accepted
per-root ambient injections (PR #670) cannot legitimately be promoted
to an untagged global ambient embedding.

There is, however, an exact and useful **tagged** global embedding:
retain the intrinsic old A-component index alongside the finite local
group coordinate. The parent-index theorem says that each fibre of the
first coordinate is precisely a true old+fresh A-connected region;
the accepted per-root embeddings then give injectivity on each fibre.

This is a genuine globally defined function on ALL vertices of the
uncompleted proper-coset extension, not a choice of roots or a disjoint
union of postulated covers. We also record the corresponding relative
proper-B path reflection within a fixed parent-A-component tag, using
the separately verified first-rank theorem at EVERY old root (PR #682).

Neither statement silently identifies different old components,
supplies the higher-rank cluster-common-core induction, or proves
unconditional PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A global coordinate on a tagged multi-coset vertex which retains
its original intrinsic A-component index as well as its ambient
group element. The extra tag is essential: the ambient coordinate
alone need not be globally injective across disconnected old
components. -/
def multiCosetComponentTaggedAmbientValue
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    K.ComponentIndex A × Γ :=
  ((K.multiCosetVertexToParent P hadm hgen hret A
      (fun C hCP => (P.proper C hCP).subset) z).1,
   K.multiCosetAmbientValue P hadm hgen hret z)

/-- Per-original-A-component ambient-coordinate injectivity implies
a GLOBAL embedding once the genuine parent A-component tag is
retained. This uses the exact tagged-parent characterization,
not a false claim that the original skeleton is connected. -/
theorem multiCosetComponentTaggedAmbientValue_injective_of_all_roots
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hRoots : ∀ r : K.Vertex,
      Set.InjOn (K.multiCosetAmbientValue P hadm hgen hret)
        (K.rootedMultiCosetImage P hadm hgen hret r)) :
    Function.Injective
      (K.multiCosetComponentTaggedAmbientValue P hadm hgen hret) := by
  intro u v hEq
  have hIndex :
      (K.multiCosetVertexToParent P hadm hgen hret A
        (fun C hCP => (P.proper C hCP).subset) u).1 =
      (K.multiCosetVertexToParent P hadm hgen hret A
        (fun C hCP => (P.proper C hCP).subset) v).1 :=
    congrArg Prod.fst hEq
  have hValue :
      K.multiCosetAmbientValue P hadm hgen hret u =
      K.multiCosetAmbientValue P hadm hgen hret v :=
    congrArg Prod.snd hEq
  obtain ⟨r, hr⟩ := K.componentClass_surjective A
    ((K.multiCosetVertexToParent P hadm hgen hret A
      (fun C hCP => (P.proper C hCP).subset) u).1)
  have hu : u ∈ K.rootedMultiCosetImage P hadm hgen hret r :=
    (K.rootedMultiCosetImage_iff_parent_A_index
      P hadm hgen hret r u).mpr hr.symm
  have hv : v ∈ K.rootedMultiCosetImage P hadm hgen hret r :=
    (K.rootedMultiCosetImage_iff_parent_A_index
      P hadm hgen hret r v).mpr (hIndex.symm.trans hr.symm)
  exact hRoots r hu hv hValue

/-- Correct global form of relative bridge reflection: if two
genuine proper-coset-extension points have the SAME intrinsic old
A-component tag and their ambient values share a proper B-coset,
then there is a REAL signed B-path. We require the relative
bridge theorem for every old root, but never cross an A-component
boundary merely because ambient coordinates agree. -/
theorem allProperCoset_same_parent_proper_bridge_of_all_roots
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hRoots : ∀ r : K.Vertex,
      K.RootedProperBridgeReflection hadm hgen hret r)
    (B : Finset ι) (hBA : B ⊂ A)
    (u v : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hParent :
      (K.multiCosetVertexToParent (allProperCosetFamily A)
        hadm hgen hret A
        (fun C hCP => ((allProperCosetFamily A).proper C hCP).subset)
        u).1 =
      (K.multiCosetVertexToParent (allProperCosetFamily A)
        hadm hgen hret A
        (fun C hCP => ((allProperCosetFamily A).proper C hCP).subset)
        v).1)
    (hCoset :
      K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret v ∈
        generatedLeftCoset gen B
          (K.multiCosetAmbientValue (allProperCosetFamily A)
            hadm hgen hret u)) :
    ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows u w v := by
  let P := allProperCosetFamily A
  obtain ⟨r, hr⟩ := K.componentClass_surjective A
    ((K.multiCosetVertexToParent P hadm hgen hret A
      (fun C hCP => (P.proper C hCP).subset) u).1)
  have hu : u ∈ K.rootedMultiCosetImage P hadm hgen hret r :=
    (K.rootedMultiCosetImage_iff_parent_A_index
      P hadm hgen hret r u).mpr hr.symm
  have hv : v ∈ K.rootedMultiCosetImage P hadm hgen hret r :=
    (K.rootedMultiCosetImage_iff_parent_A_index
      P hadm hgen hret r v).mpr (hParent.symm.trans hr.symm)
  exact hRoots r B hBA u v hu hv hCoset

end CayleySubgraphSpec

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- First-rank corrected ABO source certificate: ALL original
old+fresh G=T(X₂^all)[A] P_A vertices inject into the product
of their intrinsic old A-component tag and finite local G[A]
coordinate. The tag may NOT be dropped. Every individual old
component is genuinely covered by the original source action. -/
theorem sourceLiteralY1SelectedLocal_componentTaggedAmbient_injective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Injective
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetComponentTaggedAmbientValue
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)) := by
  let K := sourceLiteralY1SelectedLocalGOldPullback
    src dst base A root
  exact K.multiCosetComponentTaggedAmbientValue_injective_of_all_roots
    (allProperCosetFamily A)
    (sourceLiteralY1SelectedLocalGOld_admissible
      src dst base A hcard root)
    (sourceLiteralY1X2AllLocal_isGenerated src dst A)
    (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
    (fun r => sourceLiteralY1SelectedLocal_everyOldRoot_rootedMultiCoset_injOn
      src dst base A hcard root r)

end ABO
end PSTSEPPA
