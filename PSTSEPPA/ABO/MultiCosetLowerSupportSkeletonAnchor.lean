import PSTSEPPA.ABO.MultiCosetMinimalSupportPaths
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Proper-support boundary vertices have skeleton anchors in the same C-tag

The local first-exit geometry identifies vertices of a tagged
C-constituent which also have genuine smaller D⊊C support.
To continue the higher-rank cluster argument, we need to
connect that lower-support vertex to the *original skeleton*
using only a proper subalphabet of C, without switching C-tags.

A quotient vertex z admits one least tagged support (M,p).
Its minimality forces M⊆D⊊C. The already proved
minimum-support accessibility lemma supplies an actual
M-labelled path from an old skeleton vertex x to z.
Because M⊆C, the path also runs inside the selected complete
C-coset of x, and injectivity of the C-summand inclusion
shows that x has the *same C-component index* as the
original tagged C-point representing z.

This bridge is stronger than mere equality of ambient Cayley
coordinates. It avoids global Cayley injectivity and does not
assume the cluster property or bridge-freeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If z in a selected C-copy is also supported by a proper
D⊊C, then z is accessible by an actual M⊊C word from an
old skeleton anchor x **in the same component-tagged C-copy**.
The least supporting alphabet M is selected, and its exact
component tag is retained across all inclusions. -/
theorem allProperCoset_lower_support_skeleton_anchor_in_C_tag
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C D : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hDP : D ∈ (allProperCosetFamily A).alphabets)
    (hDC : D ⊂ C)
    (pC : K.AttachedCosetVertex C)
    (pD : K.AttachedCosetVertex D)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hCz :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP pC = z)
    (hDz :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret D hDP pD = z) :
    ∃ (M : Finset ι)
      (hMP : M ∈ (allProperCosetFamily A).alphabets)
      (x : K.Vertex)
      (w : LabelWord ι),
      M ⊂ C ∧
      LabelWord.Uses M w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            C hCP).onVertex x) w z ∧
      K.componentClass C x = pC.1 := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨M, hMP, pM, x, w, hMz, hwM, hpathM, hmin⟩ :=
    K.allProperCosetVertex_minimal_support_accessible
      hadm hgen hret z
  obtain ⟨hMD, _⟩ := hmin D hDP pD hDz
  obtain ⟨hMC, _⟩ := hmin C hCP pC hCz
  have hStrict : M ⊂ C := by
    refine ⟨hMD.trans hDC.1, ?_⟩
    intro hCM
    exact hDC.2 (hCM.trans hMD)
  have hskeleton :
      (K.skeletonToMultiCosetHom P
        hadm hgen hret M hMP).onVertex x =
      (K.skeletonToMultiCosetHom P
        hadm hgen hret C hCP).onVertex x :=
    K.skeletonToMultiCosetHom_vertex_independent
      P hadm hgen hret M C hMP hCP x
  have hpathC :
      G.Follows
        ((K.skeletonToMultiCosetHom P
          hadm hgen hret C hCP).onVertex x) w z := by
    rw [← hskeleton]
    exact hpathM
  have hpathC' :
      G.Follows
        (K.multiCosetInclude P hadm hgen hret
          C hCP (K.attachedOfSkeletonVertex C x)) w z :=
    hpathC
  obtain ⟨qC, hqidx, hqz⟩ :=
    K.multiCoset_selected_B_path_stays_in_coset
      P hadm hgen hret C hCP w (hwM.mono hMC)
      (K.attachedOfSkeletonVertex C x) z hpathC'
  have hqp : qC = pC :=
    K.multiCosetInclude_injective
      P hadm hgen hret C hCP
      (hqz.symm.trans hCz.symm)
  have htag : K.componentClass C x = pC.1 := by
    calc
      K.componentClass C x = qC.1 := hqidx.symm
      _ = pC.1 := congrArg Sigma.fst hqp
  exact ⟨M, hMP, x, w, hStrict, hwM, hpathC, htag⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
