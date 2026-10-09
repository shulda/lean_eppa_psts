import PSTSEPPA.ABO.MultiCosetMinimalSupportPaths
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# One universal tagged skeleton anchor for all presentations of a vertex

A vertex of the genuine multi-coset quotient may be represented in
many selected complete C-copies with different alphabet/component tags.
Previous lemmas provide a least supporting tagged point and, for
two chosen presentations, a common skeleton anchor.

Here we prove a simultaneous strengthening: for any ONE quotient
vertex z, there exist ONE least supporting alphabet M, ONE skeleton
vertex x and ONE realised M-labelled path x→z that work for *every*
selected C-presentation of z. In particular, the intrinsic C-component
index of x is exactly the given tag of that presentation, for ALL C
at once, not merely two selected coatoms.

The proof selects the same minimal-support accessibility witness
once and for all, then applies labelled-path confinement inside
each completed C-copy to extract the precise component-index equality.
No global ambient Cayley injectivity or bridge-freeness is used.

This is a *vertexwise simultaneous* common-anchor theorem.
It must NOT be confused with the remaining, much stronger common
core/minimal support for an entire B-component (Definition 3.22).
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every multi-coset quotient vertex z has a SINGLE skeleton anchor x,
a SINGLE least supporting alphabet M and an actual M-word x→z
such that, simultaneously for *every* selected C-tagged presentation
p of z, M⊆C and the intrinsic C-component index of x equals p.1.

Thus for an arbitrary finite family of presentations of the same
vertex, all tagged parent components share one actual skeleton anchor.
No whole-component cluster core is asserted. -/
theorem allProperCosetVertex_universal_tagged_skeleton_anchor
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    ∃ (M : Finset ι)
      (hMP : M ∈ (allProperCosetFamily A).alphabets)
      (x : K.Vertex)
      (w : LabelWord ι),
      LabelWord.Uses M w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            M hMP).onVertex x) w z ∧
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets)
        (p : K.AttachedCosetVertex C),
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP p = z →
          M ⊆ C ∧ K.componentClass C x = p.1 := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨M, hMP, pM, x, w, hMz, hw, hPath, hMin⟩ :=
    K.allProperCosetVertex_minimal_support_accessible
      hadm hgen hret z
  refine ⟨M, hMP, x, w, hw, hPath, ?_⟩
  intro C hCP p hPz
  obtain ⟨hMC, _⟩ := hMin C hCP p hPz
  have hSkeleton :
      (K.skeletonToMultiCosetHom P hadm hgen hret
        M hMP).onVertex x =
      (K.skeletonToMultiCosetHom P hadm hgen hret
        C hCP).onVertex x :=
    K.skeletonToMultiCosetHom_vertex_independent
      P hadm hgen hret M C hMP hCP x
  have hCPath :
      G.Follows
        (K.multiCosetInclude P hadm hgen hret
          C hCP (K.attachedOfSkeletonVertex C x)) w z := by
    rw [← hSkeleton]
    exact hPath
  obtain ⟨q, hqIdx, hqz⟩ :=
    K.multiCoset_selected_B_path_stays_in_coset
      P hadm hgen hret C hCP w (hw.mono hMC)
      (K.attachedOfSkeletonVertex C x) z hCPath
  have hqp : q = p :=
    K.multiCosetInclude_injective P hadm hgen hret C hCP
      (hqz.symm.trans hPz.symm)
  have hTag : K.componentClass C x = p.1 := by
    calc
      K.componentClass C x = q.1 := hqIdx.symm
      _ = p.1 := congrArg Sigma.fst hqp
  exact ⟨hMC, hTag⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
