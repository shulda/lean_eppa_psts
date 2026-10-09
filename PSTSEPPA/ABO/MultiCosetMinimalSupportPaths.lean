import PSTSEPPA.ABO.MultiCosetMinimalSupport
import PSTSEPPA.ABO.MultiCosetParentComponentExact

/-!
# Access to skeleton via the least supporting alphabet

ABO §3.3.3 defines a pair (M,m) supporting a vertex of a full
coset extension when an M-labelled path connects it to the
skeleton. The previously formalized minimal tagged support
captures alphabet inclusion and the actual skeleton-component
index. Here we also recover the *realised path* part of that
source-facing definition.

Every vertex of the full proper-subalphabet coset extension has
a unique least tagged support (M,p). A skeleton point in the
underlying M-component of p can be joined to the quotient vertex
by an actual M-labelled path in the multi-coset EGraph.
The least tagged support continues to refine every other
presentation of this vertex.

This is still a singleton statement. Definition 3.22 requires
a considerably stronger uniform minimal support for each entire
off-skeleton component.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The least supporting component-tagged coset point of each
vertex is reached from an original skeleton anchor by a genuine
word using *only its least supporting alphabet*. Other
supporting representations uniquely contain the least tagged
support via the canonical alphabet extension maps. -/
theorem allProperCosetVertex_minimal_support_accessible
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    ∃ (M : Finset ι)
      (hMP : M ∈ (allProperCosetFamily A).alphabets)
      (p : K.AttachedCosetVertex M)
      (x : K.Vertex) (w : LabelWord ι),
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret M hMP p = z ∧
      LabelWord.Uses M w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
        ((K.skeletonToMultiCosetHom
          (allProperCosetFamily A) hadm hgen hret
          M hMP).onVertex x) w z ∧
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets)
        (q : K.AttachedCosetVertex C),
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP q = z →
        ∃ hMC : M ⊆ C,
          K.attachedSubalphabetMap M C hMC p = q := by
  obtain ⟨M, hMP, p, hp, hmin⟩ :=
    K.allProperCosetVertex_exists_minimal_tagged_support
      hadm hgen hret z
  obtain ⟨x, hx⟩ :=
    K.componentClass_surjective M p.1
  obtain ⟨w, hw, hpath⟩ :=
    K.singleCosetEGraph_connected_on_index
      M (K.attachedOfSkeletonVertex M x) p hx
  have hMapped := hpath.map
    (K.singleCosetToMultiHom
      (allProperCosetFamily A) hadm hgen hret M hMP)
  change
    (K.multiCosetEGraph (allProperCosetFamily A)
      hadm hgen hret).Follows
      ((K.skeletonToMultiCosetHom
        (allProperCosetFamily A) hadm hgen hret
        M hMP).onVertex x) w
      (K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret M hMP p) at hMapped
  rw [hp] at hMapped
  exact ⟨M, hMP, p, x, w, hp, hw, hMapped, hmin⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
