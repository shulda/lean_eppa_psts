import PSTSEPPA.ABO.MultiCosetOffSkeletonEdgeSupport
import PSTSEPPA.ABO.MultiCosetComponentSupportInvariant

/-!
# Every edge of an off-skeleton B-component belongs to a real patch

The structural difficulty in ABO Definition 3.22 is to describe
*entire* B-components avoiding the original skeleton, rather than
one vertex or one edge in isolation.

The preceding results yield a useful exact intermediate statement:
if the B-component of z misses the old skeleton, then every
B-edge with source at **any** vertex y B-reachable from z is a
completed edge from some selected coset C, with its signed
generator belonging to B∩C.

Thus the whole off-skeleton component is locally assembled from
lower-alphabet (B∩C)-patches. This does not yet imply that these
patches share the common core demanded by the cluster property,
but identifies the precise remaining geometric question.

We use actual paths and tagged quotient edge tokens throughout.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every signed B-edge based anywhere in an entire B-component
disjoint from the embedded skeleton has an exact completed
C-coset presentation labelled in C∩B, for some proper C⊂A. -/
theorem allProperCoset_off_B_component_edges_have_lower_patches
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hOff :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            B hBP).onVertex x) w z)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hzy : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w y)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (heSource :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source e = y)
    (heB :
      signedBase ((K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).label e) ∈ B) :
    ∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (p : K.AttachedCosetVertex C)
      (s : {s : SignedLabel ι // signedBase s ∈ C}),
      signedBase s.1 ∈ C ∩ B ∧
      e = K.multiCosetEdgeInclude
        (allProperCosetFamily A) hadm hgen hret
        C hCP (Sum.inr (p, s)) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  have hyOff :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧ G.Follows
          ((K.skeletonToMultiCosetHom P hadm hgen hret
            B hBP).onVertex x) w y := by
    intro hy
    exact hOff
      ((K.allProperCoset_B_component_skeleton_meeting_iff
        hadm hgen hret B hBP z y hzy).mpr hy)
  have heOff :
      ∀ x : K.Vertex,
        (K.skeletonToMultiCosetHom P
          hadm hgen hret B hBP).onVertex x ≠
          G.source e := by
    intro x hx
    have hxy : G.Follows
        ((K.skeletonToMultiCosetHom
          P hadm hgen hret B hBP).onVertex x) [] y :=
      G.follows_nil_iff.mpr (hx.trans heSource)
    exact hyOff ⟨x, [], LabelWord.uses_nil B, hxy⟩
  exact K.multiCoset_off_skeleton_B_edge_in_intersection_patch
    P hadm hgen hret B hBP B e heB heOff

end CayleySubgraphSpec
end ABO
end PSTSEPPA
