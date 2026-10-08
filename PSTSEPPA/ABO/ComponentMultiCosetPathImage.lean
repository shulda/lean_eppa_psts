import PSTSEPPA.ABO.ComponentMultiCosetRange
import PSTSEPPA.ABO.MultiCosetParentComponentExact

/-!
# Local multi-coset vertices are precisely an intrinsic B-component

For any nonempty family P of proper subalphabets of B, the checked
embedding of the literal skeleton B-component's multi-coset extension
into the global extension has vertex image exactly the intrinsic
B-connected component of the original root's embedded skeleton point.

This is a statement about realised signed B-word paths, and follows
by combining (a) the exact image criterion via parent B-component
indices and (b) the actual B-path characterization of those indices.

It does NOT, by itself, assert edge-surjectivity onto the full
labelled graph induced by the image; original edges outside B can
remain in the global graph. The relevant B-edge correspondence is a
separate possible next gate for the full source-facing ABO Lemma 3.20.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A vertex of the larger multi-CE comes from the local
B-component's extension exactly when it is B-reachable by an
actual path from the embedded original root vertex.

The family must contain some alphabet to select a literal skeleton
inclusion in the sum-of-cosets model; the selected alphabet itself
may be empty. -/
theorem componentMultiCosetVertexMap_range_iff_B_reachable
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (z : K.MultiCosetVertex (P.intoLarger hBA) hadm hgen hret) :
    (∃ x : (K.subalphabetComponentSubgraph B root).MultiCosetVertex
      P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
      hgen hret,
      K.componentMultiCosetVertexMap B hBA root P hadm hgen hret x = z) ↔
    ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (P.intoLarger hBA) hadm hgen hret).Follows
        ((K.skeletonToMultiCosetHom
          (P.intoLarger hBA) hadm hgen hret C hCP).onVertex root)
        w z := by
  let hPsub : ∀ D ∈ (P.intoLarger hBA).alphabets, D ⊆ B :=
    componentFamily_subset_parent B hBA P
  have hroot :
      (K.multiCosetVertexToParent (P.intoLarger hBA) hadm hgen hret B
        hPsub
        ((K.skeletonToMultiCosetHom
          (P.intoLarger hBA) hadm hgen hret C hCP).onVertex root)).1 =
        K.componentClass B root := by
    exact congrArg (K.attachedIndex B)
      (K.multiCosetVertexToParent_skeleton
        (P.intoLarger hBA) hadm hgen hret B hPsub C hCP root)
  have hrange :=
    K.componentMultiCosetVertexMap_range_iff
      B hBA root P hadm hgen hret z
  have hpath :=
    K.multiCosetEGraph_B_reachable_iff_parent_index
      (P.intoLarger hBA) hadm hgen hret B hPsub
      ((K.skeletonToMultiCosetHom
        (P.intoLarger hBA) hadm hgen hret C hCP).onVertex root) z
  constructor
  · intro hin
    have hparent := hrange.mp hin
    exact hpath.mpr (hroot.trans hparent.symm)
  · intro hreach
    have hparent := hpath.mp hreach
    exact hrange.mpr (hparent.symm.trans hroot)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
