import PSTSEPPA.ABO.ComponentMultiCosetEdgeRange
import PSTSEPPA.ABO.ComponentMultiCosetPathImage

/-!
# Full B-labelled graph component represented by the local multi-CE

The multi-coset extension of the intrinsic B-component of K embeds
injectively into the global multi-coset E-graph.

On vertices its image is precisely the intrinsic B-path component
of the embedded root. On signed directed edges, it comprises exactly
those edges whose labels are in B and whose sources are B-reachable
from that root. This is the graph-data strengthening of the earlier
vertex-only component classification.

The statement purposely uses *actual realised paths* and true signed
edge-token equality. It is not an assertion about equal Cayley
coordinates or an unintended induced graph including outside-B edges.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact directed-edge image of the actual B-path component of
an embedded root inside the global multi-coset E-graph.

The chosen family P is nonempty (witnessed by C) solely to
specify the canonical skeleton embedding of root. -/
theorem componentMultiCoset_edge_range_iff_B_component
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex) (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (P.intoLarger hBA) hadm hgen hret) :
    (∃ localEdge :
      (K.subalphabetComponentSubgraph B root).MultiCosetEdgeVertexIncidenceQuotient
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret,
      (K.componentMultiCosetHom B hBA root P hadm hgen hret).onEdge
        localEdge = e) ↔
      (signedBase ((K.multiCosetEGraph (P.intoLarger hBA)
        hadm hgen hret).label e) ∈ B ∧
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (P.intoLarger hBA)
          hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom (P.intoLarger hBA)
            hadm hgen hret C hCP).onVertex root) w
          ((K.multiCosetEGraph (P.intoLarger hBA)
            hadm hgen hret).source e)) := by
  let z := (K.multiCosetEGraph (P.intoLarger hBA)
    hadm hgen hret).source e
  have hv :=
    K.componentMultiCosetVertexMap_range_iff_B_reachable
      B hBA root P hadm hgen hret C hCP z
  have he :=
    K.componentMultiCoset_edge_range_iff
      B hBA root P hadm hgen hret e
  constructor
  · intro hin
    obtain ⟨hlabel, ⟨x, hx⟩⟩ := he.mp hin
    exact ⟨hlabel, hv.mp ⟨x, hx⟩⟩
  · rintro ⟨hlabel, hpath⟩
    obtain ⟨x, hx⟩ := hv.mpr hpath
    exact he.mpr ⟨hlabel, ⟨x, hx⟩⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
