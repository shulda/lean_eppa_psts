import PSTSEPPA.ABO.Lemma43WholeComponentAmbientFaithful

/-!
# ABO Lemma 4.3: faithful ORIENTED SIGNED edges of one true common-core B-component

The source's final B-cluster identification requires faithfulness
not just on VERTICES of the genuine component-tagged coset extension,
but also on the actual oriented signed B-edges present in that
component. An ambient group Cayley edge is a source point
and a signed label. In the ORIGINAL multiCE, the same signed
source/label pair determines an edge by the verified
EGraph.deterministic theorem.

The accepted common-original-skeleton-anchor argument and
restricted-vertex-faithfulness theorem show that, within ONE
true signed B-component Q with a common quotient core,
equal ambient Cayley source coordinates identify the
original source quotient vertices. Equal ambient Cayley
edges also have equal signed labels, hence the original
multiCE signed edge tokens coincide.

This proves injectivity of the ORIGINAL signed edge-to-Cayley
map restricted to precisely those true B-labelled source
edges whose source is in Q. No old edge completion is made;
formal inverses, loops, and repeated/trivial generators
are handled as actual signed labels. The conclusion
does NOT assert edge-image surjectivity onto the
candidate translated B-cluster; this is still a
separate source Corollary-3.12 proof obligation.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If one ACTUAL quotient core z belongs to all active
original-component-tagged coatom slices meeting one
true B-component Q, then the ambient Cayley edge
map is injective on all ORIGINAL oriented signed
B-edges with REAL source in Q.

The source B-letter restriction selects the exact
intrinsic B-subgraph; the vertex injectivity and
EGraph determinism supply the proof without
inventing any missing original signed edges. -/
theorem allProperCoset_B_component_ambient_signed_edge_injOn_of_common_core
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor z : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        z ∈ K.properCosetTagSlice hadm hgen hret B anchor t) :
    Set.InjOn
      (K.multiCosetEdgeQuotientAmbient
        (allProperCosetFamily A) hadm hgen hret)
      { e : K.MultiCosetEdgeVertexIncidenceQuotient
          (allProperCosetFamily A) hadm hgen hret |
        signedBase
          ((K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).label e) ∈ B ∧
        ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w
              ((K.multiCosetEGraph (allProperCosetFamily A)
                hadm hgen hret).source e) } := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let H := K.multiCosetAmbientHom P hadm hgen hret
  have hV :
      Set.InjOn (K.multiCosetAmbientValue P hadm hgen hret)
        { y : K.MultiCosetVertex P hadm hgen hret |
          ∃ w : LabelWord ι, LabelWord.Uses B w ∧
            G.Follows anchor w y } :=
    K.allProperCoset_B_component_ambient_injOn_of_common_core
      hadm hgen hret B anchor z hAll
  intro e he f hf hef
  have heReach :
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        G.Follows anchor w (G.source e) := he.2
  have hfReach :
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        G.Follows anchor w (G.source f) := hf.2
  have hAmbientSource :
      K.multiCosetAmbientValue P hadm hgen hret (G.source e) =
      K.multiCosetAmbientValue P hadm hgen hret (G.source f) := by
    change H.onVertex (G.source e) =
      H.onVertex (G.source f)
    calc
      H.onVertex (G.source e) =
          (cayleyGraph gen).source (H.onEdge e) :=
        (H.map_source e).symm
      _ = (cayleyGraph gen).source (H.onEdge f) :=
        congrArg (cayleyGraph gen).source hef
      _ = H.onVertex (G.source f) := H.map_source f
  have hSource : G.source e = G.source f :=
    hV heReach hfReach hAmbientSource
  have hLabel : G.label e = G.label f := by
    calc
      G.label e = (cayleyGraph gen).label (H.onEdge e) :=
        (H.map_label e).symm
      _ = (cayleyGraph gen).label (H.onEdge f) :=
        congrArg (cayleyGraph gen).label hef
      _ = G.label f := H.map_label f
  exact G.deterministic hSource hLabel

end CayleySubgraphSpec
end ABO
