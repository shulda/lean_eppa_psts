import PSTSEPPA.ABO.TrueSignedBComponentImageGraphIso
import PSTSEPPA.ABO.Lemma43TranslatedLowerClusterGraphSets
import PSTSEPPA.ABO.Lemma43TrueComponentVertexSignedEdgeBijections

/-!
# ABO Lemma 4.3: the true B-component IS a translated lower B-cluster signed graph

This is the exact final GRAPH-THEORETIC consequence of the source
Lemma 4.3 signed component-faithfulness and cluster-image results,
including BOTH orientation-sensitive edge tokens.

For a true B-component Q of the ORIGINAL incomplete old+fresh
tagged full proper coset extension, suppose the accepted
whole-component induction supplies an ORIGINAL quotient core
belonging to every active tagged maximal constituent.
Assume additionally each lower alphabet B∩C is PROPER in B,
as certified in the source's multi-constituent branch.

We construct the ACTUAL target signed deterministic EGraph
whose vertex set is the translated finite proper B-cluster's
true vertex set and whose oriented signed edge tokens are
the translated B-cluster's true signed edge set.

The original incomplete B-component carries precisely its
real B-labelled paths and genuine formal inverse edge tokens.
Its canonical actual signed Cayley morphism to the target
cluster graph is a BIJECTION on vertices AND signed edges
and preserves signed labels, source and formal inverse edges.
This is an honest signed labelled graph ISOMORPHISM, not just
two ambient group set equalities.

Proof: accepted signed B-component image EGraph construction,
exact equalities of its original vertex and signed edge images
with the source translated proper B-cluster, and independently
certified source component vertex/edge injectivity.

This theorem concerns the cluster-shaped multi-constituent case
under its actual common-core and properness hypotheses. The source
still separately requires its rank induction, full-B-coset
alternative, and Theorem-4.5/4.7 applications. No new axiom,
sorry, globally untagged coset map or artificial old edge.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- There IS a true signed EGraph on the exact translated
proper lower B-cluster VERTEX and ORIENTED EDGE sets,
and a labelled morphism from the actual original B-component
to that graph which is bijective on BOTH carriers.

Because the map is already a LabelledGraphHom, it preserves
source, formal inversion, signed labels and hence target,
giving precisely the paper's labelled graph isomorphism
rather than two unrelated set bijections. -/
theorem allProperCoset_B_component_translatedLowerCluster_signedGraphIso
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι)
    (anchor core : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        core ∈ K.properCosetTagSlice hadm hgen hret B anchor t)
    (hProper :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B) :
    ∃ (T : EGraph
          {g : Γ // g ∈
            ClusterSpec.LeftTranslateSet
              (K.multiCosetAmbientValue
                (allProperCosetFamily A) hadm hgen hret core)
              ((K.activeTaggedLowerClusterSpec
                hadm hgen hret B anchor hProper).VertexSet gen)}
          {a : ActionEdge Γ ι // a ∈
            ClusterSpec.LeftTranslateEdgeSet
              (K.multiCosetAmbientValue
                (allProperCosetFamily A) hadm hgen hret core)
              ((K.activeTaggedLowerClusterSpec
                hadm hgen hret B anchor hProper).EdgeSet gen)} ι)
      (f : LabelledGraphHom
        ((K.multiCosetEGraph
          (allProperCosetFamily A) hadm hgen hret).BComponentEGraph
            B anchor).toLabelledGraph
        T.toLabelledGraph),
      Function.Bijective f.onVertex ∧
      Function.Bijective f.onEdge := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let H := (cayleyGraph gen).toEGraph
  let F := K.multiCosetAmbientHom P hadm hgen hret
  obtain ⟨hV, hE⟩ :=
    K.allProperCoset_B_component_vertex_and_signed_edge_images_eq_lower_cluster
      hadm hgen hret hcard B anchor core hAll hProper
  have hv : Set.InjOn F.onVertex
      (G.BComponentVertexSet B anchor) := by
    exact (K.allProperCoset_B_component_ambient_vertex_bijOn
      hadm hgen hret B anchor core hAll).2.1
  have he : Set.InjOn F.onEdge
      (G.BComponentEdgeSet B anchor) := by
    exact (K.allProperCoset_B_component_ambient_signed_edge_bijOn
      hadm hgen hret hcard B anchor core hAll).2.1
  rw [← hV, ← hE]
  exact ⟨G.BComponentImageEGraph H F B anchor,
    G.BComponentImageHom H F B anchor,
    G.BComponentImageHom_bijective H F B anchor hv he⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
