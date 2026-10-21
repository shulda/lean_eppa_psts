import PSTSEPPA.ABO.ProperClusterRootTranslatedSignedIso
import PSTSEPPA.ABO.Lemma43TrueComponentVertexSignedEdgeBijections
import PSTSEPPA.ABO.Lemma43TranslatedLowerClusterGraphSets
import PSTSEPPA.ABO.TrueSignedBComponentImageGraphIso

/-!
# ABO Lemma 4.3: canonical signed proper B-cluster, not arbitrary EGraph

The source accepted proper-B-cluster theorem exhibited some
deterministic signed EGraph T with the correct translated
cluster vertex and oriented edge carriers. The witness
actually comes from the ORIGINAL ambient Cayley morphism,
so its incidence is the canonical Cayley incidence.

We make that stronger source-facing conclusion explicit:
the REAL B-component of the true old/fresh glued extension
is signed-labelled-graph isomorphic to the ACTUAL
g-root-translated proper B-cluster Cayley skeleton, whose
source, formal edge reversal, signed label and target are
the concrete original ambient Γ-Cayley operations.

The proof combines the source actual B-component image
equalities with independently proved injectivity on
B-component vertices and both signed edge tokens, and
uses NO fake old edge, global ambient Cayley embedding,
or identification of distinct old component tags.

It is the canonical-shaped version of the printed
proper-cluster alternative, needed to compose the full
local H[C] cluster-property proof with the root-translation
isomorphism H[C]→Γ from the preceding module.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A genuine labelled-graph isomorphism of the ACTUAL
component-tagged signed B-component with the CANONICAL
g-left-translated proper B-cluster in ambient Γ.

Both actual vertices and oriented signed edge tokens are
bijectively identified, and the morphism preserves
source, formal inverse, full signed label and targets. -/
theorem allProperCoset_B_component_canonicalTranslatedCluster_signedIso
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
    ∃ f : LabelledGraphHom
      (((K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).BComponentEGraph B anchor).toLabelledGraph)
      (((K.activeTaggedLowerClusterSpec
        hadm hgen hret B anchor hProper).rootTranslatedCayleySubgraph
          gen (K.multiCosetAmbientValue
            (allProperCosetFamily A) hadm hgen hret core)).toEGraph.toLabelledGraph),
      Function.Bijective f.onVertex ∧
      Function.Bijective f.onEdge := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let F := K.multiCosetAmbientHom P hadm hgen hret
  let Q := K.activeTaggedLowerClusterSpec hadm hgen hret B anchor hProper
  let g : Γ := K.multiCosetAmbientValue P hadm hgen hret core
  let T := Q.rootTranslatedCayleySubgraph gen g
  obtain ⟨hV, hE⟩ :=
    K.allProperCoset_B_component_vertex_and_signed_edge_images_eq_lower_cluster
      hadm hgen hret hcard B anchor core hAll hProper
  have hInjV : Set.InjOn F.onVertex (G.BComponentVertexSet B anchor) :=
    (K.allProperCoset_B_component_ambient_vertex_bijOn
      hadm hgen hret B anchor core hAll).2.1
  have hInjE : Set.InjOn F.onEdge (G.BComponentEdgeSet B anchor) :=
    (K.allProperCoset_B_component_ambient_signed_edge_bijOn
      hadm hgen hret hcard B anchor core hAll).2.1
  have hvImage (v : {v : K.MultiCosetVertex P hadm hgen hret //
      v ∈ G.BComponentVertexSet B anchor}) :
      F.onVertex v.1 ∈ T.vertices := by
    change F.onVertex v.1 ∈ ClusterSpec.LeftTranslateSet g (Q.VertexSet gen)
    rw [← hV]
    exact ⟨v.1, v.2, rfl⟩
  have heImage (e : {e : K.MultiCosetEdgeVertexIncidenceQuotient
      P hadm hgen hret // e ∈ G.BComponentEdgeSet B anchor}) :
      F.onEdge e.1 ∈ T.edges := by
    change F.onEdge e.1 ∈ ClusterSpec.LeftTranslateEdgeSet g (Q.EdgeSet gen)
    rw [← hE]
    exact ⟨e.1, e.2, rfl⟩
  let f : LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      T.toEGraph.toLabelledGraph := {
    onVertex := fun v => ⟨F.onVertex v.1, hvImage v⟩
    onEdge := fun e => ⟨F.onEdge e.1, heImage e⟩
    map_source e := by
      apply Subtype.ext
      exact F.map_source e.1
    map_inv e := by
      apply Subtype.ext
      exact F.map_inv e.1
    map_label := by
      intro e
      exact F.map_label e.1
  }
  refine ⟨f, ⟨?_,?_⟩, ⟨?_,?_⟩⟩
  · intro x y hxy
    apply Subtype.ext
    exact hInjV x.2 y.2 (congrArg Subtype.val hxy)
  · intro y
    have hy : y.1 ∈
        {z : Γ | ∃ v : K.MultiCosetVertex P hadm hgen hret,
          v ∈ G.BComponentVertexSet B anchor ∧
          F.onVertex v = z} := by
      have hMem := congrArg (fun S : Set Γ => y.1 ∈ S) hV
      exact hMem.symm ▸ y.2
    obtain ⟨x,hx,hxy⟩ := hy
    refine ⟨⟨x,hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  · intro x y hxy
    apply Subtype.ext
    exact hInjE x.2 y.2 (congrArg Subtype.val hxy)
  · intro y
    have hy : y.1 ∈
        {a : ActionEdge Γ ι |
          ∃ e : K.MultiCosetEdgeVertexIncidenceQuotient
            P hadm hgen hret,
            e ∈ G.BComponentEdgeSet B anchor ∧ F.onEdge e = a} := by
      have hMem := congrArg (fun S : Set (ActionEdge Γ ι) => y.1 ∈ S) hE
      exact hMem.symm ▸ y.2
    obtain ⟨e,he,hey⟩ := hy
    refine ⟨⟨e,he⟩, ?_⟩
    apply Subtype.ext
    exact hey

end CayleySubgraphSpec
end ABO
end PSTSEPPA
