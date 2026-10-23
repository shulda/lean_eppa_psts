import PSTSEPPA.ABO.CanonicalSignedTranslatedProperCluster

/-!
# Source forward 4.5: ORIGINAL canonical signed B-component isomorphism
  with exact original ambient coordinates, not just abstract graph isomorphism

The verified original forward theorem constructs a genuine vertex-
and BOTH-oriented-edge-bijective signed graph map from the ONE
true original component-tagged B-component of CE(H,L_H;P_A) to
its root-left-translated canonical proper B-cluster, and the
proof explicitly defines that map by RESTRICTING the ORIGINAL
signed multi-coset ambient morphism to the true B-component.

However the earlier exported statement only retained existence
of some bijective signed graph morphism, hiding its precise
group-coordinate and oriented-edge-token naturality.

For corrected upward Theorem 4.7(iii), these coordinates MATTER:
the original H signed coset-map of a genuinely selected
coatom constituent must have the exact original H
multiCE ambient value. Otherwise comparing the real H
component anchor with a labelled G→H group quotient is
not justified by the weaker abstract isomorphism alone.

Here we EXPOSE the original source's already proved actual
canonical witness again, strengthening its statement with:
  (i) BOTH signed vertex and oriented-edge bijectivity;
  (ii) EVERY original component-tagged old H vertex x maps
       to precisely its ORIGINAL ambient H multiCE value;
  (iii) EVERY original directed signed H B-edge e maps to
        the precise ORIGINAL ambient signed edge projection.
No global ambient map injectivity is asserted; the
injectivity is only on the ONE true source B-component,
certified by the actual common-core hypothesis.

This mathematical source strengthens the interface for
deriving true selected B∩C_i constituent memberships
and correct H/G anchor coordinate agreements in
corrected ABO 4.7(iii), without quotient-tag collapse
or inventing original old signed edges.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Actual signed canonical proper source-B-cluster graph
isomorphism with EXACT original H vertex and signed
oriented-edge coordinate maps. The forward geometry
proved these facts; no arbitrary choice of a non-natural
signed B-component isomorphism is used. -/
theorem allProperCoset_B_component_canonicalTranslatedCluster_signedIso_with_exact_ambient_value
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
      Function.Bijective f.onEdge ∧
      (∀ x, (f.onVertex x).1 =
        (K.multiCosetAmbientHom (allProperCosetFamily A)
          hadm hgen hret).onVertex x.1) ∧
      (∀ e, (f.onEdge e).1 =
        (K.multiCosetAmbientHom (allProperCosetFamily A)
          hadm hgen hret).onEdge e.1) := by
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
  refine ⟨f, ⟨?_,?_⟩, ⟨?_,?_⟩, ?_, ?_⟩
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
  · intro x
    rfl
  · intro e
    rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
