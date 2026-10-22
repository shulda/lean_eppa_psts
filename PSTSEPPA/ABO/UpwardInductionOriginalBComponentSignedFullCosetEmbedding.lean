import PSTSEPPA.ABO.CanonicalSignedTranslatedProperCluster
import PSTSEPPA.ABO.IsolatedCosetGluing
import PSTSEPPA.ABO.TrueSignedBComponentImageGraphIso

/-!
# TRUE original H B-component embeds, on vertices AND signed edges, in full H[B]

The corrected ABO upward Theorem 4.7(iii) nonisolated
proper B-cluster augmentation must use the EXACT original
component-tagged signed B-component, not the globally
non-injective H group-coordinate projection of the whole
coset extension.

The already certified ORIGINAL source forward Theorem 4.5
supplies an isomorphism (vertex- AND oriented edge-token
BIJECTIVE labelled morphism) of a true original signed
B-component with a g-LEFT-TRANSLATED canonical proper
B-cluster formed from selected genuine D⊊B constituents.

Every translated cluster vertex belongs to the SAME
g H[B] coset, and every true cluster signed oriented edge
belongs to the COMPLETE full H[B] coset. We construct the
ACTUAL signed labelled graph inclusion of the canonical
translated proper cluster into that full H[B] coset,
preserving source, formal edge reversal and signed labels,
not merely a map of vertex coordinate sets.

Composing with the actual original H signed cluster
isomorphism yields a genuine labelled morphism from
the original component-tagged old H B-component into
the full H[B] coset. It is INJECTIVE on original vertices
without any global H CE ambient embedding assumption.

This INJECTIVE coordinate map is precisely the missing
mathematical input to the correct entire-component
old+fresh carrier and completed augmentation constructed
in the companion source modules #929/#930. The final
history-selected stage and its G-Cayley cover are still
separate source-specific obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {B : Finset ι}

namespace ClusterSpec

/-- Every ACTUAL original vertex of a translated canonical
proper B-cluster belongs to the SAME genuine left H[B] coset,
because each true selected constituent D is strictly inside B.
No generation or retraction hypothesis on the ambient Γ. -/
theorem rootTranslatedCluster_vertex_mem_fullBCoset
    (gen : ι → Γ) (P : ClusterSpec B) (g : Γ)
    (v : (P.rootTranslatedCayleySubgraph gen g).Vertex) :
    v.1 ∈ generatedLeftCoset gen B g := by
  have hv : g⁻¹ * v.1 ∈ P.VertexSet gen := v.2
  obtain ⟨D, hDP, hD⟩ := hv
  exact generatedSubgroup_mono gen (P.proper D hDP).subset hD

/-- Every ACTUAL directed signed edge token of the g-translated
proper B-cluster occurs as an actual signed full H[B]-coset
edge, not as a fabricated edge of a later completion. -/
theorem rootTranslatedCluster_edge_mem_fullBCoset
    (gen : ι → Γ) (P : ClusterSpec B) (g : Γ)
    (e : (P.rootTranslatedCayleySubgraph gen g).Edge) :
    e.1 ∈ FullCosetEdgeSet gen B g := by
  have he :
      ∃ D ∈ P.pieces,
        g⁻¹ * e.1.1 ∈ generatedSubgroup gen D ∧
        signedBase e.1.2 ∈ D := e.2
  obtain ⟨D, hDP, hsource, hlabel⟩ := he
  refine ⟨?_, ?_⟩
  · exact generatedSubgroup_mono gen (P.proper D hDP).subset hsource
  · exact (P.proper D hDP).subset hlabel

/-- Genuine labelled graph EMBEDDING from the source's canonical
translated proper B-cluster into the literal full H[B] coset.
Original positive/inverse signed edge tokens, sources, targets
and formal inverse edges are all retained. -/
noncomputable def rootTranslatedClusterToFullBCosetHom
    (gen : ι → Γ) (P : ClusterSpec B) (g : Γ) :
    LabelledGraphHom
      ((P.rootTranslatedCayleySubgraph gen g).toEGraph).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph).toLabelledGraph where
  onVertex v := ⟨v.1, P.rootTranslatedCluster_vertex_mem_fullBCoset gen g v⟩
  onEdge e := ⟨e.1, P.rootTranslatedCluster_edge_mem_fullBCoset gen g e⟩
  map_source e := by
    apply Subtype.ext
    rfl
  map_inv e := by
    apply Subtype.ext
    rfl
  map_label e := rfl

/-- The canonical proper B-cluster inclusion in the full coset
is vertex-injective, with NO quotient by ambient group value
outside the single chosen original component. -/
theorem rootTranslatedClusterToFullBCosetHom_vertex_injective
    (gen : ι → Γ) (P : ClusterSpec B) (g : Γ) :
    Function.Injective
      (P.rootTranslatedClusterToFullBCosetHom gen g).onVertex := by
  intro x y h
  apply Subtype.ext
  exact congrArg Subtype.val h

end ClusterSpec

namespace EGraph

/-- The TRUE original old H B-component signed labelled graph
maps into its actual full H[B] coset, provided by the SOURCE
forward canonical proper B-cluster signed isomorphism.
This is the composition of two GENUINE signed graph morphisms,
not an equality of H ambient coordinates for all old tags. -/
noncomputable def originalBComponentToFullBCosetHom
    {V OldEdge : Type*}
    (H : EGraph V OldEdge ι) (B : Finset ι) (anchor : V)
    (gen : ι → Γ) (P : ClusterSpec B) (g : Γ)
    (f : LabelledGraphHom
      (H.BComponentEGraph B anchor).toLabelledGraph
      ((P.rootTranslatedCayleySubgraph gen g).toEGraph).toLabelledGraph) :
    LabelledGraphHom
      (H.BComponentEGraph B anchor).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph).toLabelledGraph :=
  (P.rootTranslatedClusterToFullBCosetHom gen g).comp f

/-- The true ORIGINAL component-tagged H old vertex map to
the full H[B]-coset is INJECTIVE, as a direct consequence
of the forward-source signed canonical-cluster vertex
isomorphism. This is the exact input to the correct
WHOLE-component B-action replacement stage. -/
theorem originalBComponentToFullBCosetHom_vertex_injective
    {V OldEdge : Type*}
    (H : EGraph V OldEdge ι) (B : Finset ι) (anchor : V)
    (gen : ι → Γ) (P : ClusterSpec B) (g : Γ)
    (f : LabelledGraphHom
      (H.BComponentEGraph B anchor).toLabelledGraph
      ((P.rootTranslatedCayleySubgraph gen g).toEGraph).toLabelledGraph)
    (hf : Function.Injective f.onVertex) :
    Function.Injective
      (H.originalBComponentToFullBCosetHom B anchor gen P g f).onVertex := by
  intro u v h
  apply hf
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  change (f.onVertex u).1 = (f.onVertex v).1 at hval
  exact hval

end EGraph
end ABO
end PSTSEPPA
