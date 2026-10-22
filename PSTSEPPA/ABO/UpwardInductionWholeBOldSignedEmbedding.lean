import PSTSEPPA.ABO.UpwardInductionWholeBOriginalSignedOldHom

/-!
# Source ABO 4.7(iii): ORIGINAL old H embeds on VERTICES AND directed SIGNED EDGES

The previous source-facing theorem constructs the actual signed
labelled graph morphism i:H_old→T from the ENTIRE original
component-tagged incomplete signed H EGraph into the new
nonisolated whole-B-component augmented complete H-stage.

The corrected original paper needs an actual OLD embedding,
not just a map. We strengthen the constructed map by proving
it INJECTIVE on all old vertices AND all oriented signed old
edge tokens, even when distinct old vertices have equal
ambient H-group coordinates.

Vertex injection follows from the exact replacement carrier
{old outside selected component} ⊕ (full H[B]-coset) and the
restricted selected-component injection derived from the
true forward canonical B-cluster isomorphism.

Directed signed edge-token injection follows from:
* a real labelled graph morphism preserves each original
  edge SOURCE and COMPLETE SIGNED LABEL;
* old vertex injection reflects equality of the original
  sources;
* the original incomplete H graph has deterministic
  signed outgoing edges, even for geometric loops and
  inverse edge tokens.

No artificial old edges, quotient by ambient group
coordinates, no-old-B-root hypothesis or custom axioms.
The correctly based source Cayley(G) cover and historical
stage selection are still required for full upward 4.7.
-/

namespace PSTSEPPA
namespace ABO

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace EGraph

/-- The actual original old-H→whole-B-component
augmented H-stage signed graph morphism is injective
on ALL ORIGINAL old vertices, not only on the selected
B-component. Distinct unrelated original tagged H
vertices with coincident ambient group values remain
different. -/
theorem wholeOriginalBComponentOldSignedHom_vertex_injective
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (cHom : LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph).toLabelledGraph)
    (hcInjective : Function.Injective cHom.onVertex) :
    Function.Injective
      (G.wholeOriginalBComponentOldSignedHom
        hpaired gen B anchor g cHom hcInjective).onVertex :=
  G.originalVertexToFullBReplacement_injective
    gen B anchor g cHom.onVertex hcInjective

/-- The SAME actual ORIGINAL signed H inclusion is also
injective on ALL genuine oriented signed OLD edge tokens,
including both formal orientations of existing geometric
loops and any old outside-B edge crossing the chosen
B-component boundary. No completion-created loop is
misidentified with a true old signed edge. -/
theorem wholeOriginalBComponentOldSignedHom_edge_injective
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (cHom : LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph).toLabelledGraph)
    (hcInjective : Function.Injective cHom.onVertex) :
    Function.Injective
      (G.wholeOriginalBComponentOldSignedHom
        hpaired gen B anchor g cHom hcInjective).onEdge := by
  let T := G.wholeOriginalBComponentAugmentedStage
    hpaired gen B anchor g cHom.onVertex hcInjective
  let F := G.wholeOriginalBComponentOldSignedHom
    hpaired gen B anchor g cHom hcInjective
  intro e d hed
  have hV : Function.Injective F.onVertex :=
    G.wholeOriginalBComponentOldSignedHom_vertex_injective
      hpaired gen B anchor g cHom hcInjective
  have hSource : G.source e = G.source d := by
    apply hV
    calc
      F.onVertex (G.source e) = T.source (F.onEdge e) :=
        (F.map_source e).symm
      _ = T.source (F.onEdge d) := congrArg T.source hed
      _ = F.onVertex (G.source d) := F.map_source d
  have hLabel : G.label e = G.label d := by
    calc
      G.label e = T.label (F.onEdge e) := (F.map_label e).symm
      _ = T.label (F.onEdge d) := congrArg T.label hed
      _ = G.label d := F.map_label d
  exact G.deterministic hSource hLabel

/-- Actual original old H EGraph is embedded in the whole
nonisolated complete B-augmentation on both true old
vertices and BOTH signed directed edge-token carriers. -/
theorem wholeOriginalBComponentOldSignedHom_bijectiveOntoImage
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (cHom : LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph).toLabelledGraph)
    (hcInjective : Function.Injective cHom.onVertex) :
    Function.Injective
      (G.wholeOriginalBComponentOldSignedHom
        hpaired gen B anchor g cHom hcInjective).onVertex ∧
    Function.Injective
      (G.wholeOriginalBComponentOldSignedHom
        hpaired gen B anchor g cHom hcInjective).onEdge :=
  ⟨G.wholeOriginalBComponentOldSignedHom_vertex_injective
      hpaired gen B anchor g cHom hcInjective,
    G.wholeOriginalBComponentOldSignedHom_edge_injective
      hpaired gen B anchor g cHom hcInjective⟩

end EGraph
end ABO
end PSTSEPPA
