import PSTSEPPA.ABO.SourceOriginalH1Z1ThreeFamilyAction
import PSTSEPPA.ABO.CompleteStageWordCongruenceReachableCover

/-!
# Real finite source G₂ Cayley graph covers of the actual original H₁ Z₁ three-family action

The input-specific rank-one source action is the LITERAL tagged
dependent disjoint family of (0) original plain full proper-coset
completed stages, (1) all original anchored augmented clusters,
and (2) genuine rooted full-B-coset augmentations of original
H₁ preimage components in their proved root-translated presentation.

Its complete signed-word congruence already factors through the
concrete finite sourceAllLocalG2. The group is genuinely generated
by the original input labels. The generic action well-definedness
theorem therefore builds a real LABELLED GRAPH HOMOMORPHISM
  Cayley(G₂, generator) ⟶ original H₁ Z₁ three-family action
based at ANY original tagged stage vertex.

The induced cover hits precisely the reachable completed-stage
component: every vertex and EVERY formal directed signed edge token
of that component, including inverse and legally completed loop
edges. It does NOT assume an ambient H₁ Cayley embedding, choose
component representatives or identify equal ambient coordinates.

The source's exact narrower Definition-5.3 Z₁ index-selection/
exhaustiveness and automorphism-equivariance remain separate
requirements; no general higher-rank reflecting group or PSTS EPPA
is claimed here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The EXACT vertex carrier of the previously constructed
original H₁ three-kind source completed action. All stage tags
and original old/fresh coset vertices remain distinct. -/
abbrev SourceOriginalH1Z1Vertex
    (src dst : ι → V) :=
  Σ j : sourceOriginalH1Z1ThreeFamilyIndex src dst,
    sourceOriginalH1Z1StageVertex src dst j

/-- A genuine signed labelled graph morphism from the Cayley
graph of the actual finite input-dependent group G₂ into the
original H₁ source completed Z₁ three-family action, rooted
at ANY chosen tagged original source stage vertex. -/
noncomputable def sourceOriginalH1Z1G2CayleyHom
    (src dst : ι → V)
    (u : SourceOriginalH1Z1Vertex src dst) :
    LabelledGraphHom
      (cayleyGraph (sourceAllLocalG2Generator src dst)).toEGraph.toLabelledGraph
      (sourceOriginalH1Z1ThreeFamilyStage src dst).toEGraph.toLabelledGraph :=
  (sourceOriginalH1Z1ThreeFamilyStage src dst).cayleyCoverFromWordCongruence
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceOriginalH1Z1ThreeFamily_wordValue_congr src dst)
    u

/-- The concrete G₂ identity maps to the LITERAL original
source basepoint of the chosen completed stage. -/
@[simp] theorem sourceOriginalH1Z1G2CayleyHom_one
    (src dst : ι → V)
    (u : SourceOriginalH1Z1Vertex src dst) :
    (sourceOriginalH1Z1G2CayleyHom src dst u).onVertex 1 = u :=
  (sourceOriginalH1Z1ThreeFamilyStage src dst).cayleyCoverFromWordCongruence_one
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceOriginalH1Z1ThreeFamily_wordValue_congr src dst) u

/-- The genuine finite G₂ Cayley value of any signed chronological
word reaches exactly its actual original H₁ source completed-stage
endpoint, for positive AND inverse labels and legal loop edges. -/
theorem sourceOriginalH1Z1G2CayleyHom_word
    (src dst : ι → V)
    (u : SourceOriginalH1Z1Vertex src dst)
    (w : LabelWord ι) :
    (sourceOriginalH1Z1G2CayleyHom src dst u).onVertex
      (PSTS.SignedWord.evalGroup (sourceAllLocalG2Generator src dst) w) =
    (sourceOriginalH1Z1ThreeFamilyStage src dst).followWord u w :=
  (sourceOriginalH1Z1ThreeFamilyStage src dst).cayleyCoverFromWordCongruence_word
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceOriginalH1Z1ThreeFamily_wordValue_congr src dst) u w

/-- Exact vertex image of the actual based G₂ Cayley cover:
ALL and ONLY signed-word reachable original stage vertices.
No connectedness of the entire disjoint family is postulated. -/
theorem sourceOriginalH1Z1G2CayleyHom_vertex_range
    (src dst : ι → V)
    (u : SourceOriginalH1Z1Vertex src dst) :
    Set.range (sourceOriginalH1Z1G2CayleyHom src dst u).onVertex =
      {v : SourceOriginalH1Z1Vertex src dst |
        (sourceOriginalH1Z1ThreeFamilyStage src dst).Reachable u v} :=
  (sourceOriginalH1Z1ThreeFamilyStage src dst).cayleyCoverFromWordCongruence_vertex_range
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceOriginalH1Z1ThreeFamily_wordValue_congr src dst) u

/-- Exact DIRECTED EDGE TOKEN image of the actual G₂ cover:
all signed edges, including distinct inverse stationary loops,
whose sources lie in the chosen original Z₁ reachable component. -/
theorem sourceOriginalH1Z1G2CayleyHom_edge_range
    (src dst : ι → V)
    (u : SourceOriginalH1Z1Vertex src dst) :
    Set.range (sourceOriginalH1Z1G2CayleyHom src dst u).onEdge =
      {e : ActionEdge (SourceOriginalH1Z1Vertex src dst) ι |
        (sourceOriginalH1Z1ThreeFamilyStage src dst).Reachable u
          ((sourceOriginalH1Z1ThreeFamilyStage src dst).source e)} :=
  (sourceOriginalH1Z1ThreeFamilyStage src dst).cayleyCoverFromWordCongruence_edge_range
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceOriginalH1Z1ThreeFamily_wordValue_congr src dst) u

end ABO
end PSTSEPPA
