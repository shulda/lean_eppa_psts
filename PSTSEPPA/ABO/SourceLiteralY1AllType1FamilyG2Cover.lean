import PSTSEPPA.ABO.SourceLiteralY1Type1ExactIndexEquiv
import PSTSEPPA.ABO.SourceLiteralY1Type1G2CayleyCover
import PSTSEPPA.ABO.DependentDisjointWordCongruence
import PSTSEPPA.ABO.CompleteStageWordCongruenceReachableCover

/-!
# The ENTIRE anchored type-(1) literal paper T(Y₁) finite Z₁ stage family

The corrected ABO first-rank type-(1) stages comprise EVERY
anchored augmented cluster of genuine strictly proper
subalphabet subgroup pieces in the literal generated group
T(Y₁), for each actual |A|=2, cluster P, proper B⊊A,
and old anchor v IN that cluster.

The full dependent index family was certified finite and in
exact bijection with the original SourceH₁ stage index family.
For each actual indexed fibre, the TRUE legally completed
old+fresh signed augmented action has already been shown
vertex/edge-bijectively isomorphic to the real source-H₁
action and controlled by the CONCRETE finite input-derived G₂.

Here we assemble every such genuine printed action on a
single DEPENDENT disjoint union indexed by the ACTUAL paper
(A,P,B,v) tags, with no duplicated or collapsed old vertices.
Equality of any chronological signed word values in the finite
G₂ implies equality of their complete signed actions at
EVERY vertex of the ENTIRE original anchored type-(1) family.
The canonical Cayley(G₂) map based at an arbitrary family
vertex then covers PRECISELY its true reachable completed
signed-action component, on both vertices and directed
signed edge tokens (including newly added fixed loops).

This is full type-(1) family G₂ coverage, but only ONE of the
three corrected Definition-5.3 families. The type-(2)
off-B augmented family, exact full selected Z₁ catalogue,
higher-rank history/Condition 5.2/Theorem 4.7 and ordinary
PSTS EPPA are separate open obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Exact underlying dependent carrier of ALL genuine
literal-paper anchored type-(1) augmented stages. Every
source (A,P,B,v) index remains explicitly tagged. -/
abbrev sourceLiteralY1AllType1FamilyVertex
    (src dst : ι → V) :=
  Σ j : sourceLiteralY1Type1Index src dst,
    ClusterSpec.augmentedType1Vertex j.2

/-- The COMPLETE signed action of the entire true printed
type-(1) family, with the literal original old P-cluster and
attached full B-coset in each fibre, and legal fixed-loop
completion. No generic catalogue-only surrogate. -/
noncomputable def sourceLiteralY1AllType1FamilyStage
    (src dst : ι → V) :
    CompleteEGraph
      (sourceLiteralY1AllType1FamilyVertex src dst)
      (ActionEdge (sourceLiteralY1AllType1FamilyVertex src dst) ι) ι :=
  dependentDisjointStage
    (fun j : sourceLiteralY1Type1Index src dst =>
      ClusterSpec.augmentedType1Stage j.2)

/-- ACTUAL finite G₂ group-word equality forces equality
of complete signed word actions at EVERY original indexed
(A,P,B,v)-tagged vertex of the ENTIRE printed type-(1)
family. This is not merely an individual fibre theorem or
an equality of ambient group coordinates. -/
theorem sourceG2LiteralY1AllType1Family_wordValue_congr
    (src dst : ι → V)
    (p q : LabelWord ι)
    (hpq :
      PSTS.SignedWord.evalGroup (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup (sourceAllLocalG2Generator src dst) q) :
    ∀ x : sourceLiteralY1AllType1FamilyVertex src dst,
      (sourceLiteralY1AllType1FamilyStage src dst).followWord x p =
      (sourceLiteralY1AllType1FamilyStage src dst).followWord x q := by
  exact (dependentDisjointStage_wordEquality_all_iff
    (fun j : sourceLiteralY1Type1Index src dst =>
      ClusterSpec.augmentedType1Stage j.2) p q).mpr (by
    intro j x
    exact sourceG2LiteralY1Type1_wordValue_congr
      src dst j.1.1 j.1.2
      j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2
      p q hpq x)

/-- An ACTUAL based labelled signed Cayley(G₂) morphism into
the entire literal printed type-(1) family, rooted at ANY
(A,P,B,v,old/new-point) vertex and respecting all tags. -/
noncomputable def sourceG2LiteralY1AllType1FamilyCayleyHom
    (src dst : ι → V)
    (u : sourceLiteralY1AllType1FamilyVertex src dst) :
    LabelledGraphHom
      (cayleyGraph (sourceAllLocalG2Generator src dst)).toEGraph.toLabelledGraph
      (sourceLiteralY1AllType1FamilyStage src dst).toEGraph.toLabelledGraph :=
  (sourceLiteralY1AllType1FamilyStage src dst).cayleyCoverFromWordCongruence
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1AllType1Family_wordValue_congr src dst) u

/-- The based actual G₂ Cayley map hits exactly its requested
original printed anchored type-(1) vertex. -/
theorem sourceG2LiteralY1AllType1FamilyCayleyHom_one
    (src dst : ι → V)
    (u : sourceLiteralY1AllType1FamilyVertex src dst) :
    (sourceG2LiteralY1AllType1FamilyCayleyHom src dst u).onVertex 1 = u :=
  (sourceLiteralY1AllType1FamilyStage src dst).cayleyCoverFromWordCongruence_one
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1AllType1Family_wordValue_congr src dst) u

/-- The full indexed ORIGINAL printed type-(1) family Cayley(G₂)
map reaches EXACTLY the complete signed-action component of
its specified root, neither fewer points nor unrelated fibres. -/
theorem sourceG2LiteralY1AllType1FamilyCayleyHom_vertex_range
    (src dst : ι → V)
    (u : sourceLiteralY1AllType1FamilyVertex src dst) :
    Set.range
      (sourceG2LiteralY1AllType1FamilyCayleyHom src dst u).onVertex =
      {v : sourceLiteralY1AllType1FamilyVertex src dst |
        (sourceLiteralY1AllType1FamilyStage src dst).Reachable u v} :=
  (sourceLiteralY1AllType1FamilyStage src dst).cayleyCoverFromWordCongruence_vertex_range
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1AllType1Family_wordValue_congr src dst) u

/-- The identical printed type-(1) Cayley(G₂) cover maps ONTO
all actual formal directed signed action-edge tokens with
reachable sources, including both signs of newly inserted
fixed loops. No old+fresh identification by ambient values. -/
theorem sourceG2LiteralY1AllType1FamilyCayleyHom_edge_range
    (src dst : ι → V)
    (u : sourceLiteralY1AllType1FamilyVertex src dst) :
    Set.range
      (sourceG2LiteralY1AllType1FamilyCayleyHom src dst u).onEdge =
      {e : ActionEdge (sourceLiteralY1AllType1FamilyVertex src dst) ι |
        (sourceLiteralY1AllType1FamilyStage src dst).Reachable u
          ((sourceLiteralY1AllType1FamilyStage src dst).source e)} :=
  (sourceLiteralY1AllType1FamilyStage src dst).cayleyCoverFromWordCongruence_edge_range
    (sourceAllLocalG2Generator src dst)
    (sourceAllLocalG2Generator_isGenerated src dst)
    (sourceG2LiteralY1AllType1Family_wordValue_congr src dst) u

end ABO
end PSTSEPPA
