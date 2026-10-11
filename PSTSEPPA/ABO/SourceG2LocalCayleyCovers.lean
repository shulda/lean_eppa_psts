import PSTSEPPA.ABO.SourceH1AllLocalG2
import PSTSEPPA.ABO.UniversalStageRealCayleyCover

/-!
# Actual Cayley graph covering maps for the finite source-graph G2

The already-certified source construction (#343, #348) produces a
FINITE synchronously generated G2 from the original oriented edge
labels and the genuine three-family completed coset stages of
EVERY local H1[A] Cayley skeleton on two letters.

Here we connect this exact group to the actual graph-cover layer:
for each root in its entire true tagged disjoint completed action,
construct the literal labelled morphism Cayley(G2) -> that stage.
It maps 1 to the prescribed root, sends any group word to precisely
the signed path endpoint, and its vertex and directed-edge images
are EXACTLY the reachable component of the root. No injectivity
or ambient-coordinate Cayley embedding is assumed.

Since the complete stage is a dependent DISJOINT union of the actual
three-family geometric actions, all these covers preserve the
true outer stage index. Distinct coset quotient tags never get
identified by an auxiliary ambient H1 coordinate.

This is the graph-cover consequence of the genuinely constructed
first-level G2, not a proof that every original source Definition-5.3
Z1 stage has already been identified with one of our local actions,
or a proof of the higher-rank reflecting group/PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The exact true tagged stage vertex type of the concrete G2
from the original input graph. No quotient by H1 coordinates. -/
noncomputable abbrev sourceG2LocalStageVertex
    (src dst : ι → V) :=
  rankTwoIndexedAmbientVertex
    (gen := sourceH1Generator src dst)
    (fun j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst) =>
      allLocalRankTwoAlphabet j)
    (fun j => allLocalRankTwoAlphabet_card j)
    (fun j => allLocalRankTwoSkeleton j)
    (sourceH1_twoRetractable src dst)

/-- The literal completed dependent disjoint source action
whose true transition group is used to form G2. -/
noncomputable abbrev sourceG2LocalCompleteStage
    (src dst : ι → V) :=
  allLocalRankTwoStage (gen := sourceH1Generator src dst)
    (sourceH1_twoRetractable src dst)

/-- The canonical signed labelled Cayley graph morphism from
the ACTUAL generated finite G2 to its true completed stage,
based at any chosen vertex. -/
noncomputable def sourceG2LocalCayleyHom
    (src dst : ι → V)
    (u : sourceG2LocalStageVertex src dst) :
    LabelledGraphHom
      (cayleyGraph (sourceAllLocalG2Generator src dst)).toEGraph.toLabelledGraph
      (sourceG2LocalCompleteStage src dst).toEGraph.toLabelledGraph :=
  SynchronizedProduct.stageCoverCayleyHom
    (sourceH1Generator src dst)
    (sourceG2LocalCompleteStage src dst) u

/-- The identity of the REAL finite G2 goes to the selected
actual stage vertex, not just to its H1 ambient image. -/
@[simp] theorem sourceG2LocalCayleyHom_one
    (src dst : ι → V)
    (u : sourceG2LocalStageVertex src dst) :
    (sourceG2LocalCayleyHom src dst u).onVertex 1 = u := by
  exact SynchronizedProduct.stageCoverCayleyHom_one
    (sourceH1Generator src dst)
    (sourceG2LocalCompleteStage src dst) u

/-- Following ANY signed word in the source-graph G2
produces exactly the endpoint of that SAME word in the
actual tagged completed rank-two geometric action. -/
theorem sourceG2LocalCayleyHom_word
    (src dst : ι → V)
    (u : sourceG2LocalStageVertex src dst)
    (w : LabelWord ι) :
    (sourceG2LocalCayleyHom src dst u).onVertex
      (PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) w) =
      (sourceG2LocalCompleteStage src dst).followWord u w := by
  exact SynchronizedProduct.stageCoverCayleyHom_word
    (sourceH1Generator src dst)
    (sourceG2LocalCompleteStage src dst) u w

/-- The image of the constructed G2 Cayley graph is
PRECISELY the true reachable component of the root,
including in a disconnected geometric completed stage. -/
theorem sourceG2LocalCayleyHom_vertex_range
    (src dst : ι → V)
    (u : sourceG2LocalStageVertex src dst) :
    Set.range (sourceG2LocalCayleyHom src dst u).onVertex =
      {v : sourceG2LocalStageVertex src dst |
        (sourceG2LocalCompleteStage src dst).Reachable u v} := by
  exact SynchronizedProduct.stageCoverCayleyHom_vertex_range
    (sourceH1Generator src dst)
    (sourceG2LocalCompleteStage src dst) u

/-- Every real formal signed edge of the same reachable
component is hit by the G2 Cayley cover. Both orientations
and formal inverses of loops remain distinct edge tokens. -/
theorem sourceG2LocalCayleyHom_edge_range
    (src dst : ι → V)
    (u : sourceG2LocalStageVertex src dst) :
    Set.range (sourceG2LocalCayleyHom src dst u).onEdge =
      {e : ActionEdge (sourceG2LocalStageVertex src dst) ι |
        (sourceG2LocalCompleteStage src dst).Reachable
          u ((sourceG2LocalCompleteStage src dst).source e)} := by
  exact SynchronizedProduct.stageCoverCayleyHom_edge_range
    (sourceH1Generator src dst)
    (sourceG2LocalCompleteStage src dst) u

end ABO
end PSTSEPPA
