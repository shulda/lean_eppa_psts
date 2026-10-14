import PSTSEPPA.ABO.SourceOriginalH1Z1ActualG2CayleyCover
import PSTSEPPA.ABO.SourceH1AllLocalG2

/-!
# A concrete first-rank ABO source-stage covering theorem for genuine finite G₂

Start with any finite original oriented edge-labelled input, including
loops and nonfaithful labels. The actual source H₁ is its explicit
source-shaped first generated synchronous group, and G₂ is the
CONCRETE finite synchronously generated group of all genuine local
rank-two signed stage actions. Both groups and their generators
are defined from the input, not postulated abstractly.

The certified algebra supplies a generator-preserving surjective
1-stable quotient G₂→H₁ and genuine 2-retractability of G₂.
The certified source-specific completed-stage congruence and its
real Cayley cover supply, for EVERY vertex of EVERY original
three-kind H₁ source stage, a true labelled Cayley(G₂) map
onto EXACTLY the reachable complete signed graph component,
surjective on both vertices and directed signed edge tokens.

The main theorem packages this precise source-facing rank-one
geometric/algebraic bridge in one human-readable place. It is
stronger than bare word-kernel inclusion, and it never conflates
old coset quotient tags with equal ambient group coordinates.

**Scope:** The source three-family supercatalogue is verified
input-dependent and finite-indexed. Additional equivalence to the
paper's *selected* Definition-5.3 Z₁, coherent automorphism
actions, corrected Condition 5.2, Theorem 4.7 and all higher
Yₖ/Zₖ rank induction remain mathematically OPEN. This is NOT
the final unconditional ordinary PSTS EPPA theorem.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Actual finite source G₂: a 1-stable quotient onto the
original source-shaped H₁, 2-retractable, and with a genuine
based labelled signed Cayley cover onto every reachable
component of the entire original H₁ Z₁ three-family completed
action, including surjectivity on formal directed edge tokens. -/
theorem sourceG2_firstRank_sourceStageCover
    (src dst : ι → V) :
    (sourceAllLocalG2ToH1 src dst).KStable 1 ∧
    KRetractable (sourceAllLocalG2Generator src dst) 2 ∧
    ∀ (u : SourceOriginalH1Z1Vertex src dst),
      ∃ f : LabelledGraphHom
        (cayleyGraph (sourceAllLocalG2Generator src dst)).toEGraph.toLabelledGraph
        (sourceOriginalH1Z1ThreeFamilyStage src dst).toEGraph.toLabelledGraph,
        f.onVertex 1 = u ∧
        Set.range f.onVertex =
          {v : SourceOriginalH1Z1Vertex src dst |
            (sourceOriginalH1Z1ThreeFamilyStage src dst).Reachable u v} ∧
        Set.range f.onEdge =
          {e : ActionEdge (SourceOriginalH1Z1Vertex src dst) ι |
            (sourceOriginalH1Z1ThreeFamilyStage src dst).Reachable u
              ((sourceOriginalH1Z1ThreeFamilyStage src dst).source e)} := by
  refine ⟨sourceAllLocalG2ToH1_oneStable src dst,
    sourceAllLocalG2_twoRetractable src dst, ?_⟩
  intro u
  exact ⟨sourceOriginalH1Z1G2CayleyHom src dst u,
    sourceOriginalH1Z1G2CayleyHom_one src dst u,
    sourceOriginalH1Z1G2CayleyHom_vertex_range src dst u,
    sourceOriginalH1Z1G2CayleyHom_edge_range src dst u⟩

end ABO
end PSTSEPPA
