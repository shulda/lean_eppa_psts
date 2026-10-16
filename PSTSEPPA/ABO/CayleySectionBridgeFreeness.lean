import PSTSEPPA.ABO.TrivialLoopCompletionCayleyCosetBridge

/-!
# A compatible based Cayley cover and OLD lift imply bridge-freeness

For the corrected ABO Theorem 4.7 geometry we need to
distinguish three ingredients:

(1) the actual incomplete signed EGraph G and its LEGAL
    stationary-loop completion complete(G);
(2) a labelled based Cayley(Γ) -> complete(G) covering map F;
(3) an OLD signed-graph lift S : G -> Cayley(Γ).

It is NOT valid to infer existence of (3) from (2).
However, once a lift exists and is compatible with the
cover at one old basepoint, connectedness of the old graph
forces F(S(x))=x on EVERY old vertex: compare the old path
from the basepoint with its double projected path.

This supplies the missing exact section property, hence
S is automatically VERTEX INJECTIVE. Moreover any ambient
B-left-coset connection between S(x) and S(y) projects to
a path in complete(G), and the independently certified
signed loop-stripping theorem yields a TRUE B-word path
in the OLD incomplete G. Thus both embedding and
absence of artificial B-bridges follow from the stated
compatible-lift hypothesis.

The actual construction of such a lift S for the
component-tagged multi-coset extension is the remaining
nontrivial Theorem-4.7 embeddedness work. This lemma
does NOT invent the lift, assume global ambient-coordinate
injectivity or prove unrestricted bridge freeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V Edge Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace EGraph

variable (G : EGraph V Edge ι)

/-- A labelled OLD lift and a complete-stage Cayley map
whose composite fixes ONE basepoint automatically compose
to the identity on ALL old vertices, provided every old
vertex is reached by some genuine signed path from that
basepoint. Only original edges are used in this proof. -/
theorem cayleyBasedOldLift_isSection_of_connected
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      (G.trivialLoopCompletion hpaired).toEGraph.toLabelledGraph)
    (S : LabelledGraphHom
      G.toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph)
    (base : V)
    (hbase : F.onVertex (S.onVertex base) = base)
    (hConnected : ∀ v : V, ∃ w : LabelWord ι,
      G.Follows base w v) :
    ∀ v : V, F.onVertex (S.onVertex v) = v := by
  intro v
  obtain ⟨w, hPath⟩ := hConnected v
  have hCayley :
      (cayleyGraph gen).toEGraph.Follows
        (S.onVertex base) w (S.onVertex v) :=
    hPath.map S
  have hProjected :
      (G.trivialLoopCompletion hpaired).toEGraph.Follows
        (F.onVertex (S.onVertex base)) w
        (F.onVertex (S.onVertex v)) :=
    hCayley.map F
  have hOldCompleted :
      (G.trivialLoopCompletion hpaired).toEGraph.Follows
        base w v :=
    hPath.map (G.trivialLoopCompletionHom hpaired)
  rw [hbase] at hProjected
  exact (G.trivialLoopCompletion hpaired).toEGraph.follows_right_unique
    hProjected hOldCompleted

/-- A genuine labelled section S of a Cayley projection
is automatically injective on OLD vertices and reflects
EVERY B-coset ambient connection to an actual B-path in
the original INCOMPLETE graph, for arbitrary B including
the empty alphabet. No surjectivity of the Cayley map is
needed beyond the stipulated old-point section. -/
theorem cayleySection_embedding_and_noBBridges
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      (G.trivialLoopCompletion hpaired).toEGraph.toLabelledGraph)
    (S : LabelledGraphHom
      G.toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph)
    (hSection : ∀ x : V, F.onVertex (S.onVertex x) = x) :
    Function.Injective S.onVertex ∧
    ∀ (B : Finset ι) (x y : V),
      S.onVertex y ∈ generatedLeftCoset gen B (S.onVertex x) →
      ∃ q : LabelWord ι,
        LabelWord.Uses B q ∧ G.Follows x q y := by
  constructor
  · intro x y hxy
    calc
      x = F.onVertex (S.onVertex x) := (hSection x).symm
      _ = F.onVertex (S.onVertex y) := congrArg F.onVertex hxy
      _ = y := hSection y
  · intro B x y hCoset
    obtain ⟨q, hqB, hqPath⟩ :=
      G.trivialLoopCompletion_cayleyCoset_oldPath
        hpaired gen F B
        (S.onVertex x) (S.onVertex y) hCoset
    refine ⟨q, hqB, ?_⟩
    simpa only [hSection x, hSection y] using hqPath

/-- Rooted connected version: the compatibility condition
at ONE basepoint plus the existence of the OLD labelled
lift S already implies both vertex embedding and ALL
proper-subalphabet bridge exclusions. In particular
the bridge argument adds no new group-coordinate
injectivity assumption. -/
theorem cayleyBasedOldLift_embedding_and_noBBridges
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      (G.trivialLoopCompletion hpaired).toEGraph.toLabelledGraph)
    (S : LabelledGraphHom
      G.toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph)
    (base : V)
    (hbase : F.onVertex (S.onVertex base) = base)
    (hConnected : ∀ v : V, ∃ w : LabelWord ι,
      G.Follows base w v) :
    Function.Injective S.onVertex ∧
    ∀ (B : Finset ι) (x y : V),
      S.onVertex y ∈ generatedLeftCoset gen B (S.onVertex x) →
      ∃ q : LabelWord ι,
        LabelWord.Uses B q ∧ G.Follows x q y := by
  exact G.cayleySection_embedding_and_noBBridges
    hpaired gen F S
    (G.cayleyBasedOldLift_isSection_of_connected
      hpaired gen F S base hbase hConnected)

end EGraph
end ABO
end PSTSEPPA
