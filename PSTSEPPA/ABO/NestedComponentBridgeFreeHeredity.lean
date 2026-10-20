import PSTSEPPA.ABO.NestedComponentSignedEdges
import PSTSEPPA.ABO.ForwardInductionFromActualLowerClusters

/-!
# ABO Theorem 4.5: actual hereditary lower bridge-freeness

The forward cardinality induction assumes bridge-freeness for
every genuine lower C-component of the ORIGINAL signed old
A-skeleton, not an artificially strengthened assumption for
every iterated nested lower component.

The preceding two modules proved the crucial actual-geometry
fact: for D⊆B, a nested D-component of a rooted B-component
has exactly the same Γ-valued vertex set AND oriented signed
old edge set as the original D-component of K.

Since all remaining CayleySubgraphSpec fields are PROOFS of
closure properties, the two D-skeleton objects are equal
by proof irrelevance. We now derive the source-hereditary
consequence: the printed lower rooted bridge-free hypothesis
for K implies the SAME lower rooted bridge-free hypothesis
for EVERY selected proper B-component of K.

The bridge-free structures retain their actual completed
component-tagged D-coset extensions, not just untagged
ambient Cayley coordinates. This is the missing recursion
control needed to apply the induction hypothesis of
Theorem 4.5 to every genuine lower rooted component.

No false original edge, no global ambient embedding assumption,
no generated/retractable group shortcut, and no new axiom/sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

/-- Extensionality for a literal Cayley skeleton from its actual
old group-vertex and oriented signed-edge sets. All other fields
are propositional closure proofs, hence proof-irrelevant. -/
private theorem nestedSkeleton_ext {D : Finset ι}
    {L R : CayleySubgraphSpec gen D}
    (hv : L.vertices = R.vertices)
    (he : L.edges = R.edges) : L = R := by
  cases L with
  | mk lv le ls li ll =>
      cases R with
      | mk rv re rs ri rl =>
          cases hv
          cases he
          rfl

variable (K : CayleySubgraphSpec gen A)

/-- An ACTUAL nested D-component of the original old
B-component is the SAME CayleySubgraphSpec gen D as the
original rooted D-component in K, on both original vertices
and full signed oriented old edge tokens. -/
theorem nestedComponent_eq_original
    (B D : Finset ι) (hDB : D ⊆ B) (root : K.Vertex)
    (x : (K.subalphabetComponentSubgraph B root).Vertex) :
    ((K.subalphabetComponentSubgraph B root).subalphabetComponentSubgraph
      D x) =
    K.subalphabetComponentSubgraph D
      ((K.subalphabetComponentSubgraphHom B root).onVertex x) := by
  have hBoth := K.nestedComponent_vertex_edge_sets B D hDB root x
  exact nestedSkeleton_ext hBoth.1 hBoth.2

/-- The source's actual lower rooted bridge-free premise is
HEREDITARY under passage to any genuine proper B-component.
No additional nested-rank bridge-free assumption is needed:
all nested D-stages are exactly original D-stages by the
literal original signed vertex/edge identity above. -/
theorem lowerRootedBridgeFree_hereditary
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hBridge : K.HasAllLowerRootedBridgeFree hadm hgen hret)
    (B : Finset ι) (hBA : B ⊂ A) (root : K.Vertex) :
    (K.subalphabetComponentSubgraph B root).HasAllLowerRootedBridgeFree
      (K.subalphabetComponentSubgraph_admissible
        hadm B hBA root) hgen hret := by
  intro D hDP x
  have hDB : D ⊂ B := (mem_allProperCosetFamily B D).mp hDP
  have hDA : D ⊂ A := lt_trans hDB hBA
  have hSame :=
    K.nestedComponent_eq_original B D hDB.subset root x
  have hActual :=
    hBridge D ((mem_allProperCosetFamily A D).mpr hDA)
      ((K.subalphabetComponentSubgraphHom B root).onVertex x)
  simpa only [hSame] using hActual

end CayleySubgraphSpec
end ABO
end PSTSEPPA
