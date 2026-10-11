import PSTSEPPA.ABO.SourceOriginalH1PreimageSkeleton
import PSTSEPPA.ABO.IntrinsicComponentLocalSliceIso
import PSTSEPPA.ABO.AllLocalRankTwoCayleySkeletons

/-!
# Every original H1-cover component is one of the finite local skeleton indices

Corrected ABO Definition 5.3 refers to connected H1-covers of
the ORIGINAL oriented input graph E[A], not covers of the
artificially completed initial action X1. The previously
certified SourceOriginalH1PreimageSkeleton gives an actual
incomplete H1-Cayley inverse-image skeleton for EVERY source
basepoint. IntrinsicComponentLocalSliceIso proves that ANY
genuine signed A-component of such a skeleton is bijectively
translated into the generated subgroup H1[A] while preserving
every old vertex, every signed oriented edge and the root.

This module makes that reduction a LITERAL FINITE SOURCE INDEX.
An index records an original basepoint in V, a genuine two-letter
alphabet A and a selected H1 preimage vertex h. It chooses
NO representatives of cosets or connected-component classes.

The local skeleton associated to each index is exactly the
rooted connected A-component of the real original graph
preimage, translated to H1[A]. It is therefore automatically
ONE OF the (A,K) indices of the already Lean-certified all-local
rank-two superfamily used to construct the finite group G2.
The local-to-source-component morphism is bijective on genuine
vertices and directed signed edge tokens.

This closes the source-cover component INDEXING step at the
level of incomplete graphs, not yet the functorial transport
of their completed coset extensions and B-augmentations.
No full source Condition 5.2 or PSTS EPPA is claimed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- A finite and completely redundant index for every
original-graph H1 cover component: original source basepoint,
actual two-letter alphabet and actual H1 preimage root. -/
abbrev SourceOriginalH1CoverIndex
    (src dst : ι → V) :=
  Σ base : V, Σ a : {A : Finset ι // A.card = 2},
    SourceH1 src dst

/-- The literal original incomplete source-cover Cayley
skeleton for the selected source input basepoint. -/
noncomputable abbrev sourceCoverIndexSkeleton
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :=
  sourceH1OriginalSkeleton src dst j.1

/-- The selected original source H1 vertex, viewed in
the genuine A-edge restriction of the preimage skeleton.
All H1 vertices are retained by the original inverse-image
construction; only the REAL signed edges are restricted. -/
noncomputable def sourceCoverIndexRoot
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :
    ((sourceCoverIndexSkeleton src dst j).restrictAlphabet j.2.1.1).Vertex :=
  ⟨j.2.2, by trivial⟩

/-- The ACTUAL connected A-component of the original H1
Cayley preimage at the selected vertex (NOT its entire
ambient H1[A] coset). -/
noncomputable abbrev sourceCoverIndexComponent
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :=
  ((sourceCoverIndexSkeleton src dst j).restrictAlphabet j.2.1.1).subalphabetComponentSubgraph j.2.1.1
      (sourceCoverIndexRoot src dst j)

/-- Its canonical local-Cayley presentation, rooted at 1
in the generated subgroup H1[A], with exactly its old
A-labelled original signed edges. -/
noncomputable abbrev sourceCoverIndexLocalSkeleton
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :=
  (sourceCoverIndexComponent src dst j).leftCosetSlice j.2.2

/-- Every genuine source H1-cover component is LITERALLY
one of the finite all-local pair indices used in G2.
The first coordinate is exactly A, and the second is the
true normalized connected component. No external
source-C_H enumeration is needed at construction time. -/
noncomputable def sourceCoverIntoAllLocalIndex
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :
    AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst) :=
  ⟨j.2.1, sourceCoverIndexLocalSkeleton src dst j⟩

/-- Exact index projection: the source root's component is
represented by the very same local graph, with NO enlargement
to the full ambient A-Cayley subgroup graph. -/
theorem sourceCoverIntoAllLocalIndex_exact
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :
    (sourceCoverIntoAllLocalIndex src dst j).2 =
      sourceCoverIndexLocalSkeleton src dst j := rfl

/-- The canonical local-to-source-cover-component morphism
is a literal bijection on both types of graph objects:
vertices and formal signed oriented edge tokens. This is
the exact graph-level source-cover correspondence needed
before transporting the full coset-extension construction. -/
theorem sourceCoverIndex_local_graph_bijective
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :
    Function.Bijective
      ((sourceCoverIndexComponent src dst j).leftCosetSliceHom j.2.2).onVertex ∧
    Function.Bijective
      ((sourceCoverIndexComponent src dst j).leftCosetSliceHom j.2.2).onEdge := by
  exact
    ((sourceCoverIndexSkeleton src dst j).restrictAlphabet j.2.1.1).intrinsicComponentLocalHom_bijective j.2.1.1
        (sourceCoverIndexRoot src dst j)

/-- Every input-indexed H1-cover component has a canonical
local representative whose identity maps to the selected
root, not to an arbitrarily chosen group coset representative. -/
theorem sourceCoverIndex_local_identity_normalization
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :
    ∃ x : (sourceCoverIndexLocalSkeleton src dst j).Vertex,
      x.1 =
        (1 : generatedSubgroup (sourceH1Generator src dst) j.2.1.1) ∧
      ((sourceCoverIndexComponent src dst j).leftCosetSliceHom j.2.2).onVertex x =
        ((sourceCoverIndexSkeleton src dst j).restrictAlphabet j.2.1.1).componentLiftVertex j.2.1.1
            (sourceCoverIndexRoot src dst j)
            (sourceCoverIndexRoot src dst j)
            (((sourceCoverIndexSkeleton src dst j).restrictAlphabet j.2.1.1).subalphabetReachable_refl j.2.1.1
                (sourceCoverIndexRoot src dst j)) := by
  exact
    ((sourceCoverIndexSkeleton src dst j).restrictAlphabet j.2.1.1).intrinsicComponentLocal_identity_root j.2.1.1
        (sourceCoverIndexRoot src dst j)

/-- All possible genuine source H1-cover component indices
form an ACTUAL FINITE family, even for disconnected original
graphs and repeated or loop edge labels. Its finiteness uses
the constructed finite H1, not a postulated finite cover. -/
theorem finite_SourceOriginalH1CoverIndex
    (src dst : ι → V) :
    Finite (SourceOriginalH1CoverIndex src dst) := by
  classical
  letI : Finite (SourceH1 src dst) := finite_sourceH1 src dst
  infer_instance

end ABO
end PSTSEPPA
