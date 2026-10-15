import PSTSEPPA.ABO.BijectiveLabelledEGraphPaths
import PSTSEPPA.ABO.SourceLiteralY1OriginalCoverIndexEquiv

/-!
# Literal paper H₁ original-cover A-components are the indexed source ones

The corrected first-rank Definition 5.3 refers to connected A-components
of the ORIGINAL incomplete signed input graph's H₁ preimages. We have
now constructed all required ingredients independently:

* the literal paper transition group T(Y₁) with its direct original-edge
  preimage Cayley skeleton;
* the synchronized SourceH₁ original-edge preimage and its finite
  source cover indices used in the G₂ all-local stage catalogue;
* a true signed labelled graph isomorphism between the DIRECT paper
  cover and the SourceH₁ cover over the same original EGraph; and
* a generic lemma showing that vertex-and-edge-bijective labelled
  morphisms preserve AND REFLECT every genuinely realised signed path.

We now compose the source cover isomorphisms explicitly and prove
that they preserve and reflect all A-supported signed old paths,
for every original input alphabet A, root and target. In particular,
the exact component rooted at any literal paper-H₁ cover index
is the preimage under this graph isomorphism of the corresponding
indexed original SourceH₁ A-component.

Thus EVERY printed literal first-rank original-input cover root
has the finite local representative already used in the construction
of G₂, WITHOUT declaring equality of ambient group coordinates
to be equality of component-tagged coset quotient vertices.

Still open: functorial transport of full/augmented selected Z₁
coset-extension stages, their automorphism-equivariance, corrected
Condition 5.2 and Theorem 4.7 geometry and higher rank induction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The true original signed T(Y₁)-preimage graph is transported
via the ALREADY-VERIFIED direct-to-transported paper cover
isomorphism followed by the source-H₁ original cover map.
Both maps are over the original input EGraph, never all of X₁. -/
noncomputable def sourceLiteralY1DirectToSourceH1OriginalHom
    (src dst : ι → V) (base : V) :
    LabelledGraphHom
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).toEGraph).toLabelledGraph
      ((sourceH1OriginalSkeleton src dst base).toEGraph).toLabelledGraph :=
  (sourceLiteralY1OriginalSkeletonToSourceH1 src dst base).comp
    (sourceLiteralY1DirectToTransportedOriginalHom src dst base)

/-- The composed direct-paper-to-source comparison remains a
GENUINE SIGNED GRAPH ISOMORPHISM, with inverse on the true
vertex and oriented directed signed edge-token types. -/
theorem sourceLiteralY1DirectToSourceH1OriginalHom_bijective
    (src dst : ι → V) (base : V) :
    Function.Bijective
      (sourceLiteralY1DirectToSourceH1OriginalHom src dst base).onVertex ∧
    Function.Bijective
      (sourceLiteralY1DirectToSourceH1OriginalHom src dst base).onEdge := by
  have hD :=
    sourceLiteralY1DirectToTransportedOriginalHom_bijective
      src dst base
  have hT :=
    sourceLiteralY1OriginalSkeletonToSourceH1_bijective
      src dst base
  constructor
  · constructor
    · intro x y h
      exact hD.1.1 (hT.1.1 h)
    · intro y
      obtain ⟨z, hz⟩ := hT.1.2 y
      obtain ⟨x, hx⟩ := hD.1.2 z
      refine ⟨x, ?_⟩
      change (sourceLiteralY1OriginalSkeletonToSourceH1
        src dst base).onVertex
          ((sourceLiteralY1DirectToTransportedOriginalHom
            src dst base).onVertex x) = y
      rw [hx, hz]
  · constructor
    · intro e f h
      exact hD.2.1 (hT.2.1 h)
    · intro y
      obtain ⟨z, hz⟩ := hT.2.2 y
      obtain ⟨x, hx⟩ := hD.2.2 z
      refine ⟨x, ?_⟩
      change (sourceLiteralY1OriginalSkeletonToSourceH1
        src dst base).onEdge
          ((sourceLiteralY1DirectToTransportedOriginalHom
            src dst base).onEdge x) = y
      rw [hx, hz]

/-- The composite direct-paper to source H₁ cover
isomorphism commutes with projections into ORIGINAL input
vertices. Not merely a map to X₁ complete transition endpoints. -/
theorem sourceLiteralY1DirectToSourceH1_over_input_vertex
    (src dst : ι → V) (base : V)
    (x : (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex) :
    (sourceH1OriginalSkeletonHom src dst base).onVertex
      ((sourceLiteralY1DirectToSourceH1OriginalHom
        src dst base).onVertex x) =
    (sourceLiteralY1DirectOriginalHom src dst base).onVertex x := by
  change
    (sourceLiteralY1OriginalSkeletonToInput
      src dst base).onVertex
      ((sourceLiteralY1DirectToTransportedOriginalHom
        src dst base).onVertex x) =
    (sourceLiteralY1DirectOriginalHom src dst base).onVertex x
  exact sourceLiteralY1DirectToTransported_over_input_vertex
    src dst base x

/-- The same exact cover-commutation holds for every signed
ORIGINAL oriented edge token, preserving its sign even if
the corresponding original edge is a geometric loop. -/
theorem sourceLiteralY1DirectToSourceH1_over_input_edge
    (src dst : ι → V) (base : V)
    (e : (sourceLiteralY1DirectOriginalSkeleton src dst base).Edge) :
    (sourceH1OriginalSkeletonHom src dst base).onEdge
      ((sourceLiteralY1DirectToSourceH1OriginalHom
        src dst base).onEdge e) =
    (sourceLiteralY1DirectOriginalHom src dst base).onEdge e := by
  change
    (sourceLiteralY1OriginalSkeletonToInput
      src dst base).onEdge
      ((sourceLiteralY1DirectToTransportedOriginalHom
        src dst base).onEdge e) =
    (sourceLiteralY1DirectOriginalHom src dst base).onEdge e
  exact sourceLiteralY1DirectToTransported_over_input_edge
    src dst base e

/-- The DIRECT paper H₁ signed original edge path language is
exactly the source-synchronized H₁ original edge path language,
under the literal graph isomorphism, for all chronological signed
words, endpoints, loops and disconnected original input graphs. -/
theorem sourceLiteralY1DirectToSourceH1_original_paths_iff
    (src dst : ι → V) (base : V)
    (x y : (sourceLiteralY1DirectOriginalSkeleton
      src dst base).Vertex)
    (w : LabelWord ι) :
    ((sourceLiteralY1DirectOriginalSkeleton
      src dst base).toEGraph).Follows x w y ↔
    ((sourceH1OriginalSkeleton
      src dst base).toEGraph).Follows
        ((sourceLiteralY1DirectToSourceH1OriginalHom
          src dst base).onVertex x) w
        ((sourceLiteralY1DirectToSourceH1OriginalHom
          src dst base).onVertex y) := by
  have hb :=
    sourceLiteralY1DirectToSourceH1OriginalHom_bijective
      src dst base
  exact ((sourceLiteralY1DirectOriginalSkeleton
    src dst base).toEGraph).follows_iff_of_bijective_labelledHom
      ((sourceH1OriginalSkeleton src dst base).toEGraph)
      (sourceLiteralY1DirectToSourceH1OriginalHom src dst base)
      hb.1 hb.2 x y w

/-- Arbitrary intrinsic A-components of ACTUAL original paper
H₁ covers are exactly the SourceH₁ components, tested by
real signed A-words, not by ambient H₁[A] coset equality. -/
theorem sourceLiteralY1DirectToSourceH1_A_reachable_iff
    (src dst : ι → V) (base : V) (A : Finset ι)
    (x y : (sourceLiteralY1DirectOriginalSkeleton
      src dst base).Vertex) :
    (sourceLiteralY1DirectOriginalSkeleton src dst base).SubalphabetReachable
      A x y ↔
    (sourceH1OriginalSkeleton src dst base).SubalphabetReachable
      A
      ((sourceLiteralY1DirectToSourceH1OriginalHom
        src dst base).onVertex x)
      ((sourceLiteralY1DirectToSourceH1OriginalHom
        src dst base).onVertex y) := by
  have hb :=
    sourceLiteralY1DirectToSourceH1OriginalHom_bijective
      src dst base
  exact ((sourceLiteralY1DirectOriginalSkeleton
    src dst base).toEGraph).subalphabet_paths_iff_of_bijective_labelledHom
      ((sourceH1OriginalSkeleton src dst base).toEGraph)
      (sourceLiteralY1DirectToSourceH1OriginalHom src dst base)
      hb.1 hb.2 A x y

/-- The literal paper preimage root given by the exact finite
cover-index equivalence maps to the ACTUAL source-H₁ root,
without choosing any abstract connected-component class
representative. -/
theorem sourceLiteralY1DirectToSourceH1_index_root
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :
    (sourceLiteralY1DirectToSourceH1OriginalHom
      src dst j.1).onVertex
      (⟨(sourceOriginalH1CoverIndexEquivLiteral
          src dst j).2.2, by trivial⟩ :
        (sourceLiteralY1DirectOriginalSkeleton
          src dst j.1).Vertex) =
      (⟨j.2.2, by trivial⟩ :
        (sourceH1OriginalSkeleton src dst j.1).Vertex) := by
  apply Subtype.ext
  change (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceH1EquivLiteralY1Transition src dst j.2.2) = j.2.2
  simp

/-- FIRST-RANK SOURCE COVER INDEX CLASSIFICATION:
for EVERY literal paper T(Y₁) old-edge cover root in the
finite index family, its true A-component at the chosen
root is precisely the SOURCE H₁ original A-component of
the corresponding indexed root. Both sides use only REAL
signed original input paths, with no artificial X₁ edges. -/
theorem sourceLiteralY1_index_A_component_iff_source
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst)
    (y : (sourceLiteralY1DirectOriginalSkeleton
      src dst j.1).Vertex) :
    (sourceLiteralY1DirectOriginalSkeleton src dst j.1).SubalphabetReachable
      j.2.1.1
      (⟨(sourceOriginalH1CoverIndexEquivLiteral
          src dst j).2.2, by trivial⟩ :
        (sourceLiteralY1DirectOriginalSkeleton src dst j.1).Vertex)
      y ↔
    (sourceH1OriginalSkeleton src dst j.1).SubalphabetReachable
      j.2.1.1
      (⟨j.2.2, by trivial⟩ :
        (sourceH1OriginalSkeleton src dst j.1).Vertex)
      ((sourceLiteralY1DirectToSourceH1OriginalHom
        src dst j.1).onVertex y) := by
  have hPath :=
    sourceLiteralY1DirectToSourceH1_A_reachable_iff
      src dst j.1 j.2.1.1
      (⟨(sourceOriginalH1CoverIndexEquivLiteral
          src dst j).2.2, by trivial⟩ :
        (sourceLiteralY1DirectOriginalSkeleton src dst j.1).Vertex)
      y
  rw [sourceLiteralY1DirectToSourceH1_index_root src dst j] at hPath
  exact hPath

end ABO
end PSTSEPPA
