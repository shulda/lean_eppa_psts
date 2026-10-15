import PSTSEPPA.ABO.SourceLiteralY1OriginalCoverIso
import PSTSEPPA.ABO.SourceLiteralY1G1ProjectionCompatibility

/-!
# The DIRECT and TRANSPORTED literal T(Y₁) original-input covers coincide

There are TWO entirely independently built true ORIGINAL-input preimages
inside the actual T(Y₁)-Cayley group:

* the DIRECT preimage of the paper's intrinsic restriction
  T(Y₁)↠T(X₁)=G₁, formed by selecting exactly the old original
  oriented signed input-edge tokens in its canonical X₁ action;
* the TRANSPORTED preimage of the old SourceH₁ cover along the
  independently proved same-labelled SourceH₁ ≃* T(Y₁).

We do not assume these coincide by definition. The preceding
two-sided quotient compatibility theorem proves both T(Y₁) projections
have identical original input vertex values; consequently the
directly selected and transported OLD EDGE predicates coincide.

We construct an actual labelled graph isomorphism between these
two INCOMPLETE signed preimages. It is the identity on the same
ambient T(Y₁) Cayley vertex coordinates and real formal oriented
signed edge tokens (not an identification of distinct completed
coset quotient points), and it is bijective on BOTH their old
vertex and edge carriers. The graph isomorphism moreover commutes
STRICTLY with the projections to the ORIGINAL input EGraph,
on vertices and on both signed edge orientations.

This closes the first-rank direct-vs-transported original H₁ COVER
comparison. It DOES NOT identify the eventual full/augmented
selected Definition-5.3 Z₁ completed coset extension family,
prove source stage equivariance, Condition 5.2, Theorem 4.7,
higher rank induction or ordinary PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The direct paper H₁ old-edge predicate is equivalent to the
separately transported SourceH₁ old-edge predicate, ON EVERY
genuine oriented signed Cayley token. This equality includes both
signed orientations of geometric loops, repeated labels, and
vertices at which the artificial X₁ completion has extra edges. -/
theorem sourceLiteralY1Direct_vs_transported_edge_iff
    (src dst : ι → V) (base : V)
    (e : ActionEdge (sourceLiteralY1 src dst).transitionGroup ι) :
    e ∈ (sourceLiteralY1DirectOriginalSkeleton src dst base).edges ↔
      e ∈ (sourceLiteralY1OriginalSkeleton src dst base).edges := by
  let E := sourceH1EquivLiteralY1Transition src dst
  have h :=
    sourceLiteralY1DirectOriginal_edge_iff_sourceH1
      src dst base (E.symm e.1) e.2
  have hpair : (E (E.symm e.1), e.2) = e := by
    apply Prod.ext
    · simp
    · rfl
  rw [hpair] at h
  change e ∈ (sourceLiteralY1DirectOriginalSkeleton src dst base).edges ↔
    sourceH1Orbit src dst base (E.symm e.1) =
      sourceInputSignedSource src dst e.2 at h
  exact h.trans
    (sourceLiteralY1OriginalSkeleton_edge_iff src dst base e).symm

/-- The canonical signed labelled morphism is the LITERAL
identity on the common ambient paper-H₁ Cayley coordinates.
The nontrivial proof obligation is that its edge predicate
has exactly the correct source, inverse and signed label. -/
noncomputable def sourceLiteralY1DirectToTransportedOriginalHom
    (src dst : ι → V) (base : V) :
    LabelledGraphHom
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).toEGraph).toLabelledGraph
      ((sourceLiteralY1OriginalSkeleton src dst base).toEGraph).toLabelledGraph where
  onVertex x := ⟨x.1, by trivial⟩
  onEdge e :=
    ⟨e.1, (sourceLiteralY1Direct_vs_transported_edge_iff
      src dst base e.1).mp e.2⟩
  map_source := by
    intro e
    apply Subtype.ext
    rfl
  map_inv := by
    intro e
    apply Subtype.ext
    rfl
  map_label := by
    intro e
    rfl

/-- The direct-to-transported comparison is bijective on
the original H₁-cover VERTICES AND DIRECTED SIGNED EDGE TOKENS;
no artificial completion edge or coset-label collapse is involved. -/
theorem sourceLiteralY1DirectToTransportedOriginalHom_bijective
    (src dst : ι → V) (base : V) :
    Function.Bijective
      (sourceLiteralY1DirectToTransportedOriginalHom
        src dst base).onVertex ∧
    Function.Bijective
      (sourceLiteralY1DirectToTransportedOriginalHom
        src dst base).onEdge := by
  constructor
  · constructor
    · intro x y h
      apply Subtype.ext
      exact congrArg Subtype.val h
    · intro y
      refine ⟨⟨y.1, by trivial⟩, ?_⟩
      apply Subtype.ext
      rfl
  · constructor
    · intro e f h
      apply Subtype.ext
      exact congrArg
        (fun z : (sourceLiteralY1OriginalSkeleton
          src dst base).Edge => z.1) h
    · intro y
      have hmem :
          y.1 ∈ (sourceLiteralY1DirectOriginalSkeleton
            src dst base).edges :=
        (sourceLiteralY1Direct_vs_transported_edge_iff
          src dst base y.1).mpr y.2
      refine ⟨⟨y.1, hmem⟩, ?_⟩
      apply Subtype.ext
      rfl

/-- The comparison map is an isomorphism OF COVERS OVER THE
ORIGINAL incomplete graph, not only an abstract labelled graph
isomorphism. All paper-H₁ original vertices project identically
in both constructions after their common Cayley coordinate map. -/
theorem sourceLiteralY1DirectToTransported_over_input_vertex
    (src dst : ι → V) (base : V)
    (x : (sourceLiteralY1DirectOriginalSkeleton
      src dst base).Vertex) :
    (sourceLiteralY1OriginalSkeletonToInput src dst base).onVertex
      ((sourceLiteralY1DirectToTransportedOriginalHom
        src dst base).onVertex x) =
    (sourceLiteralY1DirectOriginalHom src dst base).onVertex x := by
  change sourceH1Orbit src dst base
      ((sourceH1EquivLiteralY1Transition src dst).symm x.1) =
    sourceLiteralY1Orbit src dst base x.1
  have h :=
    sourceLiteralY1Orbit_equiv_sourceH1Orbit
      src dst base
      ((sourceH1EquivLiteralY1Transition src dst).symm x.1)
  simpa using h.symm

/-- Likewise each ACTUAL ORIGINAL directed signed edge
projects to exactly the SAME input edge token via the direct
or transported paper T(Y₁) preimage. Formal inverses remain
distinct, including when the original edge is a loop. -/
theorem sourceLiteralY1DirectToTransported_over_input_edge
    (src dst : ι → V) (base : V)
    (e : (sourceLiteralY1DirectOriginalSkeleton
      src dst base).Edge) :
    (sourceLiteralY1OriginalSkeletonToInput src dst base).onEdge
      ((sourceLiteralY1DirectToTransportedOriginalHom
        src dst base).onEdge e) =
    (sourceLiteralY1DirectOriginalHom src dst base).onEdge e :=
  rfl

end ABO
end PSTSEPPA
