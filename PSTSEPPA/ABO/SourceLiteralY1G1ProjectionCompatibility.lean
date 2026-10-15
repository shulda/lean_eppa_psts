import PSTSEPPA.ABO.SourceLiteralY1CanonicalOriginalCover
import PSTSEPPA.ABO.SourceLiteralY1H1GroupEquiv
import PSTSEPPA.ABO.SourceOriginalH1PreimageSkeleton

/-!
# The literal Y₁→X₁ restriction is the synchronized H₁→G₁ projection

At the first corrected ABO rank there are now TWO independently
constructed, Lean-checked presentations of H₁:

* SourceH₁, the genuinely generated synchronized unary detector group;
* the paper's LITERAL transition group T(Y₁), where Y₁ is the actual
  signed disjoint union X₁ ⊔ ⨆ᵢ Cayley(G₁[{i}]).

These are identified by a generator-preserving group isomorphism E.
There are also TWO independently defined generator-preserving quotients
to the original transition group G₁=T(X₁): the synchronized first-coordinate
quotient and the paper's actual restriction of T(Y₁) to the X₁ summand.

This module checks that the triangle COMMUTES ON ALL GROUP ELEMENTS,
not merely on selected generator or word representatives. It then
checks that both canonical Cayley projections have exactly the same
original-input vertex values and the same predicate on REAL signed
original input edge tokens. No artificially completed X₁ edge is
introduced.

These facts are the precise compatibility bridge needed to prove a
cover-over-input isomorphism and ultimately transport the selected
Definition-5.3 Z₁ geometric stages from actual T(Y₁) to the already
audited SourceH₁ cover model. No such completed-stage equivalence,
Condition 5.2, Theorem 4.7 or PSTS EPPA is asserted here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The canonical labelled group isomorphism SourceH₁ ≃ T(Y₁)
intertwines the ACTUAL paper restriction T(Y₁) → T(X₁) with
the separately constructed synchronized first-coordinate quotient
SourceH₁ → G₁. This equality holds for EVERY generated group element
(including a group with repeated or identity-labelled generators). -/
theorem sourceLiteralY1ToG1_compatible_with_sourceH1
    (src dst : ι → V) (h : SourceH1 src dst) :
    (sourceLiteralY1ToG1Quotient src dst).hom
        (sourceH1EquivLiteralY1Transition src dst h) =
      (unarySynchronizedCoverQuotient
        (sourceG1Generator src dst)
        (sourceG1Generator_isGenerated src dst)).hom h := by
  obtain ⟨w, hw⟩ :=
    (sourceH1Generator_isGenerated src dst).exists_evalGroup_eq h
  rw [← hw]
  calc
    (sourceLiteralY1ToG1Quotient src dst).hom
        (sourceH1EquivLiteralY1Transition src dst
          (PSTS.SignedWord.evalGroup (sourceH1Generator src dst) w)) =
      (sourceLiteralY1ToG1Quotient src dst).hom
        (PSTS.SignedWord.evalGroup
          (sourceLiteralY1 src dst).transitionSubgroupGenerator w) :=
        congrArg (sourceLiteralY1ToG1Quotient src dst).hom
          (sourceH1EquivLiteralY1Transition_evalGroup src dst w)
    _ = PSTS.SignedWord.evalGroup (sourceG1Generator src dst) w :=
      (sourceLiteralY1ToG1Quotient src dst).map_evalGroup w
    _ = (unarySynchronizedCoverQuotient
          (sourceG1Generator src dst)
          (sourceG1Generator_isGenerated src dst)).hom
          (PSTS.SignedWord.evalGroup (sourceH1Generator src dst) w) :=
      ((unarySynchronizedCoverQuotient
        (sourceG1Generator src dst)
        (sourceG1Generator_isGenerated src dst)).map_evalGroup w).symm

/-- The canonical projections to the ORIGINAL X₁ vertex set
commute with the H₁-labelled group equivalence. Hence changing
between the paper's literal H₁ and our synchronized presentation
does NOT change the old vertex over which a Cayley element lies. -/
theorem sourceLiteralY1Orbit_equiv_sourceH1Orbit
    (src dst : ι → V) (base : V)
    (h : SourceH1 src dst) :
    sourceLiteralY1Orbit src dst base
        (sourceH1EquivLiteralY1Transition src dst h) =
      sourceH1Orbit src dst base h := by
  change CompleteEGraph.rightApply
      ((sourceLiteralY1ToG1Quotient src dst).hom
        (sourceH1EquivLiteralY1Transition src dst h)) base =
    CompleteEGraph.rightApply
      ((unarySynchronizedCoverQuotient
        (sourceG1Generator src dst)
        (sourceG1Generator_isGenerated src dst)).hom h) base
  rw [sourceLiteralY1ToG1_compatible_with_sourceH1]

/-- After applying the ACTUAL labelled group isomorphism, the
DIRECT paper T(Y₁) original-edge preimage has exactly the same
old signed directed edge predicate as the SourceH₁ original
preimage; neither predicate sees X₁'s artificial edges. -/
theorem sourceLiteralY1DirectOriginal_edge_iff_sourceH1
    (src dst : ι → V) (base : V)
    (h : SourceH1 src dst) (s : SignedLabel ι) :
    (sourceH1EquivLiteralY1Transition src dst h, s) ∈
        (sourceLiteralY1DirectOriginalSkeleton src dst base).edges ↔
      (h, s) ∈ (sourceH1OriginalSkeleton src dst base).edges := by
  change
    sourceLiteralY1Orbit src dst base
      (sourceH1EquivLiteralY1Transition src dst h) =
        sourceInputSignedSource src dst s ↔
    sourceH1Orbit src dst base h =
        sourceInputSignedSource src dst s
  rw [sourceLiteralY1Orbit_equiv_sourceH1Orbit]

/-- The vertex projection of the DIRECT printed source cover
agrees with the original SourceH₁ cover projection after applying
the generator-preserving group isomorphism; this is an equality
in the ORIGINAL input vertex set, not just in X₁. -/
theorem sourceLiteralY1DirectOriginal_vertex_projection_equiv
    (src dst : ι → V) (base : V)
    (h : SourceH1 src dst) :
    (sourceLiteralY1DirectOriginalHom src dst base).onVertex
      (⟨sourceH1EquivLiteralY1Transition src dst h, by trivial⟩ :
        (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex) =
    (sourceH1OriginalSkeletonHom src dst base).onVertex
      (⟨h, by trivial⟩ :
        (sourceH1OriginalSkeleton src dst base).Vertex) := by
  change sourceLiteralY1Orbit src dst base
    (sourceH1EquivLiteralY1Transition src dst h) =
      sourceH1Orbit src dst base h
  exact sourceLiteralY1Orbit_equiv_sourceH1Orbit src dst base h

/-- Original signed directed input-edge tokens are STRICTLY
preserved by the same basepoint and group-coordinate change,
even when both orientations of a geometric edge are loops. -/
theorem sourceLiteralY1DirectOriginal_edge_projection_equiv
    (src dst : ι → V) (base : V)
    (h : SourceH1 src dst) (s : SignedLabel ι)
    (hs : (h,s) ∈ (sourceH1OriginalSkeleton src dst base).edges) :
    (sourceLiteralY1DirectOriginalHom src dst base).onEdge
      (⟨(sourceH1EquivLiteralY1Transition src dst h, s),
        (sourceLiteralY1DirectOriginal_edge_iff_sourceH1
          src dst base h s).mpr hs⟩ :
        (sourceLiteralY1DirectOriginalSkeleton src dst base).Edge) =
    (sourceH1OriginalSkeletonHom src dst base).onEdge
      (⟨(h,s),hs⟩ :
        (sourceH1OriginalSkeleton src dst base).Edge) :=
  rfl

end ABO
end PSTSEPPA
