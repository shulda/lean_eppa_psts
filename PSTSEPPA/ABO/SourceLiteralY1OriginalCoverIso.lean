import PSTSEPPA.ABO.SourceLiteralY1H1GroupEquiv
import PSTSEPPA.ABO.SourceOriginalH1PreimageSkeleton
import PSTSEPPA.ABO.InjectiveLabelledQuotientSkeletonIso

/-!
# The paper's literal T(Y₁) has EXACTLY the original H₁-cover geometry

The printed corrected ABO first expansion is the actual complete action
Y₁ = X₁ ⊔ ⨆_i Cayley(G₁[{i}]), with H₁^paper := T(Y₁).
Our earlier SourceH₁ was a concrete finite synchronously generated group.
The independently Lean-certified source isomorphism between these two
labelled groups preserves EACH positive generator and every signed word.

We transfer that isomorphism to the ORIGINAL INCOMPLETE INPUT-GRAPH
preimage inside the respective Cayley graphs. The source H₁ old-edge
preimage has every H₁ group point and exactly those signed edges
whose projected initial vertex is the actual source of that old edge,
excluding all other artificial edges of X₁.

The label-preserving group isomorphism gives a labelled quotient in
the reverse direction T(Y₁) ↠ SourceH₁. Pulling back the genuine
incomplete source Cayley skeleton along this quotient defines the
literal T(Y₁) original-edge preimage with EXACTLY the same old
oriented signed edge tokens. Because the quotient is injective too,
the resulting graph morphism is bijective on BOTH all old vertices
and directed signed edge tokens and commutes STRICTLY with the
projection to the ORIGINAL input EGraph.

This is the missing first-rank source-to-literal H₁ cover interface.
It does NOT identify the printed selected completed Z₁ stages with
the three-kind supercatalogue or establish Condition 5.2,
Theorem 4.7, later ranks, the reflecting group or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The canonical labelled-group quotient from the LITERAL
T(Y₁) to the separately constructed source synchronized H₁,
obtained by the actual inverse labelled group isomorphism.
All positive and negative generator values are preserved. -/
noncomputable def sourceLiteralY1ToSourceH1Quotient
    (src dst : ι → V) :
    LabelledGroupQuotient
      (sourceLiteralY1 src dst).transitionSubgroupGenerator
      (sourceH1Generator src dst) where
  hom := (sourceH1EquivLiteralY1Transition src dst).symm.toMonoidHom
  map_gen := by
    intro i
    let E := sourceH1EquivLiteralY1Transition src dst
    change E.symm ((sourceLiteralY1 src dst).transitionSubgroupGenerator i) =
      sourceH1Generator src dst i
    have h :
        E (sourceH1Generator src dst i) =
          (sourceLiteralY1 src dst).transitionSubgroupGenerator i :=
      sourceH1EquivLiteralY1Transition_generator src dst i
    simpa using congrArg E.symm h.symm
  surjective :=
    (sourceH1EquivLiteralY1Transition src dst).symm.surjective

/-- EXACT old-edge Cayley preimage inside the printed literal
H₁=T(Y₁), with no X₁-only artificial edges. It is defined
as the generator-preserving group-isomorphism pullback of the
ALREADY VERIFIED true source-original incomplete H₁ skeleton,
so every original signed edge remains a separate real edge
token and no new edge is added. -/
noncomputable def sourceLiteralY1OriginalSkeleton
    (src dst : ι → V) (base : V) :
    CayleySubgraphSpec
      (sourceLiteralY1 src dst).transitionSubgroupGenerator Finset.univ :=
  (sourceH1OriginalSkeleton src dst base).pullbackQuotient
    (sourceLiteralY1ToSourceH1Quotient src dst)

/-- The canonical signed labelled morphism from the actual
paper-H₁ original-input preimage into the source synchronized
H₁ original-input preimage. It is an isomorphism on vertices
and oriented edge tokens; the proof is separate below. -/
noncomputable def sourceLiteralY1OriginalSkeletonToSourceH1
    (src dst : ι → V) (base : V) :
    LabelledGraphHom
      ((sourceLiteralY1OriginalSkeleton src dst base).toEGraph).toLabelledGraph
      ((sourceH1OriginalSkeleton src dst base).toEGraph).toLabelledGraph :=
  (sourceH1OriginalSkeleton src dst base).pullbackQuotientHom
    (sourceLiteralY1ToSourceH1Quotient src dst)

/-- The ACTUAL PAPER-H₁ original graph cover maps back into
the ORIGINAL incomplete input graph, not all of X₁.
It factors STRICTLY through the already-certified source H₁
cover and therefore retains all prescribed signed edge labels. -/
noncomputable def sourceLiteralY1OriginalSkeletonToInput
    (src dst : ι → V) (base : V) :
    LabelledGraphHom
      ((sourceLiteralY1OriginalSkeleton src dst base).toEGraph).toLabelledGraph
      (sourceInputEGraph src dst).toLabelledGraph :=
  (sourceH1OriginalSkeletonHom src dst base).comp
    (sourceLiteralY1OriginalSkeletonToSourceH1 src dst base)

/-- The Cayley-pullback map from the paper H₁=T(Y₁) to our
old-edge SourceH₁ preimage is a genuine vertex- AND
SIGNED-DIRECTED-EDGE bijection. No vertex with an equal
ambient group coordinate can cause a component collapse. -/
theorem sourceLiteralY1OriginalSkeletonToSourceH1_bijective
    (src dst : ι → V) (base : V) :
    Function.Bijective
      (sourceLiteralY1OriginalSkeletonToSourceH1 src dst base).onVertex ∧
    Function.Bijective
      (sourceLiteralY1OriginalSkeletonToSourceH1 src dst base).onEdge := by
  let Q := sourceLiteralY1ToSourceH1Quotient src dst
  have hQ : Function.Injective Q.hom := by
    change Function.Injective
      ((sourceH1EquivLiteralY1Transition src dst).symm :
        (sourceLiteralY1 src dst).transitionGroup → SourceH1 src dst)
    exact (sourceH1EquivLiteralY1Transition src dst).symm.injective
  exact (sourceH1OriginalSkeleton src dst base).pullbackQuotientHom_bijective_of_injective
    Q hQ

/-- The paper T(Y₁) old-edge preimage has exactly the same
oriented signed edge membership predicate as the original
source H₁ preimage after applying the concrete inverse group
isomorphism. In particular all fake completion edges are absent. -/
theorem sourceLiteralY1OriginalSkeleton_edge_iff
    (src dst : ι → V) (base : V)
    (e : ActionEdge
      (sourceLiteralY1 src dst).transitionGroup ι) :
    e ∈ (sourceLiteralY1OriginalSkeleton src dst base).edges ↔
      sourceH1Orbit src dst base
        ((sourceH1EquivLiteralY1Transition src dst).symm e.1) =
          sourceInputSignedSource src dst e.2 :=
  Iff.rfl

/-- Exact source vertex-projection formula for the literal
paper group, independent of any arbitrary representative of
an intrinsic A-component or a component-tagged coset point. -/
@[simp] theorem sourceLiteralY1OriginalSkeletonToInput_vertex
    (src dst : ι → V) (base : V)
    (x : (sourceLiteralY1OriginalSkeleton src dst base).Vertex) :
    (sourceLiteralY1OriginalSkeletonToInput src dst base).onVertex x =
      sourceH1Orbit src dst base
        ((sourceH1EquivLiteralY1Transition src dst).symm x.1) :=
  rfl

/-- The original input directed edge token of the paper's
literal H₁ cover is exactly the signed label of the
corresponding old Cayley edge; formal +/- tokens remain
distinct even if both are geometric loops. -/
@[simp] theorem sourceLiteralY1OriginalSkeletonToInput_edge
    (src dst : ι → V) (base : V)
    (e : (sourceLiteralY1OriginalSkeleton src dst base).Edge) :
    (sourceLiteralY1OriginalSkeletonToInput src dst base).onEdge e =
      e.1.2 :=
  rfl

end ABO
end PSTSEPPA
