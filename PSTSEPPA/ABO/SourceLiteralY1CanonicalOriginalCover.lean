import PSTSEPPA.ABO.SourceLiteralY1ActionKernel
import PSTSEPPA.ABO.SourceOriginalH1PreimageSkeleton
import PSTSEPPA.ABO.DisjointCompleteTransitionQuotients

/-!
# The genuine paper projection T(Y₁) → T(X₁) and its original-edge preimage

The literal first paper action Y₁ is the complete, signed, TAGGED disjoint
union X₁ ⊔ ⨆ᵢ Cayley(G₁[{i}]). Its ACTUAL transition subgroup T(Y₁)
restricts to X₁ because no signed transition leaves its old summand.
The preceding general disjoint-union theorem constructs this restriction
as a generator-preserving SURJECTIVE labelled group quotient
T(Y₁) ↠ T(X₁)=G₁. No auxiliary synchronized H₁ group presentation is
used to DEFINE the printed first-rank projection.

The resulting canonical T(Y₁)-Cayley action maps to initial X₁ at any
selected original basepoint. We select EXACTLY the original positive
and negative input edge tokens in its Cayley preimage: a signed edge
(g,s) is present iff its projected X₁ source equals the source of the
ACTUAL original input edge s. All fake completeness edges of X₁ are
omitted. The literal preimage is closed under the formal signed edge
involution and maps to the ORIGINAL incomplete input EGraph, with
literal signed edge lifting and path lifting at any prescribed fibre
source.

The constructed cover has all T(Y₁) group vertices; intrinsic A-components
and full coset extension tags remain a separate next step. Matching this
DIRECT printed T(Y₁) projection with the transported synchronized-source
H₁ projection and selected Definition-5.3 Z₁ stages remains open, as do
Condition 5.2, Theorem 4.7 and PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The TRUE generator-preserving SURJECTIVE projection of the
paper's literal T(Y₁) complete transition group onto G₁=T(X₁).
This comes DIRECTLY from restricting the literal Y₁ complete
action to its old X₁ summand, not from a model isomorphism. -/
noncomputable def sourceLiteralY1ToG1Quotient
    (src dst : ι → V) :
    LabelledGroupQuotient
      (sourceLiteralY1 src dst).transitionSubgroupGenerator
      (sourceG1Generator src dst) :=
  (sourceX1 src dst).disjointUnionLeftQuotient
    (sourceLiteralY1UnaryStage src dst)

/-- The canonical labelled morphism from the actual paper
T(Y₁)-Cayley graph to the initial COMPLETE X₁ action at base.
The additional X₁ edges are excluded in the old-edge preimage
defined below. -/
noncomputable def sourceLiteralY1ToX1Hom
    (src dst : ι → V) (base : V) :
    LabelledGraphHom
      (cayleyGraph
        (sourceLiteralY1 src dst).transitionSubgroupGenerator).toEGraph.toLabelledGraph
      (sourceX1 src dst).toEGraph.toLabelledGraph :=
  (sourceX1 src dst).cayleyProjectionFromGroup
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceLiteralY1ToG1Quotient src dst).hom
    (sourceLiteralY1ToG1Quotient src dst).map_gen base

/-- Literal paper-H₁ group orbit in X₁, induced by the
actual T(Y₁) restriction quotient at a specified old vertex. -/
noncomputable abbrev sourceLiteralY1Orbit
    (src dst : ι → V) (base : V)
    (g : (sourceLiteralY1 src dst).transitionGroup) : V :=
  (sourceLiteralY1ToX1Hom src dst base).onVertex g

/-- Identity in the actual printed group T(Y₁) projects
to the selected X₁ basepoint, as required by the source cover. -/
@[simp] theorem sourceLiteralY1Orbit_one
    (src dst : ι → V) (base : V) :
    sourceLiteralY1Orbit src dst base 1 = base := by
  exact (sourceX1 src dst).cayleyProjectionFromGroup_one
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceLiteralY1ToG1Quotient src dst).hom
    (sourceLiteralY1ToG1Quotient src dst).map_gen base

/-- The direct paper-H₁ orbit of the literal group value of
a signed word agrees EXACTLY with the corresponding X₁ word path,
including inverse letters and trivial labelled generators. -/
theorem sourceLiteralY1Orbit_evalGroup
    (src dst : ι → V) (base : V) (w : LabelWord ι) :
    sourceLiteralY1Orbit src dst base
        (PSTS.SignedWord.evalGroup
          (sourceLiteralY1 src dst).transitionSubgroupGenerator w) =
      (sourceX1 src dst).followWord base w :=
  (sourceX1 src dst).cayleyProjectionFromGroup_evalGroup
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceLiteralY1ToG1Quotient src dst).hom
    (sourceLiteralY1ToG1Quotient src dst).map_gen base w

/-- The direct canonical paper covering commutes with each signed
Cayley edge target in the TRUE total X₁ action. The OLD-edge
subset restriction is performed separately below. -/
theorem sourceLiteralY1Orbit_cayley_target
    (src dst : ι → V) (base : V)
    (e : ActionEdge
      (sourceLiteralY1 src dst).transitionGroup ι) :
    sourceLiteralY1Orbit src dst base
      ((cayleyGraph
        (sourceLiteralY1 src dst).transitionSubgroupGenerator).target e) =
      (sourceX1 src dst).target
        (sourceLiteralY1Orbit src dst base e.1, e.2) := by
  have h := (sourceLiteralY1ToX1Hom src dst base).map_target e
  change
    (sourceX1 src dst).target
      ((sourceX1 src dst).edgeAt
        (sourceLiteralY1Orbit src dst base e.1) e.2) =
      sourceLiteralY1Orbit src dst base
        ((cayleyGraph
          (sourceLiteralY1 src dst).transitionSubgroupGenerator).target e) at h
  have hedge :
      (sourceX1 src dst).edgeAt
        (sourceLiteralY1Orbit src dst base e.1) e.2 =
      (sourceLiteralY1Orbit src dst base e.1, e.2) := by
    change (actionGraph (fun i => Equiv.swap (src i) (dst i))).edgeAt
      (sourceLiteralY1Orbit src dst base e.1) e.2 =
        (sourceLiteralY1Orbit src dst base e.1, e.2)
    exact actionGraph.edgeAt (fun i => Equiv.swap (src i) (dst i)) _ _
  rw [hedge] at h
  exact h.symm

/-- EXACT signed original-edge inverse-image Cayley skeleton
inside the literal paper T(Y₁), omitting every false additional
edge of the X₁ completion while retaining all old group vertices. -/
noncomputable def sourceLiteralY1DirectOriginalSkeleton
    (src dst : ι → V) (base : V) :
    CayleySubgraphSpec
      (sourceLiteralY1 src dst).transitionSubgroupGenerator Finset.univ where
  vertices := Set.univ
  edges := {e |
    sourceLiteralY1Orbit src dst base e.1 =
      sourceInputSignedSource src dst e.2}
  source_mem := by
    intro e he
    trivial
  label_mem := by
    intro e he
    exact Finset.mem_univ _
  inv_mem := by
    intro e he
    change
      sourceLiteralY1Orbit src dst base
        ((cayleyGraph
          (sourceLiteralY1 src dst).transitionSubgroupGenerator).target e) =
      sourceInputSignedSource src dst (PSTS.SignedLetter.inv e.2)
    calc
      sourceLiteralY1Orbit src dst base
          ((cayleyGraph
            (sourceLiteralY1 src dst).transitionSubgroupGenerator).target e) =
        (sourceX1 src dst).target
          (sourceLiteralY1Orbit src dst base e.1, e.2) :=
        sourceLiteralY1Orbit_cayley_target src dst base e
      _ = (sourceX1 src dst).target
          (sourceInputSignedSource src dst e.2, e.2) := by rw [he]
      _ = sourceInputSignedSource src dst
          (PSTS.SignedLetter.inv e.2) :=
        sourceX1_original_signed_target src dst e.2

/-- The real direct paper T(Y₁) preimage maps to the ORIGINAL
incomplete EGraph. In particular every old directed edge token
maps literally to its own signed label, rather than to an
artificial complete X₁ transition edge. -/
noncomputable def sourceLiteralY1DirectOriginalHom
    (src dst : ι → V) (base : V) :
    LabelledGraphHom
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).toEGraph).toLabelledGraph
      (sourceInputEGraph src dst).toLabelledGraph where
  onVertex x := sourceLiteralY1Orbit src dst base x.1
  onEdge e := e.1.2
  map_source e := by
    change sourceInputSignedSource src dst e.1.2 =
      sourceLiteralY1Orbit src dst base e.1.1
    exact e.2.symm
  map_inv _ := rfl
  map_label _ := rfl

/-- Every GENUINE original signed edge has a lift from any
specified paper-H₁ cover fibre vertex above its source. The
lift is one of the actual old preimage edge tokens and thus
also handles both orientations of a geometric input loop. -/
theorem sourceLiteralY1DirectOriginal_edge_lift
    (src dst : ι → V) (base : V)
    (s : SignedLabel ι)
    (x : (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex)
    (hx :
      (sourceLiteralY1DirectOriginalHom src dst base).onVertex x =
        (sourceInputEGraph src dst).source s) :
    ∃ e : (sourceLiteralY1DirectOriginalSkeleton src dst base).Edge,
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).toEGraph).source e = x ∧
      (sourceLiteralY1DirectOriginalHom src dst base).onEdge e = s := by
  have he : (x.1, s) ∈
      (sourceLiteralY1DirectOriginalSkeleton src dst base).edges := by
    change sourceLiteralY1Orbit src dst base x.1 =
      sourceInputSignedSource src dst s
    exact hx
  refine ⟨⟨(x.1,s),he⟩, ?_, ?_⟩
  · apply Subtype.ext
    rfl
  · rfl

/-- The direct printed source covering lifts EVERY REAL
original signed input path from ANY selected vertex above its
source, preserving the whole chronological word and target.
No missing old edge is postulated and no fake X₁ completion
edge is used. -/
theorem sourceLiteralY1DirectOriginal_follows_lift
    (src dst : ι → V) (base : V)
    {u v : V} {w : LabelWord ι}
    (hp : (sourceInputEGraph src dst).Follows u w v)
    (x : (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex)
    (hx : (sourceLiteralY1DirectOriginalHom src dst base).onVertex x = u) :
    ∃ y : (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex,
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).toEGraph).Follows x w y ∧
      (sourceLiteralY1DirectOriginalHom src dst base).onVertex y = v := by
  let K := sourceLiteralY1DirectOriginalSkeleton src dst base
  let F := sourceLiteralY1DirectOriginalHom src dst base
  induction hp generalizing x with
  | nil u =>
      exact ⟨x, EGraph.Follows.nil x, hx⟩
  | @cons u v s w e hs hl hrest ih =>
      have hsrc : F.onVertex x =
          (sourceInputEGraph src dst).source e := hx.trans hs.symm
      obtain ⟨f, hfsrc, hfmap⟩ :=
        sourceLiteralY1DirectOriginal_edge_lift src dst base e x hsrc
      have htarget : F.onVertex (K.toEGraph.target f) =
          (sourceInputEGraph src dst).target e := by
        calc
          F.onVertex (K.toEGraph.target f) =
            (sourceInputEGraph src dst).target (F.onEdge f) :=
              (F.map_target f).symm
          _ = (sourceInputEGraph src dst).target e := by rw [hfmap]
      obtain ⟨y, hyLift, hyMap⟩ :=
        ih (K.toEGraph.target f) htarget
      have hfLabel : K.toEGraph.label f = s := by
        calc
          K.toEGraph.label f =
            (sourceInputEGraph src dst).label (F.onEdge f) :=
              (F.map_label f).symm
          _ = (sourceInputEGraph src dst).label e := by rw [hfmap]
          _ = s := hl
      exact ⟨y, EGraph.Follows.cons f hfsrc hfLabel hyLift, hyMap⟩

end ABO
end PSTSEPPA
