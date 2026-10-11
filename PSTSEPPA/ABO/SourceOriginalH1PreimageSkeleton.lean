import PSTSEPPA.ABO.SourceX1ConcreteH1
import PSTSEPPA.ABO.CayleyStageProjection
import PSTSEPPA.ABO.CayleySubgraph

/-!
# The ACTUAL original oriented graph and its genuine H1-Cayley preimage

The original input graph has one genuinely oriented positive edge
src(i) --(+i)--> dst(i) and its formal inverse (-i). In the initial
complete action X1, the positive generator i swaps those endpoints,
fixing other vertices. The complete X1 consequently contains MANY
extra labelled edges that were NOT present in the original graph.

Corrected ABO Definition 5.3 uses covers of the ORIGINAL incomplete
oriented graph, not covers of all artificially completed X1 edges.

For each selected source basepoint v, take the exact finite H1 Cayley
action on X1 via the certified quotient H1 -> Transition(X1).
Retain all H1 group vertices, but only those TRUE signed Cayley
edges (h,s) whose projected initial vertex equals the original
source of the corresponding signed input edge s.

We prove that the resulting actual incomplete Cayley skeleton is
closed under formal edge inversion, and give a literal labelled
graph morphism to the ORIGINAL graph. EVERY real original signed
edge lifts at EVERY selected fibre source, and therefore every real
original signed path lifts, retaining its word and endpoint, from
any chosen source preimage. No missing X1 edge is introduced.

This is a geometric H1-cover input for source Y1/Z1, not yet the
connected-component cover classification or source Condition 5.2.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The original source vertex of each actual signed oriented
edge of the input graph. Positive and negative edge tokens
are distinct even when the endpoints coincide. -/
def sourceInputSignedSource
    (src dst : ι → V) : SignedLabel ι → V
  | .pos i => src i
  | .neg i => dst i

/-- The literal ORIGINAL finite incomplete directed E-graph.
Unlike X1, it has only TWO directed edge tokens per original
label, not a total transition at each vertex and label. -/
noncomputable def sourceInputEGraph
    (src dst : ι → V) :
    EGraph V (SignedLabel ι) ι where
  source := sourceInputSignedSource src dst
  inv := PSTS.SignedLetter.inv
  inv_inv := PSTS.SignedLetter.inv_inv
  inv_ne := by
    intro s h
    cases s <;> simp [PSTS.SignedLetter.inv] at h
  label := id
  label_inv := by
    intro s
    rfl
  deterministic := by
    intro e f _ hlabel
    exact hlabel

/-- The old signed edge in X1 has EXACTLY its prescribed
original endpoint, also for a loop and for the inverse token.
This does not assert anything about the many EXTRA X1 edges. -/
theorem sourceX1_original_signed_target
    (src dst : ι → V) (s : SignedLabel ι) :
    (sourceX1 src dst).target
      (sourceInputSignedSource src dst s, s) =
      sourceInputSignedSource src dst (PSTS.SignedLetter.inv s) := by
  cases s with
  | pos i =>
      change (Equiv.swap (src i) (dst i)) (src i) = dst i
      simp
  | neg i =>
      change ((Equiv.swap (src i) (dst i)).symm) (dst i) = src i
      simp

/-- The original graph embeds as a labelled SUBGRAPH of the
complete X1 action, using EXACTLY the original oriented edge
tokens. No false claim that it is an induced subgraph. -/
noncomputable def sourceInputToX1
    (src dst : ι → V) :
    LabelledGraphHom
      (sourceInputEGraph src dst).toLabelledGraph
      (sourceX1 src dst).toEGraph.toLabelledGraph where
  onVertex := id
  onEdge := fun s => (sourceInputSignedSource src dst s, s)
  map_source _ := rfl
  map_inv s := by
    change
      (sourceInputSignedSource src dst (PSTS.SignedLetter.inv s),
        PSTS.SignedLetter.inv s) =
      ((sourceX1 src dst).target
          (sourceInputSignedSource src dst s, s),
        PSTS.SignedLetter.inv s)
    exact Prod.ext (sourceX1_original_signed_target src dst s).symm rfl
  map_label _ := rfl

/-- The canonical COMPLETE Cayley action of the actual source H1
on X1 vertices, based at any input vertex v. Its homomorphism is
the true labelled first projection H1 -> G1 from #343. -/
noncomputable def sourceH1ToX1
    (src dst : ι → V) (base : V) :
    LabelledGraphHom
      (cayleyGraph (sourceH1Generator src dst)).toEGraph.toLabelledGraph
      (sourceX1 src dst).toEGraph.toLabelledGraph :=
  (sourceX1 src dst).cayleyProjectionFromGroup
    (sourceH1Generator src dst)
    (unarySynchronizedCoverQuotient
      (sourceG1Generator src dst)
      (sourceG1Generator_isGenerated src dst)).hom
    (unarySynchronizedCoverQuotient
      (sourceG1Generator src dst)
      (sourceG1Generator_isGenerated src dst)).map_gen
    base

/-- The actual vertex in the original X1 action reached by
the element h of H1 from a selected base vertex. -/
noncomputable abbrev sourceH1Orbit
    (src dst : ι → V) (base : V)
    (h : SourceH1 src dst) : V :=
  (sourceH1ToX1 src dst base).onVertex h

/-- The identity of H1 projects to the chosen source basepoint. -/
@[simp] theorem sourceH1Orbit_one
    (src dst : ι → V) (base : V) :
    sourceH1Orbit src dst base 1 = base := by
  exact (sourceX1 src dst).cayleyProjectionFromGroup_one
    (sourceH1Generator src dst)
    (unarySynchronizedCoverQuotient
      (sourceG1Generator src dst)
      (sourceG1Generator_isGenerated src dst)).hom
    (unarySynchronizedCoverQuotient
      (sourceG1Generator src dst)
      (sourceG1Generator_isGenerated src dst)).map_gen
    base

/-- Projection of one true H1 Cayley signed edge commutes with
its target in the COMPLETE X1 action. The *edge-set restriction*
to the original graph is made separately below. -/
theorem sourceH1Orbit_cayley_target
    (src dst : ι → V) (base : V)
    (e : ActionEdge (SourceH1 src dst) ι) :
    sourceH1Orbit src dst base
      ((cayleyGraph (sourceH1Generator src dst)).target e) =
      (sourceX1 src dst).target
        (sourceH1Orbit src dst base e.1, e.2) := by
  have h := (sourceH1ToX1 src dst base).map_target e
  change
    (sourceX1 src dst).target
      ((sourceX1 src dst).edgeAt
        (sourceH1Orbit src dst base e.1) e.2) =
      sourceH1Orbit src dst base
        ((cayleyGraph (sourceH1Generator src dst)).target e) at h
  rw [actionGraph.edgeAt] at h
  exact h.symm

/-- The exact inverse-image Cayley skeleton of the ORIGINAL
graph's oriented edge tokens. It retains every H1 vertex;
an H1 Cayley signed edge (h,s) is present iff its projected
source is exactly the source of the ORIGINAL input edge s.
Importantly it does NOT include an artificial X1 edge. -/
noncomputable def sourceH1OriginalSkeleton
    (src dst : ι → V) (base : V) :
    CayleySubgraphSpec (sourceH1Generator src dst) Finset.univ where
  vertices := Set.univ
  edges := {e | sourceH1Orbit src dst base e.1 =
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
      sourceH1Orbit src dst base
        ((cayleyGraph (sourceH1Generator src dst)).target e) =
      sourceInputSignedSource src dst (PSTS.SignedLetter.inv e.2)
    calc
      sourceH1Orbit src dst base
          ((cayleyGraph (sourceH1Generator src dst)).target e) =
        (sourceX1 src dst).target
          (sourceH1Orbit src dst base e.1, e.2) :=
        sourceH1Orbit_cayley_target src dst base e
      _ = (sourceX1 src dst).target
          (sourceInputSignedSource src dst e.2, e.2) := by
        rw [he]
      _ = sourceInputSignedSource src dst
          (PSTS.SignedLetter.inv e.2) :=
        sourceX1_original_signed_target src dst e.2

/-- The TRUE inverse-image incomplete Cayley skeleton maps
directly to the original EGraph, not just the completed X1.
Its directed edge-token map forgets the H1 fibre coordinate. -/
noncomputable def sourceH1OriginalSkeletonHom
    (src dst : ι → V) (base : V) :
    LabelledGraphHom
      ((sourceH1OriginalSkeleton src dst base).toEGraph).toLabelledGraph
      (sourceInputEGraph src dst).toLabelledGraph where
  onVertex x := sourceH1Orbit src dst base x.1
  onEdge e := e.1.2
  map_source e := by
    change sourceInputSignedSource src dst e.1.2 =
      sourceH1Orbit src dst base e.1.1
    exact e.2.symm
  map_inv _ := rfl
  map_label _ := rfl

/-- Every original signed edge has a REAL lift from EVERY
chosen H1 skeleton vertex above its source. No invented
Cayley edge or arbitrary lift of an incomplete path. -/
theorem sourceH1OriginalSkeleton_edge_lift
    (src dst : ι → V) (base : V)
    (s : SignedLabel ι)
    (x : (sourceH1OriginalSkeleton src dst base).Vertex)
    (hx :
      (sourceH1OriginalSkeletonHom src dst base).onVertex x =
        (sourceInputEGraph src dst).source s) :
    ∃ e : (sourceH1OriginalSkeleton src dst base).Edge,
      ((sourceH1OriginalSkeleton src dst base).toEGraph).source e = x ∧
      (sourceH1OriginalSkeletonHom src dst base).onEdge e = s := by
  have he :
      (x.1,s) ∈ (sourceH1OriginalSkeleton src dst base).edges := by
    change sourceH1Orbit src dst base x.1 =
      sourceInputSignedSource src dst s
    exact hx
  refine ⟨⟨(x.1,s),he⟩, ?_, ?_⟩
  · apply Subtype.ext
    rfl
  · rfl

/-- Every genuine signed path in the ORIGINAL input graph
lifts from any fixed H1 fibre starting point, with the SAME
signed word and its prescribed projected endpoint. -/
theorem sourceH1OriginalSkeleton_follows_lift
    (src dst : ι → V) (base : V)
    {u v : V} {w : LabelWord ι}
    (hp : (sourceInputEGraph src dst).Follows u w v)
    (x : (sourceH1OriginalSkeleton src dst base).Vertex)
    (hx : (sourceH1OriginalSkeletonHom src dst base).onVertex x = u) :
    ∃ y : (sourceH1OriginalSkeleton src dst base).Vertex,
      ((sourceH1OriginalSkeleton src dst base).toEGraph).Follows x w y ∧
      (sourceH1OriginalSkeletonHom src dst base).onVertex y = v := by
  let K := sourceH1OriginalSkeleton src dst base
  let F := sourceH1OriginalSkeletonHom src dst base
  induction hp generalizing x with
  | nil u =>
      exact ⟨x, EGraph.Follows.nil x, hx⟩
  | @cons u v s w e hs hl hrest ih =>
      have hsrc : F.onVertex x =
          (sourceInputEGraph src dst).source e := hx.trans hs.symm
      obtain ⟨f, hfsrc, hfmap⟩ :=
        sourceH1OriginalSkeleton_edge_lift src dst base e x hsrc
      have htarget : F.onVertex (K.toEGraph.target f) =
          (sourceInputEGraph src dst).target e := by
        calc
          F.onVertex (K.toEGraph.target f) =
            (sourceInputEGraph src dst).target (F.onEdge f) :=
              (F.map_target f).symm
          _ = (sourceInputEGraph src dst).target e := by
            rw [hfmap]
      obtain ⟨y, hyLift, hyMap⟩ :=
        ih (K.toEGraph.target f) htarget
      have hfLabel : K.toEGraph.label f = s := by
        calc
          K.toEGraph.label f =
            (sourceInputEGraph src dst).label (F.onEdge f) :=
              (F.map_label f).symm
          _ = (sourceInputEGraph src dst).label e := by
            rw [hfmap]
          _ = s := hl
      exact ⟨y, EGraph.Follows.cons f hfsrc hfLabel hyLift, hyMap⟩

/-- Exact image of the intrinsic signed C-component of any
specified H1-preimage root equals the signed C-component
of its vertex in the ACTUAL ORIGINAL input graph.
Both directions use real old edge tokens. -/
theorem sourceH1OriginalSkeleton_subalphabetReachable_iff
    (src dst : ι → V) (base : V)
    (C : Finset ι)
    (x : (sourceH1OriginalSkeleton src dst base).Vertex)
    (v : V) :
    (∃ w : LabelWord ι,
      LabelWord.Uses C w ∧
        (sourceInputEGraph src dst).Follows
          ((sourceH1OriginalSkeletonHom src dst base).onVertex x) w v) ↔
    ∃ y : (sourceH1OriginalSkeleton src dst base).Vertex,
      (sourceH1OriginalSkeleton src dst base).SubalphabetReachable C x y ∧
      (sourceH1OriginalSkeletonHom src dst base).onVertex y = v := by
  constructor
  · rintro ⟨w, hw, hp⟩
    obtain ⟨y, hy, hyval⟩ :=
      sourceH1OriginalSkeleton_follows_lift src dst base hp x rfl
    exact ⟨y, ⟨w, hw, hy⟩, hyval⟩
  · rintro ⟨y, ⟨w, hw, hy⟩, hyval⟩
    have hproj := hy.map (sourceH1OriginalSkeletonHom src dst base)
    rw [hyval] at hproj
    exact ⟨w, hw, hproj⟩

/-- The selected basepoint has its canonical lift at the
identity element of the concrete finite H1. -/
theorem sourceH1OriginalSkeleton_identity_base
    (src dst : ι → V) (base : V) :
    (sourceH1OriginalSkeletonHom src dst base).onVertex
      (⟨1, by trivial⟩ : (sourceH1OriginalSkeleton src dst base).Vertex) =
      base := by
  exact sourceH1Orbit_one src dst base

end ABO
end PSTSEPPA
