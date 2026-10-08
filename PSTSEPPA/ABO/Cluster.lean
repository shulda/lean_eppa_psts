import PSTSEPPA.ABO.CosetConnectivity

/-!
# ABO clusters as labelled subgraphs

For a retractable labelled group and a family P of proper subalphabets of A,
the source defines

  CL(G[A], P) = ⋃_{B ∈ P} G[B].

This file represents that union literally as a labelled subgraph of the
ambient Cayley graph, on both vertices and directed edge tokens.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- A finite family of proper constituent alphabets for an A-cluster. -/
structure ClusterSpec (A : Finset ι) where
  pieces : Finset (Finset ι)
  proper : ∀ B ∈ pieces, B ⊂ A

namespace ClusterSpec

variable {A : Finset ι}

/-- Vertex set of the cluster: the union of the constituent subgroups. -/
def VertexSet (gen : ι → Γ) (P : ClusterSpec A) : Set Γ :=
  {x | ∃ B ∈ P.pieces, x ∈ generatedSubgroup gen B}

/-- Directed edges of the cluster: an ambient Cayley edge belongs precisely
when it lies in one constituent G[B]. -/
def EdgeSet (gen : ι → Γ) (P : ClusterSpec A) :
    Set (ActionEdge Γ ι) :=
  {e |
    ∃ B ∈ P.pieces,
      (cayleyGraph gen).source e ∈ generatedSubgroup gen B ∧
      signedBase ((cayleyGraph gen).label e) ∈ B}

abbrev Vertex (gen : ι → Γ) (P : ClusterSpec A) :=
  {x : Γ // x ∈ P.VertexSet gen}

abbrev Edge (gen : ι → Γ) (P : ClusterSpec A) :=
  {e : ActionEdge Γ ι // e ∈ P.EdgeSet gen}

theorem constituent_vertex_mem
    (gen : ι → Γ) (P : ClusterSpec A)
    {B : Finset ι} (hBP : B ∈ P.pieces)
    {x : Γ} (hx : x ∈ generatedSubgroup gen B) :
    x ∈ P.VertexSet gen :=
  ⟨B, hBP, hx⟩

theorem constituent_edge_mem
    (gen : ι → Γ) (P : ClusterSpec A)
    {B : Finset ι} (hBP : B ∈ P.pieces)
    {e : ActionEdge Γ ι}
    (hsource :
      (cayleyGraph gen).source e ∈ generatedSubgroup gen B)
    (hlabel :
      signedBase ((cayleyGraph gen).label e) ∈ B) :
    e ∈ P.EdgeSet gen :=
  ⟨B, hBP, hsource, hlabel⟩

/-- A Cayley edge whose source lies in G[B] and whose label lies in B also
has target in G[B]. -/
theorem target_mem_constituent
    (gen : ι → Γ) (B : Finset ι) (e : ActionEdge Γ ι)
    (hsource :
      (cayleyGraph gen).source e ∈ generatedSubgroup gen B)
    (hlabel :
      signedBase ((cayleyGraph gen).label e) ∈ B) :
    (cayleyGraph gen).target e ∈ generatedSubgroup gen B := by
  rcases e with ⟨x, s⟩
  change x ∈ generatedSubgroup gen B at hsource
  change signedBase s ∈ B at hlabel
  rw [cayleyGraph.target_eq_mul_evalGroupLetter]
  apply (generatedSubgroup gen B).mul_mem hsource
  cases s with
  | pos i =>
      exact generator_mem_generatedSubgroup gen B hlabel
  | neg i =>
      exact
        (generatedSubgroup gen B).inv_mem
          (generator_mem_generatedSubgroup gen B hlabel)

/-- Sources of cluster edges are cluster vertices. -/
theorem edge_source_mem
    (gen : ι → Γ) (P : ClusterSpec A)
    {e : ActionEdge Γ ι} (he : e ∈ P.EdgeSet gen) :
    (cayleyGraph gen).source e ∈ P.VertexSet gen := by
  rcases he with ⟨B, hBP, hs, hl⟩
  exact P.constituent_vertex_mem gen hBP hs

/-- Targets of cluster edges are cluster vertices. -/
theorem edge_target_mem
    (gen : ι → Γ) (P : ClusterSpec A)
    {e : ActionEdge Γ ι} (he : e ∈ P.EdgeSet gen) :
    (cayleyGraph gen).target e ∈ P.VertexSet gen := by
  rcases he with ⟨B, hBP, hs, hl⟩
  exact
    P.constituent_vertex_mem gen hBP
      (P.target_mem_constituent gen B e hs hl)

/-- Cluster edge membership is closed under formal edge reversal. -/
theorem edge_inv_mem
    (gen : ι → Γ) (P : ClusterSpec A)
    {e : ActionEdge Γ ι} (he : e ∈ P.EdgeSet gen) :
    (cayleyGraph gen).inv e ∈ P.EdgeSet gen := by
  rcases he with ⟨B, hBP, hs, hl⟩
  refine P.constituent_edge_mem gen hBP ?_ ?_
  · change
      (cayleyGraph gen).source ((cayleyGraph gen).inv e) ∈
        generatedSubgroup gen B
    rw [(cayleyGraph gen).source_inv]
    exact P.target_mem_constituent gen B e hs hl
  · rw [(cayleyGraph gen).label_inv_eq]
    simpa using hl

/-- The literal labelled graph underlying the cluster union. -/
noncomputable def toLabelledGraph
    (gen : ι → Γ) (P : ClusterSpec A) :
    LabelledGraph (P.Vertex gen) (P.Edge gen) ι where
  source e :=
    ⟨(cayleyGraph gen).source e.1,
      P.edge_source_mem gen e.2⟩
  inv e :=
    ⟨(cayleyGraph gen).inv e.1,
      P.edge_inv_mem gen e.2⟩
  inv_inv e := by
    apply Subtype.ext
    exact (cayleyGraph gen).inv_inv e.1
  inv_ne e h := by
    apply (cayleyGraph gen).inv_ne e.1
    exact congrArg Subtype.val h
  label e := (cayleyGraph gen).label e.1
  label_inv e :=
    (cayleyGraph gen).label_inv e.1

/-- Canonical inclusion of a cluster into the ambient Cayley graph. -/
noncomputable def inclusion
    (gen : ι → Γ) (P : ClusterSpec A) :
    LabelledGraphHom
      (P.toLabelledGraph gen)
      (cayleyGraph gen).toEGraph.toLabelledGraph where
  onVertex x := x.1
  onEdge e := e.1
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

@[simp]
theorem inclusion_onVertex
    (gen : ι → Γ) (P : ClusterSpec A) (x : P.Vertex gen) :
    (P.inclusion gen).onVertex x = x.1 :=
  rfl

@[simp]
theorem inclusion_onEdge
    (gen : ι → Γ) (P : ClusterSpec A) (e : P.Edge gen) :
    (P.inclusion gen).onEdge e = e.1 :=
  rfl

end ClusterSpec

end ABO
end PSTSEPPA
