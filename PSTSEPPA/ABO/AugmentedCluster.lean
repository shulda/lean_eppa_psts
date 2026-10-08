import PSTSEPPA.ABO.ClusterComponentGraph

/-!
# ABO augmented clusters

For an A-cluster CL(G[A], P), a vertex v and a subalphabet B, ABO define the
B-augmentation at v literally inside the ambient Cayley graph as

  CL(G[A], P) ∪ v G[B].

This file records that union on vertices and directed edge tokens, proves that
it is a labelled subgraph, and isolates the degenerate case in which the
attached B-coset was already a full B-component of the cluster.

The definitions themselves are slightly more general than the source-facing
use: properness of B ⊂ A and membership of v in the original cluster are
hypotheses of the later structural theorems rather than fields of the data.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

namespace ClusterSpec

variable {A : Finset ι}

/-- Vertices of the B-augmentation of the cluster at v. -/
def AugmentedVertexSet
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) : Set Γ :=
  P.VertexSet gen ∪ generatedLeftCoset gen B v

/-- Directed edges of the B-augmentation of the cluster at v. -/
def AugmentedEdgeSet
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) : Set (ActionEdge Γ ι) :=
  P.EdgeSet gen ∪ FullCosetEdgeSet gen B v

abbrev AugmentedVertex
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) :=
  {x : Γ // x ∈ P.AugmentedVertexSet gen B v}

abbrev AugmentedEdge
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) :=
  {e : ActionEdge Γ ι // e ∈ P.AugmentedEdgeSet gen B v}

/-- A B-labelled Cayley edge starting in a left B-coset also ends in the
same left B-coset. -/
theorem fullCosetEdge_target_mem
    (gen : ι → Γ) (B : Finset ι) (v : Γ)
    {e : ActionEdge Γ ι}
    (he : e ∈ FullCosetEdgeSet gen B v) :
    (cayleyGraph gen).target e ∈ generatedLeftCoset gen B v := by
  rcases e with ⟨x, s⟩
  rcases he with ⟨hxB, hsB⟩
  change v⁻¹ * x ∈ generatedSubgroup gen B at hxB
  change signedBase s ∈ B at hsB
  rw [cayleyGraph.target_eq_mul_evalGroupLetter]
  change
    v⁻¹ * (x * PSTS.SignedWord.evalGroupLetter gen s) ∈
      generatedSubgroup gen B
  rw [← mul_assoc]
  apply (generatedSubgroup gen B).mul_mem hxB
  cases s with
  | pos i =>
      exact generator_mem_generatedSubgroup gen B hsB
  | neg i =>
      exact
        (generatedSubgroup gen B).inv_mem
          (generator_mem_generatedSubgroup gen B hsB)

/-- Full B-coset edge membership is closed under formal edge reversal. -/
theorem fullCosetEdge_inv_mem
    (gen : ι → Γ) (B : Finset ι) (v : Γ)
    {e : ActionEdge Γ ι}
    (he : e ∈ FullCosetEdgeSet gen B v) :
    (cayleyGraph gen).inv e ∈ FullCosetEdgeSet gen B v := by
  refine ⟨?_, ?_⟩
  · rw [(cayleyGraph gen).source_inv]
    exact fullCosetEdge_target_mem gen B v he
  · rw [(cayleyGraph gen).label_inv_eq]
    simpa using he.2

/-- Sources of augmented-cluster edges are augmented-cluster vertices. -/
theorem augmented_edge_source_mem
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    {e : ActionEdge Γ ι}
    (he : e ∈ P.AugmentedEdgeSet gen B v) :
    (cayleyGraph gen).source e ∈ P.AugmentedVertexSet gen B v := by
  rcases he with he | he
  · exact Or.inl (P.edge_source_mem gen he)
  · exact Or.inr he.1

/-- Targets of augmented-cluster edges are augmented-cluster vertices. -/
theorem augmented_edge_target_mem
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    {e : ActionEdge Γ ι}
    (he : e ∈ P.AugmentedEdgeSet gen B v) :
    (cayleyGraph gen).target e ∈ P.AugmentedVertexSet gen B v := by
  rcases he with he | he
  · exact Or.inl (P.edge_target_mem gen he)
  · exact Or.inr (fullCosetEdge_target_mem gen B v he)

/-- Augmented-cluster edge membership is closed under formal edge reversal. -/
theorem augmented_edge_inv_mem
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    {e : ActionEdge Γ ι}
    (he : e ∈ P.AugmentedEdgeSet gen B v) :
    (cayleyGraph gen).inv e ∈ P.AugmentedEdgeSet gen B v := by
  rcases he with he | he
  · exact Or.inl (P.edge_inv_mem gen he)
  · exact Or.inr (fullCosetEdge_inv_mem gen B v he)

/-- The literal labelled graph underlying an augmented cluster. -/
noncomputable def augmentedToLabelledGraph
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) :
    LabelledGraph
      (P.AugmentedVertex gen B v)
      (P.AugmentedEdge gen B v) ι where
  source e :=
    ⟨(cayleyGraph gen).source e.1,
      P.augmented_edge_source_mem gen B v e.2⟩
  inv e :=
    ⟨(cayleyGraph gen).inv e.1,
      P.augmented_edge_inv_mem gen B v e.2⟩
  inv_inv e := by
    apply Subtype.ext
    exact (cayleyGraph gen).inv_inv e.1
  inv_ne e h := by
    apply (cayleyGraph gen).inv_ne e.1
    exact congrArg Subtype.val h
  label e := (cayleyGraph gen).label e.1
  label_inv e :=
    (cayleyGraph gen).label_inv e.1

/-- Canonical inclusion of an augmented cluster into the ambient Cayley graph. -/
noncomputable def augmentedInclusion
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) :
    LabelledGraphHom
      (P.augmentedToLabelledGraph gen B v)
      (cayleyGraph gen).toEGraph.toLabelledGraph where
  onVertex x := x.1
  onEdge e := e.1
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

@[simp]
theorem augmentedInclusion_onVertex
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (x : P.AugmentedVertex gen B v) :
    (P.augmentedInclusion gen B v).onVertex x = x.1 :=
  rfl

@[simp]
theorem augmentedInclusion_onEdge
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (e : P.AugmentedEdge gen B v) :
    (P.augmentedInclusion gen B v).onEdge e = e.1 :=
  rfl

/-- The original cluster embeds canonically in every augmentation. -/
noncomputable def clusterToAugmentedHom
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) :
    LabelledGraphHom
      (P.toLabelledGraph gen)
      (P.augmentedToLabelledGraph gen B v) where
  onVertex x := ⟨x.1, Or.inl x.2⟩
  onEdge e := ⟨e.1, Or.inl e.2⟩
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

/-- Vertex slice of an augmented cluster inside an ambient C-coset. -/
def AugmentedComponentSlice
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (C : Finset ι) (u : Γ) : Set Γ :=
  P.AugmentedVertexSet gen B v ∩
    generatedLeftCoset gen C u

/-- C-labelled directed-edge slice of an augmented cluster in an ambient
C-coset. -/
def AugmentedComponentEdgeSlice
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (C : Finset ι) (u : Γ) : Set (ActionEdge Γ ι) :=
  {e |
    e ∈ P.AugmentedEdgeSet gen B v ∧
    (cayleyGraph gen).source e ∈ generatedLeftCoset gen C u ∧
    signedBase ((cayleyGraph gen).label e) ∈ C}

/-- If the chosen B-component of the original cluster was already the whole
ambient B-coset, B-augmentation adds no vertices. -/
theorem augmentedVertexSet_eq_of_full_component
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (hfull :
      P.ComponentSlice gen B v =
        generatedLeftCoset gen B v) :
    P.AugmentedVertexSet gen B v = P.VertexSet gen := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hx | hx
    · exact hx
    · have hs :
          x ∈ P.ComponentSlice gen B v := by
        rw [hfull]
        exact hx
      exact hs.1
  · exact Set.subset_union_left

/-- In the same degenerate case, if the directed component slice is the full
coset edge set, augmentation adds no edges either. -/
theorem augmentedEdgeSet_eq_of_full_component
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (hfull :
      P.ComponentEdgeSlice gen B v =
        FullCosetEdgeSet gen B v) :
    P.AugmentedEdgeSet gen B v = P.EdgeSet gen := by
  apply Set.Subset.antisymm
  · intro e he
    rcases he with he | he
    · exact he
    · have hs :
          e ∈ P.ComponentEdgeSlice gen B v := by
        rw [hfull]
        exact he
      exact hs.1
  · exact Set.subset_union_left

/-- Graph-data version of the source's degenerate augmentation convention:
attaching a B-coset along a component which is already the full B-coset
changes neither vertices nor directed edges. -/
theorem augmented_eq_of_full_component
    (gen : ι → Γ) (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (hfullV :
      P.ComponentSlice gen B v =
        generatedLeftCoset gen B v)
    (hfullE :
      P.ComponentEdgeSlice gen B v =
        FullCosetEdgeSet gen B v) :
    P.AugmentedVertexSet gen B v = P.VertexSet gen ∧
      P.AugmentedEdgeSet gen B v = P.EdgeSet gen :=
  ⟨P.augmentedVertexSet_eq_of_full_component gen B v hfullV,
    P.augmentedEdgeSet_eq_of_full_component gen B v hfullE⟩

end ClusterSpec

end ABO
end PSTSEPPA
