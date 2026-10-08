import PSTSEPPA.ABO.CosetConnectivity
import PSTSEPPA.ABO.Morphisms

/-!
# Arbitrary labelled subgraphs of a Cayley graph

The cluster construction uses very special unions of subgroup Cayley graphs.
For ABO Definition 3.16 and the subsequent coset extensions we also need
arbitrary skeleton graphs K embedded in G[A].

This file introduces an A-labelled Cayley subgraph with both vertex and
directed edge sets, including formal inverse edges, and the reachability
relation by realised paths using only a chosen subalphabet.

In particular, every such path stays in its ambient subalphabet coset.
No completeness or connectedness assumption is built into the structure.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- An arbitrary A-labelled subgraph of a Cayley graph, literal on both
vertices and directed edge tokens. -/
structure CayleySubgraphSpec (gen : ι → Γ) (A : Finset ι) where
  vertices : Set Γ
  edges : Set (ActionEdge Γ ι)
  source_mem : ∀ e ∈ edges, (cayleyGraph gen).source e ∈ vertices
  inv_mem : ∀ e ∈ edges, (cayleyGraph gen).inv e ∈ edges
  label_mem : ∀ e ∈ edges,
    signedBase ((cayleyGraph gen).label e) ∈ A

namespace CayleySubgraphSpec

variable {gen : ι → Γ} {A : Finset ι}
variable (K : CayleySubgraphSpec gen A)

/-- Edge targets belong to the skeleton whenever sources do, by
closure under formal edge reversal. -/
theorem target_mem
    {e : ActionEdge Γ ι} (he : e ∈ K.edges) :
    (cayleyGraph gen).target e ∈ K.vertices := by
  have h :=
    K.source_mem ((cayleyGraph gen).inv e) (K.inv_mem e he)
  simpa only [(cayleyGraph gen).source_inv] using h

abbrev Vertex := {x : Γ // x ∈ K.vertices}
abbrev Edge := {e : ActionEdge Γ ι // e ∈ K.edges}

/-- The literal labelled skeleton graph. -/
noncomputable def toLabelledGraph :
    LabelledGraph K.Vertex K.Edge ι where
  source e :=
    ⟨(cayleyGraph gen).source e.1, K.source_mem e.1 e.2⟩
  inv e :=
    ⟨(cayleyGraph gen).inv e.1, K.inv_mem e.1 e.2⟩
  inv_inv e := by
    apply Subtype.ext
    exact (cayleyGraph gen).inv_inv e.1
  inv_ne e h := by
    apply (cayleyGraph gen).inv_ne e.1
    exact congrArg Subtype.val h
  label e := (cayleyGraph gen).label e.1
  label_inv e := (cayleyGraph gen).label_inv e.1

/-- Determinism of the skeleton follows from determinism of the ambient
complete Cayley graph. -/
noncomputable def toEGraph :
    EGraph K.Vertex K.Edge ι where
  toLabelledGraph := K.toLabelledGraph
  deterministic := by
    intro e f hs hl
    apply Subtype.ext
    have hsource :
        (cayleyGraph gen).source e.1 =
          (cayleyGraph gen).source f.1 :=
      congrArg Subtype.val hs
    exact (cayleyGraph gen).toEGraph.deterministic hsource hl

/-- The canonical inclusion of a Cayley skeleton into its ambient graph. -/
noncomputable def inclusion :
    LabelledGraphHom
      (K.toEGraph).toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph where
  onVertex x := x.1
  onEdge e := e.1
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

/-- A path inside the skeleton, with every edge label in a chosen alphabet. -/
def SubalphabetReachable
    (C : Finset ι) (x y : K.Vertex) : Prop :=
  ∃ w : LabelWord ι,
    LabelWord.Uses C w ∧
      K.toEGraph.Follows x w y

theorem subalphabetReachable_refl
    (C : Finset ι) (x : K.Vertex) :
    K.SubalphabetReachable C x x :=
  ⟨[], by simp, EGraph.Follows.nil x⟩

/-- Every realised C-path within a skeleton remains in the ambient left
C-coset of its source.  This is the key compatibility between intrinsic
skeleton components and the algebraic cosets used in ABO. -/
theorem subalphabetReachable_implies_coset
    (C : Finset ι) (x y : K.Vertex)
    (h : K.SubalphabetReachable C x y) :
    y.1 ∈ generatedLeftCoset gen C x.1 := by
  rcases h with ⟨w, hwC, hwPath⟩
  have hMapped :
      (cayleyGraph gen).toEGraph.Follows x.1 w y.1 :=
    hwPath.map K.inclusion
  have hCanonical :
      (cayleyGraph gen).toEGraph.Follows
        x.1 w ((cayleyGraph gen).followWord x.1 w) :=
    (cayleyGraph gen).follows_followWord x.1 w
  have hend :
      (cayleyGraph gen).followWord x.1 w = y.1 :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      hCanonical hMapped
  exact
    (mem_generatedLeftCoset_iff_subalphabetReachable gen C x.1 y.1).2
      ⟨w, hwC, hend⟩

end CayleySubgraphSpec

end ABO
end PSTSEPPA
