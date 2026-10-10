import PSTSEPPA.ABO.AugmentedCluster
import PSTSEPPA.ABO.Morphisms
import PSTSEPPA.ABO.CayleySubgraph

/-!
# Attaching a literal full coset to an isolated E-graph vertex

Corrected ABO Definition 5.3 type (2) augments a full coset
extension along an intrinsic B-component. In the rank-two R2
base, a non-full selected B-component is a singleton. The
rank-two edge-source theorem additionally guarantees that
no old B-labelled edge (even a geometric loop) leaves it.

This file constructs the corresponding FULL B-COSET GLUING
as a *real deterministic EGraph*, not as a proposed graph.
Keep every old vertex/edge, and take a separately tagged
copy of the ambient gG[B] with g identified with the
chosen old root and NO other identifications. Attach all
signed B-edges, with their genuine formal inverses.

The missing-edge assumption is exactly what ensures that
old and new outgoing edges do not violate determinism at
the identified root. It is proved for the relevant rank-two
multi-coset extension separately.

The vertex/edge types need not be finite here; finiteness,
trivial completion and singleton-word kernels are subsequent
stages of the type-(2) construction.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

open ClusterSpec

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

abbrev CosetPoint (gen : ι → Γ) (B : Finset ι) (g : Γ) :=
  {x : Γ // x ∈ generatedLeftCoset gen B g}

abbrev FreshPoint (gen : ι → Γ) (B : Finset ι) (g : Γ) :=
  {x : Γ // x ∈ generatedLeftCoset gen B g ∧ x ≠ g}

abbrev Vertex (V : Type*) (gen : ι → Γ) (B : Finset ι) (g : Γ) :=
  V ⊕ FreshPoint gen B g

abbrev CosetEdge (gen : ι → Γ) (B : Finset ι) (g : Γ) :=
  {e : ActionEdge Γ ι // e ∈ FullCosetEdgeSet gen B g}

abbrev Edge (OldEdge : Type*) (gen : ι → Γ)
    (B : Finset ι) (g : Γ) :=
  OldEdge ⊕ CosetEdge gen B g

/-- Embed the attached full coset: its basepoint g becomes
the chosen old root; all other coset points are fresh. -/
noncomputable def gluePoint
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (p : CosetPoint gen B g) : Vertex V gen B g := by
  classical
  exact if h : p.1 = g then .inl root
    else .inr ⟨p.1, p.2, h⟩

theorem gluePoint_inl_eq_root
    (gen : ι → Γ) (B : Finset ι) (g : Γ)
    (root v : V) (p : CosetPoint gen B g)
    (h : gluePoint gen B g root p = Sum.inl v) :
    v = root := by
  classical
  by_cases hp : p.1 = g
  · simpa [gluePoint, hp] using h.symm
  · simp [gluePoint, hp] at h

/-- No distinct points in the newly attached full coset
are collapsed. In particular the basepoint is the only
point identified with an existing old vertex. -/
theorem gluePoint_injective
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V) :
    Function.Injective (gluePoint gen B g root) := by
  classical
  intro p q hpq
  by_cases hp : p.1 = g
  · by_cases hq : q.1 = g
    · exact Subtype.ext (hp.trans hq.symm)
    · simp [gluePoint, hp, hq] at hpq
  · by_cases hq : q.1 = g
    · simp [gluePoint, hp, hq] at hpq
    · have hsub :
          (⟨p.1, p.2, hp⟩ : FreshPoint gen B g) =
            (⟨q.1, q.2, hq⟩ : FreshPoint gen B g) := by
        simpa [gluePoint, hp, hq] using hpq
      have hval : p.1 = q.1 :=
        congrArg (fun z : FreshPoint gen B g => z.1) hsub
      exact Subtype.ext hval

/-- The actual full B-coset as an oriented labelled
Cayley subgraph. Both formal edge directions survive. -/
def fullCosetSubgraph
    (gen : ι → Γ) (B : Finset ι) (g : Γ) :
    CayleySubgraphSpec gen B where
  vertices := generatedLeftCoset gen B g
  edges := FullCosetEdgeSet gen B g
  source_mem := by
    intro e he
    exact he.1
  inv_mem := by
    intro e he
    exact fullCosetEdge_inv_mem gen B g he
  label_mem := by
    intro e he
    exact he.2

/-- The literal old edges and the fresh coset edges
have separate tokens. The same signed generator may
occur at two different points, but never twice at one
point of the glued graph. -/
noncomputable def gluedEGraph
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B) :
    EGraph (Vertex V gen B g) (Edge OldEdge gen B g) ι where
  source e :=
    match e with
    | .inl e => .inl (G.source e)
    | .inr e =>
        gluePoint gen B g root
          ⟨(cayleyGraph gen).source e.1, e.2.1⟩
  inv e :=
    match e with
    | .inl e => .inl (G.inv e)
    | .inr e =>
        .inr ⟨(cayleyGraph gen).inv e.1,
          fullCosetEdge_inv_mem gen B g e.2⟩
  inv_inv := by
    intro e
    cases e with
    | inl e =>
        exact congrArg Sum.inl (G.inv_inv e)
    | inr e =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact (cayleyGraph gen).inv_inv e.1
  inv_ne := by
    intro e h
    cases e with
    | inl e =>
        exact G.inv_ne e (Sum.inl.inj h)
    | inr e =>
        apply (cayleyGraph gen).inv_ne e.1
        exact congrArg Subtype.val (Sum.inr.inj h)
  label e :=
    match e with
    | .inl e => G.label e
    | .inr e => (cayleyGraph gen).label e.1
  label_inv := by
    intro e
    cases e with
    | inl e => exact G.label_inv e
    | inr e => exact (cayleyGraph gen).label_inv e.1
  deterministic := by
    intro e f hs hl
    cases e with
    | inl e =>
        cases f with
        | inl f =>
            exact congrArg Sum.inl
              (G.deterministic (Sum.inl.inj hs) hl)
        | inr f =>
            have hroot : G.source e = root :=
              (gluePoint_inl_eq_root gen B g root
                (G.source e)
                ⟨(cayleyGraph gen).source f.1, f.2.1⟩
                hs.symm)
            have hlabel :
                G.label e = (cayleyGraph gen).label f.1 := hl
            have hb : signedBase (G.label e) ∈ B := by
              rw [hlabel]
              exact f.2.2
            exact False.elim (hMissing e hroot hb)
    | inr e =>
        cases f with
        | inl f =>
            have hroot : G.source f = root :=
              gluePoint_inl_eq_root gen B g root
                (G.source f)
                ⟨(cayleyGraph gen).source e.1, e.2.1⟩ hs
            have hlabel :
                (cayleyGraph gen).label e.1 = G.label f := hl
            have hb : signedBase (G.label f) ∈ B := by
              rw [← hlabel]
              exact e.2.2
            exact False.elim (hMissing f hroot hb)
        | inr f =>
            have hpoints :
                (⟨(cayleyGraph gen).source e.1, e.2.1⟩ :
                  CosetPoint gen B g) =
                (⟨(cayleyGraph gen).source f.1, f.2.1⟩ :
                  CosetPoint gen B g) :=
              (gluePoint_injective gen B g root) hs
            have hsrc :
                (cayleyGraph gen).source e.1 =
                  (cayleyGraph gen).source f.1 :=
              congrArg Subtype.val hpoints
            have hedge : e.1 = f.1 :=
              (cayleyGraph gen).toEGraph.deterministic hsrc hl
            exact congrArg Sum.inr (Subtype.ext hedge)

/-- The original incomplete EGraph embeds with exactly
its old vertices, edges, signed labels and formal inverses.
It is not silently replaced by its loop completion. -/
noncomputable def oldHom
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B) :
    LabelledGraphHom G.toLabelledGraph
      (gluedEGraph G gen B g root hMissing).toLabelledGraph where
  onVertex := Sum.inl
  onEdge := Sum.inl
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

/-- The entire attached full B-coset embeds as a labelled
graph. Its only old vertex is the identified basepoint. -/
noncomputable def cosetHom
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B) :
    LabelledGraphHom
      ((fullCosetSubgraph gen B g).toEGraph).toLabelledGraph
      (gluedEGraph G gen B g root hMissing).toLabelledGraph where
  onVertex := gluePoint gen B g root
  onEdge := Sum.inr
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

end IsolatedCosetGluing
end ABO
end PSTSEPPA
