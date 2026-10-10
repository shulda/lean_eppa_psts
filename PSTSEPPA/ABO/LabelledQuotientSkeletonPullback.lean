import PSTSEPPA.ABO.CayleySubgraphComponents
import PSTSEPPA.ABO.Stability

/-!
# Exact lifting of a genuine incomplete Cayley skeleton along a labelled group quotient

For a surjective, generator-preserving group homomorphism
   Q : H ↠ Γ,
and ANY genuine A-labelled Γ-Cayley subgraph K (not required
connected or complete), pull K back literally along Q.

The new H-Cayley skeleton has precisely the preimage vertices and
precisely the preimage REAL signed oriented edges, with all formal
inverse tokens retained. Its canonical map to K is surjective
on vertices and on oriented signed edges. More strongly, every
actual old signed edge has a unique lift at every chosen preimage
of its source; there are no extra edges in the pullback.

This is a useful geometric interface for the corrected ABO
Theorem-3.8 Y₁/H₁-cover construction: the algebraic finite
quotient can be converted into a labelled graph cover without
silently completing missing original edges.

The construction alone makes no claims about extra R2/R4
cluster geometry, global retractability or the full H₁-cover
catalogue Z₁, and does not yet implement the whole source Y₁.
-/

namespace PSTSEPPA
namespace ABO

variable {ι H Γ : Type*} [Fintype ι] [DecidableEq ι]
variable [Group H] [Group Γ]
variable {genH : ι → H} {genΓ : ι → Γ}

namespace LabelledGroupQuotient

variable (Q : LabelledGroupQuotient genH genΓ)

/-- A labelled group quotient commutes with the actual formal
inverse tokens of a right-multiplication Cayley action, for BOTH
positive and negative labels and even geometric loops. -/
theorem map_cayley_inv (e : ActionEdge H ι) :
    (Q.hom ((cayleyGraph genH).inv e).1,
      ((cayleyGraph genH).inv e).2) =
    (cayleyGraph genΓ).inv (Q.hom e.1, e.2) := by
  rcases e with ⟨x, s⟩
  cases s with
  | pos i =>
      apply Prod.ext
      · change Q.hom (x * genH i) = Q.hom x * genΓ i
        rw [map_mul, Q.map_gen]
      · rfl
  | neg i =>
      apply Prod.ext
      · change Q.hom (x * (genH i)⁻¹) = Q.hom x * (genΓ i)⁻¹
        rw [map_mul, map_inv, Q.map_gen]
      · rfl

end LabelledGroupQuotient

variable {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec genΓ A)
variable (Q : LabelledGroupQuotient genH genΓ)

/-- The LITERAL H-Cayley preimage of an actual incomplete
Γ-Cayley skeleton, with no completed edges and with original
signed labels unchanged. -/
def pullbackQuotient :
    CayleySubgraphSpec genH A where
  vertices := {x : H | Q.hom x ∈ K.vertices}
  edges := {e : ActionEdge H ι |
    (Q.hom e.1, e.2) ∈ K.edges}
  source_mem := by
    intro e he
    have hsrc := K.source_mem (Q.hom e.1, e.2) he
    change Q.hom e.1 ∈ K.vertices
    exact hsrc
  inv_mem := by
    intro e he
    change
      (Q.hom ((cayleyGraph genH).inv e).1,
        ((cayleyGraph genH).inv e).2) ∈ K.edges
    rw [Q.map_cayley_inv e]
    exact K.inv_mem _ he
  label_mem := by
    intro e he
    have h := K.label_mem (Q.hom e.1, e.2) he
    change signedBase e.2 ∈ A
    exact h

/-- The canonical quotient map on old vertices and REAL directed
signed edge tokens is a labelled graph morphism. -/
noncomputable def pullbackQuotientHom :
    LabelledGraphHom
      ((K.pullbackQuotient Q).toEGraph).toLabelledGraph
      (K.toEGraph).toLabelledGraph where
  onVertex x := ⟨Q.hom x.1, x.2⟩
  onEdge e := ⟨(Q.hom e.1.1, e.1.2), e.2⟩
  map_source := by
    intro e
    apply Subtype.ext
    rfl
  map_inv := by
    intro e
    apply Subtype.ext
    exact Q.map_cayley_inv e.1
  map_label := by
    intro e
    rfl

/-- Every original K vertex has a preimage: this is the genuine
vertex-surjectivity of the graph covering map, not a chosen
section or an assumed partial-automorphism lift. -/
theorem pullbackQuotientHom_vertex_surjective :
    Function.Surjective (K.pullbackQuotientHom Q).onVertex := by
  intro y
  obtain ⟨x, hx⟩ := Q.surjective y.1
  have hmem : x ∈ (K.pullbackQuotient Q).vertices := by
    change Q.hom x ∈ K.vertices
    rw [hx]
    exact y.2
  refine ⟨⟨x, hmem⟩, ?_⟩
  apply Subtype.ext
  exact hx

/-- At EVERY lift x of an old edge's source, the SAME
original signed edge has an actual pullback edge starting at x.
The endpoint then follows by the group-quotient identity. -/
theorem pullbackQuotientHom_edge_lift
    (e : K.Edge)
    (x : (K.pullbackQuotient Q).Vertex)
    (hx : (K.pullbackQuotientHom Q).onVertex x =
      (K.toEGraph).source e) :
    ∃ f : (K.pullbackQuotient Q).Edge,
      ((K.pullbackQuotient Q).toEGraph).source f = x ∧
      (K.pullbackQuotientHom Q).onEdge f = e := by
  have hsrc : Q.hom x.1 = e.1.1 :=
    congrArg (fun y : K.Vertex => y.1) hx
  have hmem : (x.1, e.1.2) ∈ (K.pullbackQuotient Q).edges := by
    change (Q.hom x.1, e.1.2) ∈ K.edges
    rw [hsrc]
    exact e.2
  refine ⟨⟨(x.1, e.1.2), hmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    exact Prod.ext hsrc rfl

/-- The quotient morphism is also surjective on ACTUAL signed
edge tokens, including both directions of loops or parallel labels. -/
theorem pullbackQuotientHom_edge_surjective :
    Function.Surjective (K.pullbackQuotientHom Q).onEdge := by
  intro e
  obtain ⟨x, hx⟩ :=
    K.pullbackQuotientHom_vertex_surjective Q ((K.toEGraph).source e)
  obtain ⟨f, _, hf⟩ :=
    K.pullbackQuotientHom_edge_lift Q e x hx
  exact ⟨f, hf⟩

/-- The directed signed-edge lift at a prescribed source is
UNIQUE: same old label and same lifted H-source force exactly
the same preimage edge token. This is stronger than mere
edge-surjectivity of a graph morphism. -/
theorem pullbackQuotientHom_edge_lift_unique
    (x : (K.pullbackQuotient Q).Vertex)
    (e : K.Edge)
    (f₁ f₂ : (K.pullbackQuotient Q).Edge)
    (hsource₁ : ((K.pullbackQuotient Q).toEGraph).source f₁ = x)
    (hsource₂ : ((K.pullbackQuotient Q).toEGraph).source f₂ = x)
    (hmap₁ : (K.pullbackQuotientHom Q).onEdge f₁ = e)
    (hmap₂ : (K.pullbackQuotientHom Q).onEdge f₂ = e) :
    f₁ = f₂ := by
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : (K.pullbackQuotient Q).Vertex => z.1)
      (hsource₁.trans hsource₂.symm)
  · have h₁ : f₁.1.2 = e.1.2 :=
      congrArg (fun z : K.Edge => z.1.2) hmap₁
    have h₂ : f₂.1.2 = e.1.2 :=
      congrArg (fun z : K.Edge => z.1.2) hmap₂
    exact h₁.trans h₂.symm

end CayleySubgraphSpec
end ABO
end PSTSEPPA
