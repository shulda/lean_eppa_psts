import PSTSEPPA.ABO.ConnectedCayleyCoverTranslation

/-!
# Left-translated quotient pullbacks of genuine incomplete Cayley skeletons

For a labelled group quotient Q : H ↠ Γ and a genuine incomplete
Γ-Cayley A-skeleton K, the canonical pullback uses Q(h) ∈ K.
A general connected labelled Cayley-cover morphism f need only agree
with Q UP TO LEFT TRANSLATION by a constant c ∈ Γ.

We therefore construct the TRUE translated pullback:
  vertices = {h ∈ H | c·Q(h) ∈ K.vertices},
  edges = {(h,s) | (c·Q(h),s) ∈ K.edges}.

It is a literal H-Cayley subgraph with formal signed inverses, and
its canonical map to K is a surjective labelled graph morphism.
Every old directed edge has an actual lift above EVERY selected
source preimage. This is not a completion of missing edges.

These constructions are an interface for the connected-morphism
normalization of the previously certified theorem #329, and not
a claim that the source's entire Y₁/Z₁ catalogue has been covered.
-/

namespace PSTSEPPA
namespace ABO

variable {ι H Γ : Type*} [Fintype ι] [DecidableEq ι]
variable [Group H] [Group Γ]
variable {genH : ι → H} {genΓ : ι → Γ} {A : Finset ι}

namespace LabelledGroupQuotient

variable (Q : LabelledGroupQuotient genH genΓ)

/-- Both signed directions of right Cayley edges commute with
first applying Q and then left multiplying by a fixed c. -/
theorem leftTranslate_map_cayley_inv
    (c : Γ) (e : ActionEdge H ι) :
    (c * Q.hom ((cayleyGraph genH).inv e).1,
      ((cayleyGraph genH).inv e).2) =
      (cayleyGraph genΓ).inv (c * Q.hom e.1, e.2) := by
  rcases e with ⟨h, s⟩
  cases s with
  | pos i =>
      apply Prod.ext
      · change c * Q.hom (h * genH i) =
          (c * Q.hom h) * genΓ i
        rw [map_mul, Q.map_gen]
        simp only [mul_assoc]
      · rfl
  | neg i =>
      apply Prod.ext
      · change c * Q.hom (h * (genH i)⁻¹) =
          (c * Q.hom h) * (genΓ i)⁻¹
        rw [map_mul, map_inv, Q.map_gen]
        simp only [mul_assoc]
      · rfl

end LabelledGroupQuotient

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec genΓ A)
variable (Q : LabelledGroupQuotient genH genΓ)

/-- Exact incomplete Cayley pullback after a target-side left translation.
The old vertices and signed edges are selected LITERALLY. -/
def translatedPullbackQuotient (c : Γ) :
    CayleySubgraphSpec genH A where
  vertices := {h : H | c * Q.hom h ∈ K.vertices}
  edges := {e : ActionEdge H ι |
    (c * Q.hom e.1, e.2) ∈ K.edges}
  source_mem := by
    intro e he
    have hsrc := K.source_mem (c * Q.hom e.1, e.2) he
    change c * Q.hom e.1 ∈ K.vertices
    exact hsrc
  inv_mem := by
    intro e he
    change
      (c * Q.hom ((cayleyGraph genH).inv e).1,
        ((cayleyGraph genH).inv e).2) ∈ K.edges
    rw [Q.leftTranslate_map_cayley_inv c e]
    exact K.inv_mem _ he
  label_mem := by
    intro e he
    have h := K.label_mem (c * Q.hom e.1, e.2) he
    change signedBase e.2 ∈ A
    exact h

/-- Its canonical map preserves true vertices, signed edge tokens,
formal inversion and labels. -/
noncomputable def translatedPullbackQuotientHom (c : Γ) :
    LabelledGraphHom
      ((K.translatedPullbackQuotient Q c).toEGraph).toLabelledGraph
      (K.toEGraph).toLabelledGraph where
  onVertex x := ⟨c * Q.hom x.1, x.2⟩
  onEdge e := ⟨(c * Q.hom e.1.1, e.1.2), e.2⟩
  map_source := by
    intro e
    apply Subtype.ext
    rfl
  map_inv := by
    intro e
    apply Subtype.ext
    exact Q.leftTranslate_map_cayley_inv c e.1
  map_label := by
    intro e
    rfl

/-- Each original vertex has a genuine lift, since Q is
surjective and left multiplication by c is bijective. -/
theorem translatedPullbackQuotientHom_vertex_surjective
    (c : Γ) :
    Function.Surjective (K.translatedPullbackQuotientHom Q c).onVertex := by
  intro y
  obtain ⟨h, hh⟩ := Q.surjective (c⁻¹ * y.1)
  have hxy : c * Q.hom h = y.1 := by
    rw [hh]
    simp [mul_assoc]
  have hmem : h ∈ (K.translatedPullbackQuotient Q c).vertices := by
    change c * Q.hom h ∈ K.vertices
    rw [hxy]
    exact y.2
  refine ⟨⟨h, hmem⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- Every real directed K-edge lifts at each chosen preimage of its
source. This is a strong local covering property, not merely
surjectivity of the underlying vertex map. -/
theorem translatedPullbackQuotientHom_edge_lift
    (c : Γ)
    (e : K.Edge)
    (x : (K.translatedPullbackQuotient Q c).Vertex)
    (hx : (K.translatedPullbackQuotientHom Q c).onVertex x =
      (K.toEGraph).source e) :
    ∃ f : (K.translatedPullbackQuotient Q c).Edge,
      ((K.translatedPullbackQuotient Q c).toEGraph).source f = x ∧
      (K.translatedPullbackQuotientHom Q c).onEdge f = e := by
  have hsrc : c * Q.hom x.1 = e.1.1 :=
    congrArg (fun y : K.Vertex => y.1) hx
  have hmem : (x.1, e.1.2) ∈
      (K.translatedPullbackQuotient Q c).edges := by
    change (c * Q.hom x.1, e.1.2) ∈ K.edges
    rw [hsrc]
    exact e.2
  refine ⟨⟨(x.1, e.1.2), hmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    exact Prod.ext hsrc rfl

/-- Every actual signed edge of K is hit by the
translated-pullback cover, not by any invented new edge. -/
theorem translatedPullbackQuotientHom_edge_surjective
    (c : Γ) :
    Function.Surjective (K.translatedPullbackQuotientHom Q c).onEdge := by
  intro e
  obtain ⟨x, hx⟩ :=
    K.translatedPullbackQuotientHom_vertex_surjective Q c
      ((K.toEGraph).source e)
  obtain ⟨f, _, hf⟩ :=
    K.translatedPullbackQuotientHom_edge_lift Q c e x hx
  exact ⟨f, hf⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
