import PSTSEPPA.ABO.RetractabilityRetraction

/-!
# Source-facing form of ABO Proposition 3.3

ABO Definition 3.1 speaks of a canonical Cayley cover without fixing the image
of the identity vertex.  For a Cayley target, any such cover can be normalized
by left translation so that 1 maps to 1.  Thus the based formulation used in
the algebraic proof is equivalent to the source formulation.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Source-style cover data: a surjective labelled morphism, with no chosen
basepoint normalization. -/
structure UnbasedTrivialCompletionCover
    (gen : ι → Γ) (A : Finset ι) where
  hom :
    LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      (cayleyGraph (trivialCompletionGenerator gen A)).toEGraph.toLabelledGraph
  vertex_surjective : Function.Surjective hom.onVertex

/-- Left multiplication is a labelled automorphism of a Cayley graph because
labels act on the right. -/
noncomputable def leftTranslateCayleyHom
    {Δ : Type*} [Group Δ]
    (gen : ι → Δ) (d : Δ) :
    LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph where
  onVertex := fun x => d * x
  onEdge := fun e => (d * e.1, e.2)
  map_source := by
    rintro ⟨g, s⟩
    rfl
  map_label := by
    rintro ⟨g, s⟩
    rfl
  map_inv := by
    rintro ⟨g, s⟩
    apply Prod.ext
    · change
        d * (cayleyGraph gen).target (g, s) =
          (cayleyGraph gen).target (d * g, s)
      rw [cayleyGraph.target_eq_mul_evalGroupLetter,
        cayleyGraph.target_eq_mul_evalGroupLetter]
      simp [mul_assoc]
    · rfl

/-- Left translation on a Cayley graph is surjective on vertices. -/
theorem leftTranslateCayleyHom_vertex_surjective
    {Δ : Type*} [Group Δ]
    (gen : ι → Δ) (d : Δ) :
    Function.Surjective (leftTranslateCayleyHom gen d).onVertex := by
  intro y
  refine ⟨d⁻¹ * y, ?_⟩
  simp [leftTranslateCayleyHom, mul_assoc]

/-- Forget the based normalization. -/
def TrivialCompletionCover.toUnbased
    {gen : ι → Γ} {A : Finset ι}
    (C : TrivialCompletionCover gen A) :
    UnbasedTrivialCompletionCover gen A where
  hom := C.hom
  vertex_surjective := C.vertex_surjective

/-- Normalize an arbitrary source-style cover so that the identity vertex maps
to the identity vertex. -/
noncomputable def UnbasedTrivialCompletionCover.normalize
    {gen : ι → Γ} {A : Finset ι}
    (C : UnbasedTrivialCompletionCover gen A) :
    TrivialCompletionCover gen A := by
  let u : generatedSubgroup gen A := C.hom.onVertex 1
  let L :=
    leftTranslateCayleyHom
      (trivialCompletionGenerator gen A) u⁻¹
  exact
    { hom := LabelledGraphHom.comp L C.hom
      map_one := by
        change u⁻¹ * C.hom.onVertex 1 = 1
        change u⁻¹ * u = 1
        simp
      vertex_surjective := by
        intro y
        rcases C.vertex_surjective (u * y) with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        change u⁻¹ * C.hom.onVertex x = y
        rw [hx]
        simp [mul_assoc] }

/-- Existence of a based trivial-completion cover is equivalent to the
source-style unbased notion. -/
theorem nonempty_trivialCompletionCover_iff_unbased
    (gen : ι → Γ) (A : Finset ι) :
    Nonempty (TrivialCompletionCover gen A) ↔
      Nonempty (UnbasedTrivialCompletionCover gen A) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.toUnbased⟩
  · rintro ⟨C⟩
    exact ⟨C.normalize⟩

/-- ABO Proposition 3.3 in the source-facing cover formulation. -/
theorem retractable_iff_source_trivialCompletionCovers
    (gen : ι → Γ) (hgen : IsGenerated gen) :
    Retractable gen ↔
      ∀ A : Finset ι,
        Nonempty (UnbasedTrivialCompletionCover gen A) := by
  constructor
  · intro hret A
    have hb :
        Nonempty (TrivialCompletionCover gen A) :=
      (retractable_iff_trivialCompletionCovers gen hgen).mp hret A
    exact
      (nonempty_trivialCompletionCover_iff_unbased gen A).mp hb
  · intro hcovers
    apply (retractable_iff_trivialCompletionCovers gen hgen).mpr
    intro A
    exact
      (nonempty_trivialCompletionCover_iff_unbased gen A).mpr
        (hcovers A)

end ABO
end PSTSEPPA
