import PSTSEPPA.ABO.Morphisms

/-!
# Transport of complete signed word-action kernels through graph morphisms

A map of genuinely complete labelled E-graphs commutes with following
ANY chronological signed word, by `CompleteEGraph.hom_followWord`.

Surjectivity on vertices therefore transfers an equality of complete
word actions FROM a local stage TO its original source stage.
Injectivity transfers the same equality in the reverse direction.
For a vertex-bijective signed graph isomorphism the two action
word kernels agree exactly. No group-coordinate injectivity or
unproved properties of coset completion are assumed.

This is the precise generic interface needed to lift established
finite G₂ kernels of the local type-(2) completed augmentations to
the TRUE source H₁ stage when the named source/local complete-action
identification has been discharged separately.
-/

namespace PSTSEPPA
namespace ABO

namespace CompleteEGraph

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable (G : CompleteEGraph V₁ E₁ ι)
variable (H : CompleteEGraph V₂ E₂ ι)

/-- A vertex-surjective labelled homomorphism sends an equality of
two entire signed word actions from the source complete stage to
the target complete stage. No edge-surjectivity is needed. -/
theorem wordActionCongr_of_surjectiveHom
    (f : LabelledGraphHom
      G.toEGraph.toLabelledGraph H.toEGraph.toLabelledGraph)
    (hf : Function.Surjective f.onVertex)
    (w₁ w₂ : LabelWord ι)
    (hw : ∀ x : V₁, G.followWord x w₁ = G.followWord x w₂) :
    ∀ y : V₂, H.followWord y w₁ = H.followWord y w₂ := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  calc
    H.followWord (f.onVertex x) w₁ =
        f.onVertex (G.followWord x w₁) := G.hom_followWord H f x w₁
    _ = f.onVertex (G.followWord x w₂) := congrArg f.onVertex (hw x)
    _ = H.followWord (f.onVertex x) w₂ :=
      (G.hom_followWord H f x w₂).symm

/-- An injective labelled graph homomorphism reflects equality of
whole completed signed-word actions back to its original stage. -/
theorem wordActionCongr_of_injectiveHom
    (f : LabelledGraphHom
      G.toEGraph.toLabelledGraph H.toEGraph.toLabelledGraph)
    (hf : Function.Injective f.onVertex)
    (w₁ w₂ : LabelWord ι)
    (hw : ∀ y : V₂, H.followWord y w₁ = H.followWord y w₂) :
    ∀ x : V₁, G.followWord x w₁ = G.followWord x w₂ := by
  intro x
  apply hf
  calc
    f.onVertex (G.followWord x w₁) =
        H.followWord (f.onVertex x) w₁ :=
      (G.hom_followWord H f x w₁).symm
    _ = H.followWord (f.onVertex x) w₂ := hw _
    _ = f.onVertex (G.followWord x w₂) := G.hom_followWord H f x w₂

/-- The entire signed-word action congruence, and hence its
identity-word kernel, is invariant under a vertex-bijective
labelled morphism of genuinely completed stages. -/
theorem wordActionCongr_iff_of_bijectiveHom
    (f : LabelledGraphHom
      G.toEGraph.toLabelledGraph H.toEGraph.toLabelledGraph)
    (hf : Function.Bijective f.onVertex)
    (w₁ w₂ : LabelWord ι) :
    (∀ x : V₁, G.followWord x w₁ = G.followWord x w₂) ↔
      (∀ y : V₂, H.followWord y w₁ = H.followWord y w₂) := by
  constructor
  · exact G.wordActionCongr_of_surjectiveHom H f hf.2 w₁ w₂
  · exact G.wordActionCongr_of_injectiveHom H f hf.1 w₁ w₂

end CompleteEGraph
end ABO
end PSTSEPPA
