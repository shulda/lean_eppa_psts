import PSTSEPPA.ABO.LabelledQuotientSkeletonPullback

/-!
# Injective labelled group quotient gives an exact signed Cayley-cover isomorphism

The existing arbitrary labelled group quotient Q : H ↠ Γ gives a literal
pullback of each ORIGINAL incomplete Γ-Cayley skeleton K. Both formal signed
edge tokens and all original vertices are preserved, and the pullback graph
maps surjectively to K.

If Q is ALSO injective, the cover is a genuine isomorphism on BOTH sorts:
its canonical vertex map is bijective and its oriented signed edge-token
map is bijective, including negative labels, geometric loops and repeated
or identity generator values. Crucially, this is a theorem about the
ACTUAL selected Cayley subgraphs and their edge tokens, not merely about
the ambient groups.

This generic API will transfer every genuine original-input H₁ preimage
skeleton to the literal T(Y₁) group presentation once the independently
verified generator-preserving isomorphism SourceH₁ ≃* T(Y₁) is available.
No geometry of augmented source Z₁ stages is assumed here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι H Γ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group H] [Group Γ]
variable {genH : ι → H} {genΓ : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

/-- A labelled quotient that is injective on its group is an exact
labelled isomorphism of the corresponding TRUE incomplete Cayley
pullback onto the old skeleton, on BOTH vertex and formal signed
directed-edge token carriers. -/
theorem pullbackQuotientHom_bijective_of_injective
    (K : CayleySubgraphSpec genΓ A)
    (Q : LabelledGroupQuotient genH genΓ)
    (hinj : Function.Injective Q.hom) :
    Function.Bijective (K.pullbackQuotientHom Q).onVertex ∧
      Function.Bijective (K.pullbackQuotientHom Q).onEdge := by
  constructor
  · constructor
    · intro x y hxy
      apply Subtype.ext
      apply hinj
      exact congrArg (fun z : K.Vertex => z.1) hxy
    · exact K.pullbackQuotientHom_vertex_surjective Q
  · constructor
    · intro e f hef
      have hp :
          (Q.hom e.1.1, e.1.2) =
            (Q.hom f.1.1, f.1.2) :=
        congrArg (fun z : K.Edge => z.1) hef
      have hfirst : e.1.1 = f.1.1 :=
        hinj (congrArg Prod.fst hp)
      have hsecond : e.1.2 = f.1.2 :=
        congrArg Prod.snd hp
      apply Subtype.ext
      exact Prod.ext hfirst hsecond
    · exact K.pullbackQuotientHom_edge_surjective Q

end CayleySubgraphSpec
end ABO
end PSTSEPPA
