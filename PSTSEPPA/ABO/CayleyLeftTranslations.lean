import PSTSEPPA.ABO.CayleyGraph
import PSTSEPPA.ABO.Morphisms

/-!
# The exact left-translation symmetries needed in Cayley-GRL

For the PSTS fibre-MAX application the source oriented Cayley graph
has positive-edge alphabet E = Q × P. The only graph automorphisms
for which the reflecting-group construction must be equivariant
are the LEFT translations by elements of the finite permutation
group Q, not arbitrary automorphisms of an arbitrary graph.

The Cayley EGraph already uses right multiplication by its chosen
generator at each positive directed edge, with formal inverse edge
tokens. Left Q-translations commute with these right steps even
when a generator is trivial, repeated, or produces a geometric loop.

We construct exact labelled graph morphisms preserving the signed
edge tokens, formal inversion and labels. Their vertex and edge
maps are bijections and compose in the ORIGINAL group order.

This proves the *input graph's* required symmetry. It does NOT
yet lift the symmetry to the finite reflecting group; that remains
an obligation of the later Cayley-GRL construction, rather than an
axiom or a claim about all graph automorphisms.
-/

namespace PSTSEPPA
namespace ABO

variable {Q ι : Type*} [Group Q]

/-- Positive edges of the oriented Cayley graph have the exact
source-facing type Q × P. Their formal inverse tokens occur in
the full ActionEdge Q P, which is Q × SignedLetter P. -/
abbrev CayleyPositiveEdge (Q ι : Type*) := Q × ι

/-- Left translation of an oriented positive Cayley edge. Its
generator label is unchanged, only the starting group vertex moves. -/
def cayleyPositiveLeftTranslate (q : Q)
    (e : CayleyPositiveEdge Q ι) : CayleyPositiveEdge Q ι :=
  (q * e.1, e.2)

/-- The left Q-translation of the complete, signed Cayley
EGraph is a genuine labelled graph homomorphism, for any
generator map ι→Q. In particular, it is valid for parallel
labels, trivial generators and geometrical loops. -/
noncomputable def cayleyLeftTranslateHom
    (gen : ι → Q) (q : Q) :
    LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph where
  onVertex := fun x => q * x
  onEdge := fun e => (q * e.1, e.2)
  map_source := by
    intro e
    rfl
  map_inv := by
    rintro ⟨x, s⟩
    apply Prod.ext
    · change
        q * (x * PSTS.SignedWord.evalGroupLetter gen s) =
          (q * x) * PSTS.SignedWord.evalGroupLetter gen s
      rw [mul_assoc]
    · rfl
  map_label := by
    intro e
    rfl

@[simp]
theorem cayleyLeftTranslateHom_vertex
    (gen : ι → Q) (q x : Q) :
    (cayleyLeftTranslateHom gen q).onVertex x = q * x :=
  rfl

@[simp]
theorem cayleyLeftTranslateHom_edge
    (gen : ι → Q) (q x : Q) (s : SignedLabel ι) :
    (cayleyLeftTranslateHom gen q).onEdge (x, s) =
      (q * x, s) :=
  rfl

/-- Positive-edge support is acted on by left Q-translations
without changing the underlying selected partial automorphism. -/
theorem cayleyLeftTranslateHom_positive_edge
    (gen : ι → Q) (q x : Q) (i : ι) :
    (cayleyLeftTranslateHom gen q).onEdge
        (x, PSTS.SignedLetter.pos i) =
      ((cayleyPositiveLeftTranslate q (x, i)).1,
        PSTS.SignedLetter.pos
          (cayleyPositiveLeftTranslate q (x, i)).2) :=
  rfl

/-- All left-translation graph morphisms are injective on the
actual Cayley vertices and signed oriented edge tokens. -/
theorem cayleyLeftTranslateHom_injective
    (gen : ι → Q) (q : Q) :
    Function.Injective (cayleyLeftTranslateHom gen q).onVertex ∧
    Function.Injective (cayleyLeftTranslateHom gen q).onEdge := by
  constructor
  · intro x y h
    exact mul_left_cancel h
  · rintro ⟨x, s⟩ ⟨y, t⟩ h
    have hx : q * x = q * y := congrArg Prod.fst h
    have hs : s = t := congrArg Prod.snd h
    cases hs
    exact congrArg (fun z : Q => (z, s))
      (mul_left_cancel hx)

/-- They are surjective on both sorts, by inverse left
translation. Hence each is a true labelled graph automorphism. -/
theorem cayleyLeftTranslateHom_surjective
    (gen : ι → Q) (q : Q) :
    Function.Surjective (cayleyLeftTranslateHom gen q).onVertex ∧
    Function.Surjective (cayleyLeftTranslateHom gen q).onEdge := by
  constructor
  · intro y
    refine ⟨q⁻¹ * y, ?_⟩
    simp
  · rintro ⟨y, s⟩
    refine ⟨(q⁻¹ * y, s), ?_⟩
    apply Prod.ext
    · simp
    · rfl

/-- The group law of the Q-action on Cayley vertices is literal
left multiplication, without permutation composition reversal. -/
theorem cayleyLeftTranslateHom_mul_vertex
    (gen : ι → Q) (q r x : Q) :
    (cayleyLeftTranslateHom gen (q * r)).onVertex x =
      (cayleyLeftTranslateHom gen q).onVertex
        ((cayleyLeftTranslateHom gen r).onVertex x) := by
  simp [mul_assoc]

/-- The SAME composition law holds on oriented signed edge tokens,
so the action is compatible with the positive edge alphabet Q × ι. -/
theorem cayleyLeftTranslateHom_mul_edge
    (gen : ι → Q) (q r : Q)
    (e : ActionEdge Q ι) :
    (cayleyLeftTranslateHom gen (q * r)).onEdge e =
      (cayleyLeftTranslateHom gen q).onEdge
        ((cayleyLeftTranslateHom gen r).onEdge e) := by
  cases e with
  | mk x s =>
      simp [mul_assoc]

end ABO
end PSTSEPPA
