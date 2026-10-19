import PSTSEPPA.ABO.IntrinsicComponentLocalSliceIso
import PSTSEPPA.ABO.LocalSubalphabetGeneratedRetractable
import PSTSEPPA.ABO.Morphisms

/-!
# Reflect true signed paths through a bijective labelled graph morphism

For the source ABO forward induction (Theorem 4.5), one frequently
replaces an intrinsic component of an INCOMPLETE Cayley skeleton in H
by its genuine rooted local skeleton in the generated group H[C].
The accepted `IntrinsicComponentLocalSliceIso` proves that this
translation is bijective on vertices and ACTUAL directed signed
edge tokens, including formal inverses and geometrical loops.

A bijective labelled E-graph morphism also REFLECTS every true
realised labelled path. We prove this explicitly by induction on
the signed word. For each target edge, SURJECTIVITY on genuine
edge tokens supplies an actual source edge, and INJECTIVITY on
vertices identifies its source. The path is lifted edge by edge
in the INCOMPLETE source EGraph: no missing edge or artificial
complete-Cayley edge is introduced.

We instantiate the generic path-reflection principle for the
intrinsic rooted component's true signed local H[C] translation.
Finally we package the source's k-retractability reduction:
for |C| ≤ k, H[C] is generated and globally retractable with
outside-C letters acting as the identity; simultaneously the
original rooted C-component is genuinely isomorphic to its
local signed Cayley skeleton, on both edges and paths.

This STILL does not identify the corresponding multi-coset
extensions; their old component-tagged quotient naturality
and the full forward-induction (Theorem 4.5) remain separate
formalization obligations.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable {G : EGraph V₁ E₁ ι} {H : EGraph V₂ E₂ ι}

/-- A labelled graph morphism injective on vertices and
surjective on TRUE directed signed edge tokens lifts every
realised target word path starting at the image of a source
vertex. This does not assume completeness of either EGraph. -/
theorem follows_lift_of_vertex_injective_edge_surjective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hVertex : Function.Injective f.onVertex)
    (hEdge : Function.Surjective f.onEdge)
    {u : V₁} {y : V₂} {w : LabelWord ι}
    (hPath : H.Follows (f.onVertex u) w y) :
    ∃ v : V₁, G.Follows u w v ∧ f.onVertex v = y := by
  induction w generalizing u y with
  | nil =>
      have huy : f.onVertex u = y := H.follows_nil_iff.mp hPath
      exact ⟨u, G.Follows.nil u, huy⟩
  | cons s w ih =>
      cases hPath with
      | @cons _ _ _ _ e hs hl hRest =>
          obtain ⟨e', he'⟩ := hEdge e
          have hSource : G.source e' = u := by
            apply hVertex
            calc
              f.onVertex (G.source e') =
                  H.source (f.onEdge e') := (f.map_source e').symm
              _ = H.source e := by rw [he']
              _ = f.onVertex u := hs
          have hLabel : G.label e' = s := by
            calc
              G.label e' = H.label (f.onEdge e') :=
                (f.map_label e').symm
              _ = H.label e := by rw [he']
              _ = s := hl
          have hTarget :
              f.onVertex (G.target e') = H.target e := by
            calc
              f.onVertex (G.target e') =
                  H.target (f.onEdge e') := (f.map_target e').symm
              _ = H.target e := by rw [he']
          have hRest' :
              H.Follows (f.onVertex (G.target e')) w y := by
            rw [hTarget]
            exact hRest
          obtain ⟨v, hSourcePath, hv⟩ := ih hRest'
          exact ⟨v, G.Follows.cons e' hSource hLabel hSourcePath, hv⟩

/-- A bijective source-signed graph morphism reflects ALL
actual labelled paths, even when the source graph is
INCOMPLETE. No fake old edges enter the proof. -/
theorem follows_reflect_of_vertex_injective_edge_surjective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hVertex : Function.Injective f.onVertex)
    (hEdge : Function.Surjective f.onEdge)
    {u v : V₁} {w : LabelWord ι}
    (hPath : H.Follows (f.onVertex u) w (f.onVertex v)) :
    G.Follows u w v := by
  obtain ⟨v', hLift, hv'⟩ :=
    G.follows_lift_of_vertex_injective_edge_surjective
      f hVertex hEdge hPath
  have heq : v' = v := hVertex hv'
  simpa only [heq] using hLift

end EGraph

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Genuine original rooted C-component and its local H[C]
translated skeleton have exactly the SAME realised signed
word paths, including inverses and actual loops.

One direction is standard graph-homomorphism preservation;
the other uses TRUE signed edge surjectivity and vertex
injectivity of the separately certified local component map. -/
theorem intrinsicComponentLocalHom_follows_iff
    (C : Finset ι) (root : K.Vertex)
    (u v : (K.intrinsicComponentLocalSlice C root).Vertex)
    (w : LabelWord ι) :
    ((K.subalphabetComponentSubgraph C root).toEGraph).Follows
      ((K.intrinsicComponentLocalHom C root).onVertex u)
      w
      ((K.intrinsicComponentLocalHom C root).onVertex v) ↔
    ((K.intrinsicComponentLocalSlice C root).toEGraph).Follows
      u w v := by
  constructor
  · intro h
    have hBij := K.intrinsicComponentLocalHom_bijective C root
    exact EGraph.follows_reflect_of_vertex_injective_edge_surjective
      (G := (K.intrinsicComponentLocalSlice C root).toEGraph)
      (H := (K.subalphabetComponentSubgraph C root).toEGraph)
      (K.intrinsicComponentLocalHom C root)
      hBij.1.1 hBij.2.2 h
  · intro h
    exact h.map (K.intrinsicComponentLocalHom C root)

/-- Source-local input package for induction on alphabets:
when the ambient original group is k-retractable and
|C| ≤ k, the TRUE subgroup H[C] is labelled-generated
and globally retractable, and the rooted old C-component
is faithfully translated to an actual H[C] skeleton
on original vertices, directed signed edges AND words.

This is not an assertion that H itself is globally
retractable or that its completed proper-coset extension
is already transported to H[C]. -/
theorem intrinsicComponent_local_algebra_and_signed_iso
    (k : ℕ) (hret : KRetractable gen k)
    (C : Finset ι) (hC : C.card ≤ k)
    (root : K.Vertex) :
    (IsGenerated (trivialCompletionGenerator gen C) ∧
      Retractable (trivialCompletionGenerator gen C)) ∧
    (Function.Bijective
       (K.intrinsicComponentLocalHom C root).onVertex ∧
     Function.Bijective
       (K.intrinsicComponentLocalHom C root).onEdge) := by
  exact ⟨generated_and_retractable_local_subalphabet
    gen k hret C hC,
    K.intrinsicComponentLocalHom_bijective C root⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
