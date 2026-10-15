import PSTSEPPA.ABO.Morphisms
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Reflection of REAL signed paths across bijective labelled EGraph morphisms

An injective vertex map and a surjective directed-edge map in a
label-preserving EGraph morphism are sufficient to reflect all
realised chronological signed paths, not just graph adjacency.

Each target signed path can be lifted edge by edge: edge surjectivity
provides a genuine source edge, and vertex injectivity forces that
edge to begin at the prescribed source vertex. Formal inversion,
source, target and signed label are preserved by the morphism.

With full bijectivity of both maps, the resulting iff of actual
Follows paths gives an exact equivalence of all subalphabet-labelled
intrinsic connected components. This is the reusable source-agnostic
API for moving literal original H₁-cover components between the
paper's direct T(Y₁) preimage and their transported presentation.

No completeness, connectedness, retraction, coset quotient
injectivity or ambient Cayley-coordinate equality is assumed.
-/

namespace PSTSEPPA
namespace ABO
namespace EGraph

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable (G : EGraph V₁ E₁ ι) (H : EGraph V₂ E₂ ι)

/-- Reflection of EVERY genuine signed directed path along a
labelled EGraph morphism injective on original vertices and
surjective on all original signed edge tokens. Determinism
of the target is not substituted for actual edge lifting. -/
theorem follows_reflect_of_vertex_injective_edge_surjective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hV : Function.Injective f.onVertex)
    (hE : Function.Surjective f.onEdge)
    {u v : V₁} {w : LabelWord ι}
    (hpath : H.Follows (f.onVertex u) w (f.onVertex v)) :
    G.Follows u w v := by
  induction w generalizing u with
  | nil =>
      have huv : u = v :=
        hV (H.follows_nil_iff.mp hpath)
      subst v
      exact EGraph.Follows.nil u
  | cons s w ih =>
      cases hpath with
      | cons e heSource heLabel hRest =>
          obtain ⟨d, hd⟩ := hE e
          have hdSource : G.source d = u := by
            apply hV
            calc
              f.onVertex (G.source d) = H.source (f.onEdge d) :=
                (f.map_source d).symm
              _ = H.source e := congrArg H.source hd
              _ = f.onVertex u := heSource
          have hdLabel : G.label d = s := by
            calc
              G.label d = H.label (f.onEdge d) :=
                (f.map_label d).symm
              _ = H.label e := congrArg H.label hd
              _ = s := heLabel
          have ht : H.target e = f.onVertex (G.target d) := by
            calc
              H.target e = H.target (f.onEdge d) :=
                congrArg H.target hd.symm
              _ = f.onVertex (G.target d) := f.map_target d
          have hRest' :
              H.Follows (f.onVertex (G.target d)) w
                (f.onVertex v) := by
            simpa only [ht] using hRest
          exact EGraph.Follows.cons d hdSource hdLabel
            (ih hRest')

/-- Signed Follows paths are preserved and reflected by an
actual vertex-and-edge-bijective labelled graph isomorphism.
Both directions refer to REAL directed edges, not completed
missing loops or ambient group-word endpoint values. -/
theorem follows_iff_of_bijective_labelledHom
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hV : Function.Bijective f.onVertex)
    (hE : Function.Bijective f.onEdge)
    (u v : V₁) (w : LabelWord ι) :
    G.Follows u w v ↔
      H.Follows (f.onVertex u) w (f.onVertex v) := by
  constructor
  · intro hp
    exact hp.map f
  · intro hp
    exact G.follows_reflect_of_vertex_injective_edge_surjective
      H f hV.1 hE.2 hp

/-- Intrinsic subalphabet-reachability has EXACTLY the same
meaning on either side of a true signed graph isomorphism:
an A-supported input word connects u→v if and only if its
image connects f(u)→f(v). This is the needed component index
transport, retaining all actual old signed edge tokens. -/
theorem subalphabet_paths_iff_of_bijective_labelledHom
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hV : Function.Bijective f.onVertex)
    (hE : Function.Bijective f.onEdge)
    (A : Finset ι) (u v : V₁) :
    (∃ w : LabelWord ι, LabelWord.Uses A w ∧
      G.Follows u w v) ↔
    (∃ w : LabelWord ι, LabelWord.Uses A w ∧
      H.Follows (f.onVertex u) w (f.onVertex v)) := by
  constructor
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw,
      (G.follows_iff_of_bijective_labelledHom H f hV hE u v w).mp hp⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw,
      (G.follows_iff_of_bijective_labelledHom H f hV hE u v w).mpr hp⟩

end EGraph
end ABO
end PSTSEPPA
