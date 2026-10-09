import PSTSEPPA.ABO.CoatomFamilyGraphEquivalence
import PSTSEPPA.ABO.Morphisms

/-!
# Reflection of actual paths by a labelled-graph isomorphism

A labelled graph morphism always maps realised signed-word paths.
Conversely, if its vertex map is injective and its signed directed
edge map is surjective, EVERY realised path between image vertices
lifts to a path of the very same signed word between their originals.

The converse is proved by induction on the word. For the first
target-edge token, use surjectivity to find a source token, use
preservation of source/label plus vertex injectivity to identify
the source, and then use preservation of target to lift the tail.
The empty word uses vertex injectivity.

This generic lemma applies to the just-proved coatom-only/full
multi-coset graph isomorphism (for |A|≥2). Hence the EXACT
signed-word path relation, and in particular every intrinsic
subalphabet component relation, is invariant under the coatom
family replacement. We do not merely compare ambient cosets.

This is essential to transferring future cluster-property,
connected-slice, and bridge-freeness statements from the coatom
presentation to the original full family.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable {G : EGraph V₁ E₁ ι} {H : EGraph V₂ E₂ ι}

/-- Reflection of an actual signed-word path along a labelled
graph morphism injective on vertices and surjective on directed edges.
The induced path keeps precisely the same signed word. -/
theorem Follows.reflect_of_vertex_injective_edge_surjective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hvinj : Function.Injective f.onVertex)
    (hesurj : Function.Surjective f.onEdge)
    {u v : V₁} {w : LabelWord ι}
    (h : H.Follows (f.onVertex u) w (f.onVertex v)) :
    G.Follows u w v := by
  induction w generalizing u with
  | nil =>
      have huv : u = v :=
        hvinj (H.follows_nil_iff.mp h)
      subst v
      exact EGraph.Follows.nil _
  | cons s w ih =>
      cases h with
      | cons e hsource hlabel hrest =>
          obtain ⟨e', he⟩ := hesurj e
          subst e
          have hsrc : G.source e' = u := by
            apply hvinj
            exact (f.map_source e').symm.trans hsource
          have hlab : G.label e' = s :=
            (f.map_label e').symm.trans hlabel
          have hrest' :
              H.Follows (f.onVertex (G.target e'))
                w (f.onVertex v) := by
            rw [← f.map_target e']
            exact hrest
          exact EGraph.Follows.cons e' hsrc hlab
            (ih (u := G.target e') hrest')

/-- A vertex-injective and edge-surjective labelled E-graph morphism
preserves and REFLECTS every actual labelled word path. -/
theorem follows_iff_of_vertex_injective_edge_surjective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hvinj : Function.Injective f.onVertex)
    (hesurj : Function.Surjective f.onEdge)
    (u v : V₁) (w : LabelWord ι) :
    G.Follows u w v ↔
      H.Follows (f.onVertex u) w (f.onVertex v) := by
  constructor
  · intro h
    exact h.map f
  · intro h
    exact h.reflect_of_vertex_injective_edge_surjective
      f hvinj hesurj

end EGraph

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact path-transport equivalence between the coatom-only and full
proper-alphabet coset-extension EGraphs, at |A|≥2. Uses all the
component-tagged vertex and signed-edge equalities, never ambient
Cayley injectivity or a cluster-property hypothesis. -/
theorem coatomToFullCosetHom_follows_iff
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (u v : K.MultiCosetVertex (coatomCosetFamily A)
      hadm hgen hret)
    (w : LabelWord ι) :
    (K.multiCosetEGraph (coatomCosetFamily A)
      hadm hgen hret).Follows u w v ↔
    (K.multiCosetEGraph (allProperCosetFamily A)
      hadm hgen hret).Follows
      ((K.coatomToFullCosetHom hadm hgen hret).onVertex u)
      w
      ((K.coatomToFullCosetHom hadm hgen hret).onVertex v) := by
  let f := K.coatomToFullCosetHom hadm hgen hret
  obtain ⟨⟨hvinj, _⟩, ⟨_, hesurj⟩⟩ :=
    K.coatomToFullCosetHom_bijective
      hadm hgen hret hcard
  exact EGraph.follows_iff_of_vertex_injective_edge_surjective
    f hvinj hesurj u v w

end CayleySubgraphSpec
end ABO
end PSTSEPPA
