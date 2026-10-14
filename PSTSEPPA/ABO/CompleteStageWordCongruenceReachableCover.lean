import PSTSEPPA.ABO.CompleteStageWordCongruenceCayleyCover
import PSTSEPPA.ABO.TransitionGroupGenerated

/-!
# Full reachable-component Cayley covers from complete signed-word congruence

The generic word-congruence bridge constructs a REAL generator-preserving
homomorphism from any genuinely generated labelled group Γ onto the
complete stage's actual transition group. Since all transition-group
elements are themselves represented by signed words in the generators,
the map is surjective.

Consequently the induced based signed Cayley graph morphism hits
EXACTLY every vertex and every directed signed action-edge token
of the connected/reachable completed-stage component of its root,
including formal inverse loop edge tokens.

No connectedness, injectivity of ambient coordinates, Cayley
embedding of arbitrary completed stages, or collapse of distinct
component-tagged vertices is assumed. This is the full finite
stage-cover interface required after original Z₁ word action
congruence is established.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)

/-- The canonical homomorphism induced by group-word action
congruence commutes with evaluation of EVERY chronological
signed word (including negative letters). -/
theorem groupWordActionHom_evalGroup
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hcongr :
      ∀ (p q : LabelWord ι),
        PSTS.SignedWord.evalGroup gen p =
          PSTS.SignedWord.evalGroup gen q →
        ∀ x : V, T.followWord x p = T.followWord x q)
    (w : LabelWord ι) :
    T.groupWordActionHom gen hgen hcongr
      (PSTS.SignedWord.evalGroup gen w) =
    PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator w := by
  induction w with
  | nil => simp
  | cons s w ih =>
      cases s with
      | pos i =>
          change
            T.groupWordActionHom gen hgen hcongr
              (gen i * PSTS.SignedWord.evalGroup gen w) =
              T.transitionSubgroupGenerator i *
                PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator w
          rw [map_mul, T.groupWordActionHom_generator, ih]
      | neg i =>
          change
            T.groupWordActionHom gen hgen hcongr
              ((gen i)⁻¹ * PSTS.SignedWord.evalGroup gen w) =
              (T.transitionSubgroupGenerator i)⁻¹ *
                PSTS.SignedWord.evalGroup T.transitionSubgroupGenerator w
          rw [map_mul, map_inv, T.groupWordActionHom_generator, ih]

/-- The induced labelled homomorphism is SURJECTIVE onto the
actual transition subgroup, not an assumed abstract target.
This uses finite signed words representing all transition elements. -/
theorem groupWordActionHom_surjective
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hcongr :
      ∀ (p q : LabelWord ι),
        PSTS.SignedWord.evalGroup gen p =
          PSTS.SignedWord.evalGroup gen q →
        ∀ x : V, T.followWord x p = T.followWord x q) :
    Function.Surjective (T.groupWordActionHom gen hgen hcongr) := by
  intro g
  obtain ⟨w, hw⟩ :=
    (T.transitionSubgroupGenerator_isGenerated).exists_evalGroup_eq g
  refine ⟨PSTS.SignedWord.evalGroup gen w, ?_⟩
  exact (T.groupWordActionHom_evalGroup gen hgen hcongr w).trans hw

/-- The true signed Cayley graph based cover of T hits EXACTLY
the reachable component of its selected root: all vertices,
and NO vertices in unrelated components. -/
theorem cayleyCoverFromWordCongruence_vertex_range
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hcongr :
      ∀ (p q : LabelWord ι),
        PSTS.SignedWord.evalGroup gen p =
          PSTS.SignedWord.evalGroup gen q →
        ∀ x : V, T.followWord x p = T.followWord x q)
    (u : V) :
    Set.range (T.cayleyCoverFromWordCongruence gen hgen hcongr u).onVertex =
      {v : V | T.Reachable u v} := by
  let φ := T.groupWordActionHom gen hgen hcongr
  have hsurj : Function.Surjective φ :=
    T.groupWordActionHom_surjective gen hgen hcongr
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    change T.Reachable u (T.canonicalVertex u (φ g))
    exact T.canonicalVertex_reachable u _
  · intro hv
    obtain ⟨t, ht⟩ := T.reachable_exists_canonicalVertex u hv
    obtain ⟨g, hg⟩ := hsurj t
    refine ⟨g, ?_⟩
    change T.canonicalVertex u (φ g) = v
    simpa [hg] using ht

/-- The same actual labelled graph cover also hits EXACTLY
the directed signed-edge tokens with source in the root's
reachable component, including inverse tokens at fixed loops. -/
theorem cayleyCoverFromWordCongruence_edge_range
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hcongr :
      ∀ (p q : LabelWord ι),
        PSTS.SignedWord.evalGroup gen p =
          PSTS.SignedWord.evalGroup gen q →
        ∀ x : V, T.followWord x p = T.followWord x q)
    (u : V) :
    Set.range (T.cayleyCoverFromWordCongruence gen hgen hcongr u).onEdge =
      {e : Edge | T.Reachable u (T.source e)} := by
  let φ := T.groupWordActionHom gen hgen hcongr
  have hsurj : Function.Surjective φ :=
    T.groupWordActionHom_surjective gen hgen hcongr
  ext e
  constructor
  · rintro ⟨⟨g, s⟩, rfl⟩
    change T.Reachable u
      (T.source (T.edgeAt (T.canonicalVertex u (φ g)) s))
    rw [T.edgeAt_source]
    exact T.canonicalVertex_reachable u _
  · intro he
    obtain ⟨t, ht⟩ := T.reachable_exists_canonicalVertex u he
    obtain ⟨g, hg⟩ := hsurj t
    refine ⟨(g, T.label e), ?_⟩
    change T.edgeAt (T.canonicalVertex u (φ g))
      (T.label e) = e
    apply T.edgeAt_eq
    · simpa [hg] using ht.symm
    · rfl

end CompleteEGraph
end ABO
end PSTSEPPA
