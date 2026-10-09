import PSTSEPPA.ABO.RetractabilityRetraction
import PSTSEPPA.ABO.CanonicalCover

/-!
# Canonical projection of a final group's Cayley paths into an ABO stage

The source's Lemma 5.6 uses a labelled map from the final Cayley
group G to the selected stage extension, and the fact that two
signed words with equal FINAL G-values project to paths with
the same endpoint. This last assertion does not require the
projection to be injective.

A canonical such map exists as soon as the final labelled group
admits a generator-preserving homomorphism into the transition
group of the completed stage graph. Compose:

  Cayley(G,gen) -> Cayley(Transition(stage),genStage)
                  -> stage component, based at u.

This module proves the resulting source-exact labelled graph
morphism, its chosen basepoint normalization, and the complete
signed-word endpoint formula. In particular G-word equality
forces equal projected endpoints, including inverse letters and
trivial/loop generators.

The missing Section 5 construction still must PRODUCE the
generator-preserving homomorphism from final G to the transition
group of each relevant completed coset extension; this module
does not assert that such a projection always exists.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)

/-- Given a group homomorphism of labelled generators from Γ into
the transition group of T, compose its induced Cayley graph
morphism with the canonical Cayley-to-stage component map.
No injectivity, stability or finite group hypothesis is needed. -/
noncomputable def cayleyProjectionFromGroup
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (u : V) :
    LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph :=
  (T.canonicalCayleyHom u).comp
    (cayleyHomOfGroupHom gen T.transitionSubgroupGenerator φ hφ)

/-- The projected group coordinate is evaluated by the transition
group action at the chosen basepoint. -/
@[simp]
theorem cayleyProjectionFromGroup_onVertex
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (u : V) (g : Γ) :
    (T.cayleyProjectionFromGroup gen φ hφ u).onVertex g =
      T.canonicalVertex u (φ g) :=
  rfl

/-- The basepoint 1 in the final group maps to the specified
stage vertex u. This normalization matters for path endpoints. -/
@[simp]
theorem cayleyProjectionFromGroup_one
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (u : V) :
    (T.cayleyProjectionFromGroup gen φ hφ u).onVertex 1 = u := by
  change T.canonicalVertex u (φ 1) = u
  simp [canonicalVertex, rightApply]

/-- Exact signed-word endpoint formula for the projection:
the image of the FINAL G-value of a word w is the endpoint
of the true stage T-path following that word from u. -/
theorem cayleyProjectionFromGroup_evalGroup
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (u : V) (w : LabelWord ι) :
    (T.cayleyProjectionFromGroup gen φ hφ u).onVertex
        (PSTS.SignedWord.evalGroup gen w) =
      T.followWord u w := by
  let F := T.cayleyProjectionFromGroup gen φ hφ u
  have hEndpoint :
      (cayleyGraph gen).followWord (1 : Γ) w =
        PSTS.SignedWord.evalGroup gen w := by
    simpa using
      (cayleyGraph.followWord_eq_mul_evalGroup gen (1 : Γ) w)
  have hNaturality :
      T.followWord (F.onVertex (1 : Γ)) w =
        F.onVertex ((cayleyGraph gen).followWord 1 w) :=
    CompleteEGraph.hom_followWord
      (cayleyGraph gen) T F 1 w
  have hOne : F.onVertex (1 : Γ) = u :=
    T.cayleyProjectionFromGroup_one gen φ hφ u
  calc
    F.onVertex (PSTS.SignedWord.evalGroup gen w) =
      F.onVertex ((cayleyGraph gen).followWord 1 w) :=
        congrArg F.onVertex hEndpoint.symm
    _ = T.followWord (F.onVertex 1) w := hNaturality.symm
    _ = T.followWord u w := by rw [hOne]

/-- The source's projection argument in corrected Lemma 5.6:
two words of equal FINAL group value necessarily end at
the same stage vertex after projection from the same
basepoint. No projection injectivity is used or claimed. -/
theorem cayleyProjectionFromGroup_equal_endpoints
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (u : V) (p q : LabelWord ι)
    (hpq :
      PSTS.SignedWord.evalGroup gen p =
        PSTS.SignedWord.evalGroup gen q) :
    T.followWord u p = T.followWord u q := by
  let F := T.cayleyProjectionFromGroup gen φ hφ u
  calc
    T.followWord u p =
        F.onVertex (PSTS.SignedWord.evalGroup gen p) :=
      (T.cayleyProjectionFromGroup_evalGroup gen φ hφ u p).symm
    _ = F.onVertex (PSTS.SignedWord.evalGroup gen q) :=
      congrArg F.onVertex hpq
    _ = T.followWord u q :=
      T.cayleyProjectionFromGroup_evalGroup gen φ hφ u q

end CompleteEGraph
end ABO
end PSTSEPPA
