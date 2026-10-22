import PSTSEPPA.ABO.CayleyLeftTranslations
import PSTSEPPA.ABO.CayleyStageProjection
import PSTSEPPA.ABO.UpwardInductionStageSignedWordEndpoint

/-!
# Genuine Cayley(G) cover of a COMPLETE H-stage based at ANY old G-group point

The corrected source ABO upward Theorem 4.7(iii) needs a
REAL signed labelled morphism F : Cayley(G) → T of the
legally completed H[B]-augmented stage, with its image of
the ORIGINAL G anchor g₀ equal to the EXACT original
component-tagged H-stage base vertex u, not merely
its ambient H-group coordinate.

A transition-group quotient from G to Transition(T)
certifies the requisite signed Cayley-to-stage map
based at the group identity 1, via the accepted
`CompleteEGraph.cayleyProjectionFromGroup`.
But the published proper-cluster argument usually
needs the cover based at some arbitrary original G
coset-coordinate g₀ ≠ 1.

Cayley(G) uses RIGHT generator multiplication.
Hence LEFT translation by g₀⁻¹ is a true signed
Cayley graph isomorphism that maps g₀ to 1. Compose
this actual label/source/inverse-preserving morphism
with the certified Cayley(G)→T projection based at u.

This gives a REAL labelled cover of T with F(g₀)=u,
and for EVERY positive/inverse chronological signed
word w:
    F(g₀ * [w]_G) = T.followWord(u,w).

The proof does not assume an impossible ambient map
T→Cayley(H), does not identify distinct original
old-component tags, and permits outside-B stationary
loops in T. The historical source-specific obligation
is to CONSTRUCT the labelled G→Transition(T) quotient
for each selected augmented H-stage; this is exactly
what the source's group-cover assumption/higher-rank
finite construction must supply, not an automatic
fact of H-stage completeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)

/-- ACTUAL signed Cayley(G)→T labelled morphism, based
at a specified arbitrary ORIGINAL G-group coordinate g₀
and an exact ACTUAL target stage vertex u.

Its Cayley-source left translation is a REAL labelled
EGraph morphism preserving positive/inverse directed
edge tokens, not a nonconstructive vertex-map slogan. -/
noncomputable def basedCayleyProjectionAtGroupPoint
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (g₀ : Γ) (u : V) :
    LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph :=
  (T.cayleyProjectionFromGroup gen φ hφ u).comp
    (cayleyLeftTranslateHom gen g₀⁻¹)

/-- The Cayley cover sends the exact ORIGINAL group anchor
g₀ to the CHOSEN actual H-stage vertex u, even if g₀ is
not the identity of the original G-group. -/
theorem basedCayleyProjectionAtGroupPoint_anchor
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (g₀ : Γ) (u : V) :
    (T.basedCayleyProjectionAtGroupPoint
      gen φ hφ g₀ u).onVertex g₀ = u := by
  change (T.cayleyProjectionFromGroup gen φ hφ u).onVertex
    (g₀⁻¹ * g₀) = u
  simpa using (T.cayleyProjectionFromGroup_one gen φ hφ u)

/-- Exact ORIGINAL G-word endpoint of the genuinely
translated Cayley(G)→H-stage cover. This handles every
positive/inverse letter and all legal completed loops. -/
theorem basedCayleyProjectionAtGroupPoint_signedWordEndpoint
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (g₀ : Γ) (u : V) (w : LabelWord ι) :
    (T.basedCayleyProjectionAtGroupPoint
      gen φ hφ g₀ u).onVertex
        (g₀ * PSTS.SignedWord.evalGroup gen w) =
      T.followWord u w := by
  change (T.cayleyProjectionFromGroup gen φ hφ u).onVertex
    (g₀⁻¹ * (g₀ * PSTS.SignedWord.evalGroup gen w)) =
    T.followWord u w
  simpa only [inv_mul_cancel_left] using
    (T.cayleyProjectionFromGroup_evalGroup gen φ hφ u w)

/-- The actual based G-cover maps ANY original G ambient
B-word endpoint to the exact completed H-stage endpoint;
this is the signed source-cover equation required in
corrected ABO Theorem4.7(iii). -/
theorem basedCayleyProjectionAtGroupPoint_equalEndpoints
    (gen : ι → Γ)
    (φ : Γ →* T.transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) = T.transitionSubgroupGenerator i)
    (g₀ : Γ) (u : V)
    (p q : LabelWord ι)
    (hStage :
      T.followWord u p = T.followWord u q) :
    (T.basedCayleyProjectionAtGroupPoint
        gen φ hφ g₀ u).onVertex
        (g₀ * PSTS.SignedWord.evalGroup gen p) =
      T.followWord u q := by
  rw [T.basedCayleyProjectionAtGroupPoint_signedWordEndpoint
    gen φ hφ g₀ u p]
  exact hStage

end CompleteEGraph
end ABO
end PSTSEPPA
