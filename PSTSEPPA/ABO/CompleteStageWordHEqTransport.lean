import PSTSEPPA.ABO.CompleteStageWordKernelTransport

/-!
# Invariance of complete signed-word action congruence under actual HEq

A corrected ABO type-(2) augmented COMPLETE action has a
dependent vertex carrier: it depends on the genuine selected
OLD component-tagged quotient root and on the ambient group
coordinate anchoring the freshly attached B-left coset.

When separately certified exact root/anchor equalities identify
two such completed signed actions, the natural formal conclusion
is heterogeneous equality (HEq) of complete EGraphs, not an
unjustified homogeneous equality across different carrier
types.

HEq transports the entire chronological SIGNED word-action
kernel, for any two words and every vertex of each action.
This generic API operates on the complete signed actions
themselves, without forgetting formal positive/negative
edge tokens or invoking ambient group-coordinate injectivity.
-/

namespace PSTSEPPA
namespace ABO
namespace CompleteEGraph

variable {V₁ E₁ V₂ E₂ ι : Type*}
variable (G : CompleteEGraph V₁ E₁ ι)
variable (H : CompleteEGraph V₂ E₂ ι)

/-- Exact whole signed-word action congruence of two COMPLETE
labelled EGraphs is invariant under real dependent equality
of the graph structures, even when their vertex/edge carrier
types are written differently. -/
theorem wordActionCongr_iff_of_heq
    (hGH : HEq G H) (p q : LabelWord ι) :
    (∀ x : V₁, G.followWord x p = G.followWord x q) ↔
      (∀ y : V₂, H.followWord y p = H.followWord y q) := by
  cases hGH
  rfl

/-- Transfer equality of the actions of any two signed words
from the first complete stage to an HEq-equivalent second one.
The comparison is on ALL actual second-stage vertices. -/
theorem wordActionCongr_of_heq
    (hGH : HEq G H) (p q : LabelWord ι)
    (hG : ∀ x : V₁, G.followWord x p = G.followWord x q) :
    ∀ y : V₂, H.followWord y p = H.followWord y q :=
  (G.wordActionCongr_iff_of_heq H hGH p q).mp hG

end CompleteEGraph
end ABO
end PSTSEPPA
