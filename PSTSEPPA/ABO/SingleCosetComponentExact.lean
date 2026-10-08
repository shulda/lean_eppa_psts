import PSTSEPPA.ABO.SingleCosetConnectivity
import PSTSEPPA.ABO.SingleCosetComponentInvariant
import PSTSEPPA.ABO.SingleCosetSkeletonEmbedding

/-!
# Exact B-components of the single-alphabet coset extension

The two independently checked path lemmas now give an if-and-only-if:
two points of CE(G,K;B) can be joined by an actual B-labelled path
exactly when their intrinsic component tags agree.

Consequently the canonical skeleton embedding preserves *and reflects*
B-connectivity of old vertices. In particular, completing the B-cosets
creates no accidental connections between distinct B-components of K.

This is the exact single-alphabet B-component identification used later
by coset-extension gluing and the cover/embedding arguments.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A B-path between two points of the single-B extension exists
if and only if their component indices agree. -/
theorem singleCosetEGraph_B_reachable_iff_index
    (B : Finset ι) (p q : K.AttachedCosetVertex B) :
    (∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.singleCosetEGraph B).Follows p w q) ↔
      p.1 = q.1 := by
  constructor
  · rintro ⟨w, hw, hpath⟩
    exact K.singleCosetEGraph_follows_B_preserves_index B hpath hw
  · intro hidx
    exact K.singleCosetEGraph_connected_on_index B p q hidx

/-- The canonical embedding of the old skeleton into CE(G,K;B)
preserves and reflects intrinsic B-reachability of old vertices.
No ambient group relation can create a new connection. -/
theorem skeleton_to_singleCoset_B_reachable_iff
    (B : Finset ι) (x y : K.Vertex) :
    (∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.singleCosetEGraph B).Follows
        ((K.skeletonToSingleCosetHom B).onVertex x)
        w
        ((K.skeletonToSingleCosetHom B).onVertex y)) ↔
      K.SubalphabetReachable B x y := by
  rw [K.singleCosetEGraph_B_reachable_iff_index]
  exact K.componentClass_eq_iff B x y

end CayleySubgraphSpec
end ABO
end PSTSEPPA
