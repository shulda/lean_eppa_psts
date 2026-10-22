import PSTSEPPA.ABO.SingleCosetConnectivity
import PSTSEPPA.ABO.SingleCosetExtension
import PSTSEPPA.ABO.CayleyStageProjection

/-!
# ABO 4.7(iii): H B-augmented FULL-coset paths certify group-word equality

In the corrected Theorem 4.7(iii) OFF-SKELETON proper n≥2 case,
the true G Cayley cover of the source H-stage with an added
FULL H[B] coset is used to establish

  [p]_H = [p₁ ++ inv(p₂)]_H,

where the two actual signed B-paths have the SAME endpoints
inside the attached FULL H[B] coset.

This is a genuine geometric statement: equality of arbitrary
H-stage vertices or paths in the UNaugmented CE does not
automatically imply equality of group-word values if one
collapses old component tags or treats missing edges as loops.

We isolate the exact general path-to-word calculation:
if a REAL incomplete signed EGraph maps by a genuine
label-preserving morphism to Cayley(H), then TWO actual
signed paths with the SAME source and target have equal
H-group word evaluations. The proof uses ONLY actual
positive/inverse oriented edge tokens and deterministic
Cayley-path endpoints, no faithful embedding of the
EGraph into Cayley(H) is required.

As a corollary, every ORIGINAL component-tagged FULL
H[B] coset has this property on its true signed edges.
It is precisely the group-value reflection component
needed once the source B-augmentation cover supplies
the two actual paths in the SAME full B-coset.
This does not assert that the historic selected full-B
augmentation cover has yet been constructed.

No extra axioms/sorry, no fictitious old directed edges.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace EGraph

variable (G : EGraph V Edge ι)

/-- Exact actual-signed-path group-value reflection under a
real Cayley(Γ) labelled morphism, with NO injectivity assumption
on vertices or edges of the original incomplete signed graph.

Equal path SOURCE and TARGET in the signed EGraph give equal
evaluations of their chronological positive/inverse words
inside the ambient group Γ. -/
theorem evalGroup_eq_of_same_endpoints_in_Cayley
    (gen : ι → Γ)
    (F : LabelledGraphHom
      G.toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph)
    (u v : V) (p q : LabelWord ι)
    (hp : G.Follows u p v)
    (hq : G.Follows u q v) :
    PSTS.SignedWord.evalGroup gen p =
      PSTS.SignedWord.evalGroup gen q := by
  have hpMapped :
      (cayleyGraph gen).toEGraph.Follows
        (F.onVertex u) p (F.onVertex v) :=
    hp.map F
  have hqMapped :
      (cayleyGraph gen).toEGraph.Follows
        (F.onVertex u) q (F.onVertex v) :=
    hq.map F
  have hpEnd :
      (cayleyGraph gen).followWord (F.onVertex u) p =
        F.onVertex v :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord (F.onVertex u) p)
      hpMapped
  have hqEnd :
      (cayleyGraph gen).followWord (F.onVertex u) q =
        F.onVertex v :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord (F.onVertex u) q)
      hqMapped
  have hpValue :
      F.onVertex u * PSTS.SignedWord.evalGroup gen p =
        F.onVertex v := by
    simpa only [cayleyGraph.followWord_eq_mul_evalGroup] using hpEnd
  have hqValue :
      F.onVertex u * PSTS.SignedWord.evalGroup gen q =
        F.onVertex v := by
    simpa only [cayleyGraph.followWord_eq_mul_evalGroup] using hqEnd
  exact mul_left_cancel (hpValue.trans hqValue.symm)

end EGraph

variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The TRUE full original H[B] constituent detects equality
of evaluated chronological signed B-words from equal original
attached B-coset endpoints, retaining the original B-component
tag and actual oriented inverse edges.

This is what the corrected source B-AUGMENTATION argument
uses once the two B-paths are verified to lie in the newly
attached full H[B] coset. Neither global H-CE embeddedness
nor any quotient tag collapse is assumed. -/
theorem singleFullCoset_signedWords_equal_of_commonEndpoint
    (B : Finset ι)
    (u v : K.AttachedCosetVertex B)
    (p q : LabelWord ι)
    (hp : (K.singleCosetEGraph B).Follows u p v)
    (hq : (K.singleCosetEGraph B).Follows u q v) :
    PSTS.SignedWord.evalGroup gen p =
      PSTS.SignedWord.evalGroup gen q :=
  (K.singleCosetEGraph B).evalGroup_eq_of_same_endpoints_in_Cayley
    gen (K.singleCosetAmbientHom B) u v p q hp hq

end CayleySubgraphSpec
end ABO
end PSTSEPPA
