import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedCompletedEGraphIso
import PSTSEPPA.ABO.MultiCosetEGraph

/-!
# ABO Theorem 4.5: exact standard local multiCE / source signed graph API agreement

The globally retractable forward cluster induction uses the standard
local multiCosetEGraph, while the original/local incomplete Γ-Cayley
component comparison uses arbitraryRankRootedLocalCompletedEGraph.
Both quotient the SAME true old/fresh oriented signed edges by the
same glued-source-and-FULL-signed-label equivalence relation.

We check that the two EGraph presentations agree on EVERY REAL
signed word path, for every rank C and every selected proper
alphabet family P. This check is essential for applying the
global cluster theorem in a genuinely k-local H[C] stage, without
ever fabricating missing original old edges or conflating
intrinsic component tags with ambient Cayley coordinates.

The proof is attempted by definitional equality; if Lean
does not accept it then an explicit quotient graph isomorphism
is necessary. No statement is admitted as an axiom or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every actually realized positive/inverse signed word path in
the standard local H[C] completed coset EGraph is exactly
a path in the source-compatible signed edge quotient. -/
theorem arbitraryRankRootedLocalCompletedFollows_iff_standard
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (u v : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) (w : LabelWord ι) :
    (K.arbitraryRankRootedLocalCompletedEGraph
      C root P hadm hgen hret).Follows u w v ↔
    ((K.intrinsicComponentLocalSlice C root).multiCosetEGraph
      P hadm hgen hret).Follows u w v := by
  rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
