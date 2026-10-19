import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedCompletedEGraphIso

/-!
# ABO Theorem 4.5: all subalphabet path components of the completed local stage

The arbitrary-rank original/local multi-coset EGraph isomorphism
preserves and reflects REAL directed signed paths after the exact
source-and-full-signed-label edge quotient, not just in the old skeleton.

Here its genuine path equivalence is restricted to paths whose labels
all belong to an arbitrary subalphabet D.  This is the formulation
needed by the componentwise forward induction: the ENTIRE completed
local C-stage and original rooted C-component have the same
D-connectivity for every D, including after attaching new coset points.

The k-retractable version uses the already certified local generation
and local retractability of H[C] for |C| <= k; only the actual local
old-skeleton admissibility remains an explicit premise. In particular,
we never postulate global retractability of the ambient group or
invent missing original signed old edges.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- EVERY D-supported REAL signed path between newly completed local
multi-coset vertices exists exactly when its true original component-
tagged image is connected by a D-supported REAL signed path.  This is
valid at arbitrary finite parent rank and for EVERY D, without an
artificial old edge or global Γ-retractability assumption. -/
theorem arbitraryRankRootedCompletedEGraph_supportedFollows_iff
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι)
    (u v : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    (∃ w : LabelWord ι, LabelWord.Uses D w ∧
      (K.arbitraryRankRootedLocalCompletedEGraph
        C root P hadm hgen hret).Follows u w v) ↔
    (∃ w : LabelWord ι, LabelWord.Uses D w ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).Follows
          ((K.arbitraryRankRootedCompletedEGraphHom
            C root P hadm hgen hret).onVertex u)
          w
          ((K.arbitraryRankRootedCompletedEGraphHom
            C root P hadm hgen hret).onVertex v)) := by
  constructor
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw,
      (K.arbitraryRankRootedCompletedEGraphHom_follows_iff
        C root P hadm hgen hret u v w).mp hp⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw,
      (K.arbitraryRankRootedCompletedEGraphHom_follows_iff
        C root P hadm hgen hret u v w).mpr hp⟩

/-- Source forward-induction component-path transport with the exact
k-retractability hypotheses: |C| <= k automatically supplies the
true local group's generation and retractability.  No such assumption
is made on the entire original ambient Γ. -/
theorem arbitraryRankRootedKCompletedEGraph_supportedFollows_iff
    (k : ℕ) (hk : KRetractable gen k)
    (C : Finset ι) (hC : C.card ≤ k)
    (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (D : Finset ι)
    (u v : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm
        (isGenerated_trivialCompletionGenerator gen C)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen k hk C hC)) :
    (∃ w : LabelWord ι, LabelWord.Uses D w ∧
      (K.arbitraryRankRootedLocalCompletedEGraph
        C root P hadm
          (isGenerated_trivialCompletionGenerator gen C)
          (retractable_trivialCompletionGenerator_of_kRetractable
            gen k hk C hC)).Follows u w v) ↔
    (∃ w : LabelWord ι, LabelWord.Uses D w ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm
          (isGenerated_trivialCompletionGenerator gen C)
          (retractable_trivialCompletionGenerator_of_kRetractable
            gen k hk C hC)).Follows
          ((K.arbitraryRankRootedCompletedEGraphHom
            C root P hadm
              (isGenerated_trivialCompletionGenerator gen C)
              (retractable_trivialCompletionGenerator_of_kRetractable
                gen k hk C hC)).onVertex u)
          w
          ((K.arbitraryRankRootedCompletedEGraphHom
            C root P hadm
              (isGenerated_trivialCompletionGenerator gen C)
              (retractable_trivialCompletionGenerator_of_kRetractable
                gen k hk C hC)).onVertex v)) :=
  K.arbitraryRankRootedCompletedEGraph_supportedFollows_iff
    C root P hadm
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hC) D u v

end CayleySubgraphSpec
end ABO
end PSTSEPPA
