import PSTSEPPA.ABO.ForwardInductionLocalAdmissibility
import PSTSEPPA.ABO.ForwardInductionArbitraryRankSignedComponentTransport

/-!
# ABO Theorem 4.5: completed signed local stages from actual source hypotheses

Earlier arbitrary-rank source/local multi-coset graph normalization
assumed local H[C]-skeleton admissibility as a separate input. The
previous theorem proves that input directly from the ORIGINAL
incomplete ambient Cayley skeleton's admissibility, even if C=A.

We now apply the full source-facing hypotheses:
* the ACTUAL original Γ-Cayley old skeleton K is admissible;
* Γ is k-retractable, WITHOUT globally retractable Γ;
* C⊆A and |C|<=k.

They suffice to CONSTRUCT the true normalized local H[C]
component-tagged multi-coset extension and an honest labelled
signed EGraph isomorphism with the EXACT original rooted
component-tagged coset quotient, for ANY selected proper family P.

Both vertex and ORIENTED signed edge CLASS maps are bijective,
and ALL ACTUALLY REALIZED old/fresh signed paths are preserved
and reflected. There is no separate local admissibility,
generation, or retractability premise, no fake signed old edge,
and no collapse of distinct original component tags just
because their ambient Γ coordinates agree.

This is a SUBSTANTIAL local normalization gate for the published
forward induction. It does not assert that the completed stage
is embedded/bridge-free, prove the full Theorem 4.5, or imply PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The certified LOCAL signed old-skeleton admissibility proof
constructed directly from original Γ-Cayley admissibility, for
the chosen rooted C-component, including C=A. -/
noncomputable abbrev sourceInductionLocalAdmissibility
    (hadm : K.AdmissibleForCosetExtension)
    (C : Finset ι) (hCA : C ⊆ A) (root : K.Vertex) :
    (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension :=
  K.intrinsicComponentLocalSlice_admissible_of_parent hadm C hCA root

/-- A single labelled signed graph morphism of the true local
completed H[C] stage onto the exact original Γ-source C-component
coset extension, now constructed from original admissibility
and k-retractability ONLY; all local side conditions are proved. -/
noncomputable abbrev sourceInductionKLocalCompletedSignedHom
    (hadm : K.AdmissibleForCosetExtension)
    (k : ℕ) (hk : KRetractable gen k)
    (C : Finset ι) (hCA : C ⊆ A) (hCk : C.card ≤ k)
    (root : K.Vertex) (P : CosetFamilySpec C) :=
  K.arbitraryRankRootedCompletedEGraphHom
    C root P
    (K.sourceInductionLocalAdmissibility hadm C hCA root)
    (isGenerated_trivialCompletionGenerator gen C)
    (retractable_trivialCompletionGenerator_of_kRetractable gen k hk C hCk)

/-- No LOCAL hypothesis is assumed: original A-skeleton
admissibility and k-retractability force the complete signed
local-versus-original graph morphism to be BIJECTIVE on
ALL original/new vertices and oriented signed edge classes. -/
theorem sourceInductionKLocalCompletedSignedHom_bijective
    (hadm : K.AdmissibleForCosetExtension)
    (k : ℕ) (hk : KRetractable gen k)
    (C : Finset ι) (hCA : C ⊆ A) (hCk : C.card ≤ k)
    (root : K.Vertex) (P : CosetFamilySpec C) :
    Function.Bijective
      (K.sourceInductionKLocalCompletedSignedHom
        hadm k hk C hCA hCk root P).onVertex ∧
    Function.Bijective
      (K.sourceInductionKLocalCompletedSignedHom
        hadm k hk C hCA hCk root P).onEdge :=
  K.arbitraryRankRootedCompletedEGraphHom_bijective
    C root P
    (K.sourceInductionLocalAdmissibility hadm C hCA root)
    (isGenerated_trivialCompletionGenerator gen C)
    (retractable_trivialCompletionGenerator_of_kRetractable gen k hk C hCk)

/-- The SAME statement at the level of EVERY genuine directed
signed word path, not just completed ambient group word
evaluations. It includes missing ORIGINAL old edges, formal
inverse tokens, loops, and newly attached full D-coset points. -/
theorem sourceInductionKLocalCompletedSignedHom_follows_iff
    (hadm : K.AdmissibleForCosetExtension)
    (k : ℕ) (hk : KRetractable gen k)
    (C : Finset ι) (hCA : C ⊆ A) (hCk : C.card ≤ k)
    (root : K.Vertex) (P : CosetFamilySpec C)
    (u v : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex P
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk))
    (w : LabelWord ι) :
    (K.arbitraryRankRootedLocalCompletedEGraph
      C root P
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk)).Follows u w v ↔
    (K.arbitraryRankRootedOriginalCompletedEGraph
      C root P
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk)).Follows
      ((K.sourceInductionKLocalCompletedSignedHom
        hadm k hk C hCA hCk root P).onVertex u)
      w
      ((K.sourceInductionKLocalCompletedSignedHom
        hadm k hk C hCA hCk root P).onVertex v) :=
  K.arbitraryRankRootedCompletedEGraphHom_follows_iff
    C root P
    (K.sourceInductionLocalAdmissibility hadm C hCA root)
    (isGenerated_trivialCompletionGenerator gen C)
    (retractable_trivialCompletionGenerator_of_kRetractable
      gen k hk C hCk) u v w

end CayleySubgraphSpec
end ABO
end PSTSEPPA
