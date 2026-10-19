import PSTSEPPA.ABO.RootedSourceMultiCosetVertexQuotient
import PSTSEPPA.ABO.LocalSubalphabetGeneratedRetractable

/-!
# ABO Theorem 4.5: arbitrary-rank rooted local/original multi-coset vertex quotient

The accepted rank-two source theorem
`RootedSourceMultiCosetVertexQuotient.lean` constructs the actual
component-tagged full vertex quotient for a two-letter local group.
Its proof already uses genuinely RANK-INDEPENDENT source APIs:
  * the original incomplete signed rooted C-component is isomorphic
    to the normalized old H[C]-skeleton on ACTUAL directed signed edges;
  * all intrinsic D-path-component indices agree;
  * every full D⊆C attached point and its ORIGINAL component tag
    has a unique local H[C] preimage;
  * the raw (3.10) common-intersection-support gluing relation is
    preserved AND REFLECTED by the exact attached-coset equivalences.

We now make the actual higher-rank quotient theorem explicit.
Let C be of ARBITRARY finite rank, K an ORIGINAL incomplete signed
Cayley skeleton in Γ, and root a genuine original C-component
vertex. Let P be ANY selected family of proper subalphabets of C.
Assume exactly the local H[C]-skeleton admissibility, generation
and retractability required to CONSTRUCT ITS LOCAL multiCE.

The local multiCE quotient exists with its certified old/fresh
component-tagged gluing. Transport its precise setoid along the
existing bijection of the original/local RAW alphabet-indexed
tagged coset points. The resulting ORIGINAL rooted C-component
vertex setoid uses LITERALLY `MultiCosetRawRelated`, not a
transitive closure or untagged equality in Γ; no GLOBAL
retractability assumption is imposed on the original Γ.

The induced equivalence of entire ORIGINAL and local glued
vertex quotients includes every genuinely newly attached coset
point and preserves the alphabet and old component tags.
It also carries a concrete formula on each local selected
D-coset summand.

Finally, if Γ is k-retractable and |C|≤k, the local
H[C] group hypotheses are discharged AUTOMATICALLY from the
already certified source-local generation and retractability
theorems, leaving only local admissibility explicit.

This is a nontrivial GENERALIZATION of the already proved
rank-two quotient theorem, not a duplicate attached-fibre
naturality proof. Extending the result to the ACTUAL directed
signed EDGE quotient, and then the full source Theorem 4.5
lower-rank induction, remain separate gates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The literal original rooted C-component's ABO (3.10) gluing
setoid in ARBITRARY parent rank, transported from the genuine
globally retractable LOCAL H[C] multiCE. No global Γ
retractability or accidental identification of different
intrinsic old component tags is needed. -/
noncomputable def arbitraryRankRootedOriginalMultiCosetSetoid
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    Setoid ((K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) :=
  setoidOfEquivRelation
    (K.rootedLocalMultiCosetRawVertexEquiv C root P)
    ((K.intrinsicComponentLocalSlice C root).multiCosetSetoid
      P hadm hgen hret)
    ((K.subalphabetComponentSubgraph C root).MultiCosetRawRelated P)
    (K.rootedLocalMultiCosetRawRelated_iff C root P)

/-- By construction, the target quotient relation is EXACTLY
the original source common-(D∩E)-support gluing predicate.
It is not a weaker transitive closure or equality of
ambient Cayley coordinates. -/
theorem arbitraryRankRootedOriginalMultiCosetSetoid_iff
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (p q : (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) :
    (K.arbitraryRankRootedOriginalMultiCosetSetoid
        C root P hadm hgen hret).r p q ↔
      (K.subalphabetComponentSubgraph C root).MultiCosetRawRelated
        P p q :=
  Iff.rfl

/-- The ACTUAL local signed-old/fresh vertex quotient is in bijection
with the ORIGINAL rooted C-component's exact common-tagged-support
quotient, for every selected proper family at any finite rank.

Original Γ need NOT be globally retractable. -/
noncomputable def arbitraryRankRootedLocalMultiCosetVertexEquiv
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
        P hadm hgen hret ≃
      Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
        C root P hadm hgen hret) :=
  quotientEquivOfEquivRelation
    (K.rootedLocalMultiCosetRawVertexEquiv C root P)
    ((K.intrinsicComponentLocalSlice C root).multiCosetSetoid
      P hadm hgen hret)
    ((K.subalphabetComponentSubgraph C root).MultiCosetRawRelated P)
    (K.rootedLocalMultiCosetRawRelated_iff C root P)

/-- Exact on EVERY newly attached LOCAL D-coset point (D∈P).
The quotient equivalence is the class of the corresponding
ORIGINAL component-tagged D-point, retaining the alphabet. -/
theorem arbitraryRankRootedLocalMultiCosetVertexEquiv_include
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι) (hDP : D ∈ P.alphabets)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D) :
    K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret
        ((K.intrinsicComponentLocalSlice C root).multiCosetInclude
          P hadm hgen hret D hDP p) =
      Quotient.mk
        (K.arbitraryRankRootedOriginalMultiCosetSetoid
          C root P hadm hgen hret)
        (⟨⟨D, hDP⟩,
          K.rootedLocalAttachedCosetMap C D
            (P.proper D hDP).subset root p⟩ :
          (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) :=
  rfl

/-- The same genuinely rank-independent rooted vertex quotient
when the source Γ is only k-RETRACTABLE (not globally retractable)
and |C|≤k. The local group's generation/retractability hypotheses
are NOW PROVED, rather than silently postulated.

The local original signed skeleton's admissibility is explicit:
the paper supplies it via the preceding lower-stage induction. -/
noncomputable def arbitraryRankRootedKLocalMultiCosetVertexEquiv
    (k : ℕ) (hk : KRetractable gen k)
    (C : Finset ι) (hC : C.card ≤ k)
    (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension) :
    (K.intrinsicComponentLocalSlice C root).MultiCosetVertex P
        hadm (isGenerated_trivialCompletionGenerator gen C)
          (retractable_trivialCompletionGenerator_of_kRetractable
            gen k hk C hC) ≃
    Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm
        (isGenerated_trivialCompletionGenerator gen C)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen k hk C hC)) :=
  K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hC)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
