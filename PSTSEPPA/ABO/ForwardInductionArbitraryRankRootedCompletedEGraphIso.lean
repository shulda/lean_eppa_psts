import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedRawSignedGraph
import PSTSEPPA.ABO.SourceLabelEdgeQuotientGraphIso

/-!
# ABO Theorem 4.5: arbitrary-rank local/original complete SIGNED EGraph isomorphism

The existing corrected ABO rank-two cover theorem proves an exact
original/local coset completion isomorphism on actual oriented SIGNED
edge classes only when the parent alphabet has two letters. The prior
modules generalize its component-tagged VERTEX gluing quotient and
signed RAW edge-token graph to an arbitrary parent alphabet C.

The source's lower-rank forward induction needs the fully quotient
deterministic EGraph, not just a raw graph. We now formalize exactly
the remaining quotient step at ARBITRARY parent rank, conditional
on the genuine local H[C] admissibility/generation/retractability.

First, local admissibility supplies the true target-congruence theorem
for the source-and-FULL-signed-label equivalence on raw edges of the
LOCAL multi-coset extension. The already checked rank-independent
bijection on original/local raw edges, glued vertices, sources,
labels and formal inverses transports this congruence to the
ORIGINAL rooted ambient component -- NO global retractability of
the original Γ is assumed.

The accepted general source-and-label graph-quotient theorem then
constructs the exact deterministic EGraph on each side, with signed
inverse-edge token quotient, and a bijective LABELLED GRAPH HOM on
both the TRUE quotient vertices and every oriented signed edge class.
The bijection preserves and reflects every actually realized word
path, including its inverse letters, loops and missing old edges.

For k-retractable Γ, |C|≤k and local C-stage admissibility,
the local generation/retractability hypotheses have already been
certified; the result therefore directly applies to the genuine
H[C] subgroup used by ABO's forward induction, rather than
implicitly postulating global retractability of H.

No false signed edge is inserted into the original incomplete
skeleton. Exact old component tags are preserved even where
multiple components share an ambient Γ-coset.
The full forward induction and Condition 5.2 remain separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The locally normalized H[C] raw graph has source-and-signed-label
target congruence from the actual local admissibility hypothesis,
for ANY rank |C| and any selected proper-alphabet family P. -/
theorem arbitraryRankRootedLocalRawGraph_target_congruent
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    (K.arbitraryRankRootedLocalRawGraph
      C root P hadm hgen hret).SourceLabelTargetCongruent := by
  let L := K.intrinsicComponentLocalSlice C root
  intro e f hs hl
  change
    L.multiCosetRawEdgeSource P hadm hgen hret
      (L.multiCosetRawEdgeInv P e) =
    L.multiCosetRawEdgeSource P hadm hgen hret
      (L.multiCosetRawEdgeInv P f)
  rw [L.multiCosetRawEdgeSource_inv P hadm hgen hret e,
      L.multiCosetRawEdgeSource_inv P hadm hgen hret f]
  exact L.multiCosetTargetCongruent_of_admissible
    P hadm hgen hret e f ⟨hs, hl⟩

/-- The SAME target congruence is proved on the TRUE original
rooted C-component's signed raw coset graph by transportation.
This is the key reason no global Γ-retractability is needed. -/
theorem arbitraryRankRootedOriginalRawGraph_target_congruent
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    (K.arbitraryRankRootedOriginalRawGraph
      C root P hadm hgen hret).SourceLabelTargetCongruent :=
  sourceLabelTargetCongruent_transport
    (K.arbitraryRankRootedLocalRawGraph C root P hadm hgen hret)
    (K.arbitraryRankRootedOriginalRawGraph C root P hadm hgen hret)
    (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
      C root P hadm hgen hret)
    (K.rootedLocalMultiCosetRawEdgeEquiv C root P)
    (K.arbitraryRankRootedRawGraph_source_natural
      C root P hadm hgen hret)
    (K.arbitraryRankRootedRawGraph_label_natural
      C root P hadm hgen hret)
    (fun e => (K.arbitraryRankRootedRawGraph_inv_natural
      C root P hadm hgen hret e).symm)
    (K.arbitraryRankRootedLocalRawGraph_target_congruent
      C root P hadm hgen hret)

/-- Deterministic complete local multi-coset EGraph: quotient
oriented edge tokens by their ACTUAL glued source and entire
signed label, using only real old/fresh raw edges. -/
noncomputable abbrev arbitraryRankRootedLocalCompletedEGraph
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :=
  sourceLabelGraphQuotientEGraph
    (K.arbitraryRankRootedLocalRawGraph C root P hadm hgen hret)
    (K.arbitraryRankRootedLocalRawGraph_target_congruent
      C root P hadm hgen hret)

/-- The ORIGINAL rooted C-component completed EGraph, with
its exact original-component-tagged quotient vertices and TRUE
old+fresh oriented signed edge classes. The source ambient Γ
does NOT have to be globally retractable. -/
noncomputable abbrev arbitraryRankRootedOriginalCompletedEGraph
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :=
  sourceLabelGraphQuotientEGraph
    (K.arbitraryRankRootedOriginalRawGraph C root P hadm hgen hret)
    (K.arbitraryRankRootedOriginalRawGraph_target_congruent
      C root P hadm hgen hret)

/-- The exact source ABO 4.5 normalized H[C] versus ORIGINAL rooted
C-component labelled graph morphism on completed quotient graphs.

Both actual oriented signed edge CLASSES and old component-tagged
vertices are transported, not just group coordinates or raw edges. -/
noncomputable def arbitraryRankRootedCompletedEGraphHom
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    LabelledGraphHom
      (K.arbitraryRankRootedLocalCompletedEGraph
        C root P hadm hgen hret).toLabelledGraph
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).toLabelledGraph :=
  sourceLabelGraphQuotientHom
    (K.arbitraryRankRootedLocalRawGraph C root P hadm hgen hret)
    (K.arbitraryRankRootedOriginalRawGraph C root P hadm hgen hret)
    (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
      C root P hadm hgen hret)
    (K.rootedLocalMultiCosetRawEdgeEquiv C root P)
    (K.arbitraryRankRootedRawGraph_source_natural
      C root P hadm hgen hret)
    (K.arbitraryRankRootedRawGraph_label_natural
      C root P hadm hgen hret)
    (fun e => (K.arbitraryRankRootedRawGraph_inv_natural
      C root P hadm hgen hret e).symm)
    (K.arbitraryRankRootedLocalRawGraph_target_congruent
      C root P hadm hgen hret)
    (K.arbitraryRankRootedOriginalRawGraph_target_congruent
      C root P hadm hgen hret)

/-- The completed signed multiCE graph morphism is BIJECTIVE
on every ACTUAL quotient vertex AND every oriented signed edge
class, at arbitrary finite parent rank |C|. -/
theorem arbitraryRankRootedCompletedEGraphHom_bijective
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    Function.Bijective
      (K.arbitraryRankRootedCompletedEGraphHom
        C root P hadm hgen hret).onVertex ∧
    Function.Bijective
      (K.arbitraryRankRootedCompletedEGraphHom
        C root P hadm hgen hret).onEdge :=
  sourceLabelGraphQuotientHom_bijective
    (K.arbitraryRankRootedLocalRawGraph C root P hadm hgen hret)
    (K.arbitraryRankRootedOriginalRawGraph C root P hadm hgen hret)
    (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
      C root P hadm hgen hret)
    (K.rootedLocalMultiCosetRawEdgeEquiv C root P)
    (K.arbitraryRankRootedRawGraph_source_natural
      C root P hadm hgen hret)
    (K.arbitraryRankRootedRawGraph_label_natural
      C root P hadm hgen hret)
    (fun e => (K.arbitraryRankRootedRawGraph_inv_natural
      C root P hadm hgen hret e).symm)
    (K.arbitraryRankRootedLocalRawGraph_target_congruent
      C root P hadm hgen hret)
    (K.arbitraryRankRootedOriginalRawGraph_target_congruent
      C root P hadm hgen hret)

/-- GENUINE path preservation AND reflection through the
full old/fresh directed signed edge quotient. This is not
just equality of formal word values in an ambient group:
the two graphs have EXACTLY corresponding REAL signed paths. -/
theorem arbitraryRankRootedCompletedEGraphHom_follows_iff
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (u v : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) (w : LabelWord ι) :
    (K.arbitraryRankRootedLocalCompletedEGraph
      C root P hadm hgen hret).Follows u w v ↔
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).Follows
          ((K.arbitraryRankRootedCompletedEGraphHom
            C root P hadm hgen hret).onVertex u)
          w
          ((K.arbitraryRankRootedCompletedEGraphHom
            C root P hadm hgen hret).onVertex v) :=
  EGraph.follows_iff_bijective
    (K.arbitraryRankRootedCompletedEGraphHom
      C root P hadm hgen hret)
    (K.arbitraryRankRootedCompletedEGraphHom_bijective
      C root P hadm hgen hret).1
    (K.arbitraryRankRootedCompletedEGraphHom_bijective
      C root P hadm hgen hret).2 u v w

end CayleySubgraphSpec
end ABO
end PSTSEPPA
