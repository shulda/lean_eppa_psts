import PSTSEPPA.ABO.RootedMultiCosetRawGraphNaturality
import PSTSEPPA.ABO.SourceLabelEdgeQuotientGraphIso
import PSTSEPPA.ABO.MultiCosetEGraph

/-!
# TRUE source-rooted multi-coset completed EGraph isomorphism

This is the first source-facing assembly of all component-tagged quotient
geometry at rank two. The ambient Γ need only be 2-retractable.

For the actual signed A-component M of an incomplete Γ-Cayley source
cover, translate to its intrinsic Γ[A] local skeleton L. At the local
side, the complete proper-alphabet coset-extension quotient EGraph
has a source-and-label-to-target congruence by global retractability
OF Γ[A], even though ambient Γ need not be globally retractable.

The certified equivalence of genuine glued vertex quotients (#380)
and the source/local RAW signed graph isomorphism (#386) transport this
target congruence back to M. Thus the ORIGINAL source-rooted
multi-coset quotient has an honest deterministic EGraph, preserving
the literal vertex gluing relation and identifying oriented edge
tokens precisely by equal GLUED SOURCE and equal SIGNED LABEL.

The general exact quotient graph isomorphism (#385) then gives
bijectivity on both vertices and signed edge classes, and reflection
as well as preservation of every genuinely realised signed path.

This theorem concerns the plain multi-coset extension. Outside-A
trivial completion, genuine B-augmentation, corrected ABO Condition
5.2 and higher-rank induction remain separate mathematical gates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- Source-and-signed-label-to-target congruence for the true
LOCAL Γ[A] raw multi-coset graph. This is a direct consequence
of the certified global-retractability multi-coset geometry of
Γ[A]; it never assumes global retractability of ambient Γ. -/
theorem rootedLocalMultiCosetRawGraph_target_congruent
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A) :
    (K.rootedLocalMultiCosetRawGraph A hcard hret root P).SourceLabelTargetCongruent := by
  let L := K.intrinsicComponentLocalSlice A root
  let hadm := L.admissible_of_card_le_two hcard.le
  let hgen := isGenerated_trivialCompletionGenerator gen A
  let hretL :=
    retractable_trivialCompletionGenerator_of_kRetractable
      gen 2 hret A hcard.le
  intro e f hs hl
  change
    L.multiCosetRawEdgeSource P hadm hgen hretL
      (L.multiCosetRawEdgeInv P e) =
    L.multiCosetRawEdgeSource P hadm hgen hretL
      (L.multiCosetRawEdgeInv P f)
  rw [L.multiCosetRawEdgeSource_inv P hadm hgen hretL e,
      L.multiCosetRawEdgeSource_inv P hadm hgen hretL f]
  exact L.multiCosetTargetCongruent_of_admissible
    P hadm hgen hretL e f ⟨hs, hl⟩

/-- The original ambient-rooted H1 multi-coset raw edge relation
has the SAME true target congruence, transported by a bijection
of signed raw graphs. Global Γ retractability is not used. -/
theorem rootedAmbientMultiCosetRawGraph_target_congruent
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A) :
    (K.rootedAmbientMultiCosetRawGraph A hcard hret root P).SourceLabelTargetCongruent :=
  sourceLabelTargetCongruent_transport
    (K.rootedLocalMultiCosetRawGraph A hcard hret root P)
    (K.rootedAmbientMultiCosetRawGraph A hcard hret root P)
    (K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret root P)
    (K.rootedLocalMultiCosetRawEdgeEquiv A root P)
    (K.rootedMultiCosetRawGraph_source_natural A hcard hret root P)
    (K.rootedMultiCosetRawGraph_label_natural A hcard hret root P)
    (fun e => (K.rootedMultiCosetRawGraph_inv_natural
      A hcard hret root P e).symm)
    (K.rootedLocalMultiCosetRawGraph_target_congruent A hcard hret root P)

/-- The deterministic completed multi-coset EGraph of the local
Γ[A] representative, using the literal glued vertex setoid and the
literal source+signed-label EDGE quotient. -/
noncomputable abbrev rootedLocalMultiCosetCompletedEGraph
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A) :=
  sourceLabelGraphQuotientEGraph
    (K.rootedLocalMultiCosetRawGraph A hcard hret root P)
    (K.rootedLocalMultiCosetRawGraph_target_congruent A hcard hret root P)

/-- The corresponding deterministic EGraph of the TRUE original
source-rooted Γ-Cayley component, now certified even if Γ is only
2-retractable. Its edges remember exact component tags at the
vertex level and are identified only by glued source + signed label. -/
noncomputable abbrev rootedAmbientMultiCosetCompletedEGraph
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A) :=
  sourceLabelGraphQuotientEGraph
    (K.rootedAmbientMultiCosetRawGraph A hcard hret root P)
    (K.rootedAmbientMultiCosetRawGraph_target_congruent A hcard hret root P)

/-- ACTUAL source/local labelled graph ISOMORPHISM of the full
multi-coset signed EGraph quotients. Every original old outside-B
edge and every freshly attached inside-B coset edge is preserved
without inventing non-existing signed edges. -/
noncomputable def rootedMultiCosetCompletedEGraphHom
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A) :
    LabelledGraphHom
      (K.rootedLocalMultiCosetCompletedEGraph
        A hcard hret root P).toLabelledGraph
      (K.rootedAmbientMultiCosetCompletedEGraph
        A hcard hret root P).toLabelledGraph :=
  sourceLabelGraphQuotientHom
    (K.rootedLocalMultiCosetRawGraph A hcard hret root P)
    (K.rootedAmbientMultiCosetRawGraph A hcard hret root P)
    (K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret root P)
    (K.rootedLocalMultiCosetRawEdgeEquiv A root P)
    (K.rootedMultiCosetRawGraph_source_natural A hcard hret root P)
    (K.rootedMultiCosetRawGraph_label_natural A hcard hret root P)
    (fun e => (K.rootedMultiCosetRawGraph_inv_natural
      A hcard hret root P e).symm)
    (K.rootedLocalMultiCosetRawGraph_target_congruent A hcard hret root P)
    (K.rootedAmbientMultiCosetRawGraph_target_congruent A hcard hret root P)

/-- The source H1 and local H1[A] completed multi-coset graphs are
bijective on ALL glued vertices and on actual signed oriented
edge CLASSES, not only on ambient group coordinates. -/
theorem rootedMultiCosetCompletedEGraphHom_bijective
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A) :
    Function.Bijective
      (K.rootedMultiCosetCompletedEGraphHom A hcard hret root P).onVertex ∧
    Function.Bijective
      (K.rootedMultiCosetCompletedEGraphHom A hcard hret root P).onEdge := by
  exact sourceLabelGraphQuotientHom_bijective
    (K.rootedLocalMultiCosetRawGraph A hcard hret root P)
    (K.rootedAmbientMultiCosetRawGraph A hcard hret root P)
    (K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret root P)
    (K.rootedLocalMultiCosetRawEdgeEquiv A root P)
    (K.rootedMultiCosetRawGraph_source_natural A hcard hret root P)
    (K.rootedMultiCosetRawGraph_label_natural A hcard hret root P)
    (fun e => (K.rootedMultiCosetRawGraph_inv_natural
      A hcard hret root P e).symm)
    (K.rootedLocalMultiCosetRawGraph_target_congruent A hcard hret root P)
    (K.rootedAmbientMultiCosetRawGraph_target_congruent A hcard hret root P)

/-- The full plain source multi-coset completion realises PRECISELY
the signed paths realised by its true local Γ[A] completion. Handles
formal inverse letters, missing old edges, loops and parallel labels. -/
theorem rootedMultiCosetCompletedEGraphHom_follows_iff
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) (P : CosetFamilySpec A)
    (u v : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex P
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (w : LabelWord ι) :
    (K.rootedLocalMultiCosetCompletedEGraph
      A hcard hret root P).Follows u w v ↔
    (K.rootedAmbientMultiCosetCompletedEGraph
      A hcard hret root P).Follows
        ((K.rootedMultiCosetCompletedEGraphHom A hcard hret root P).onVertex u)
        w
        ((K.rootedMultiCosetCompletedEGraphHom A hcard hret root P).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (K.rootedMultiCosetCompletedEGraphHom A hcard hret root P)
    (K.rootedMultiCosetCompletedEGraphHom_bijective A hcard hret root P).1
    (K.rootedMultiCosetCompletedEGraphHom_bijective A hcard hret root P).2
    u v w

end CayleySubgraphSpec
end ABO
end PSTSEPPA
