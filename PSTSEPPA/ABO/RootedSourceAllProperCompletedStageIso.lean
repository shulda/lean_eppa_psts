import PSTSEPPA.ABO.RootedLocalCosetPairedLabels
import PSTSEPPA.ABO.LocallyPairedGraphIso
import PSTSEPPA.ABO.TrivialLoopCompletionIsomorphism

/-!
# True original rank-two source full proper-coset COMPLETE action equivalence

Take an actual rooted A-component (|A|=2) of an INCOMPLETE
Γ-Cayley skeleton, where Γ is merely 2-retractable. Its fully
component-tagged, signed multi-coset extension is already known
to be genuinely isomorphic to its normalized Γ[A] version (#390).

For P=P_A (ALL proper subalphabets), the local extension is WEAKLY
COMPLETE and hence has paired positive/negative outgoing labels
(#392). By the genuine signed graph isomorphism, the original
source-rooted extension also has this precise local pairing property:
missing edges of opposite signs must occur together.

Trivial fixed-loop completion is therefore LEGAL on both sides, and
the generic signed completion naturality (#388) upgrades the plain
source/local EGraph isomorphism to an isomorphism of COMPLETE signed
action graphs. Every signed-word path is preserved and REFLECTED,
including missing old edges that become fixed-point loops.

This closes the source-normalization comparison for ordinary
UN-AUGMENTED full proper-alphabet stages at rank two. It does NOT
match genuine B-augmented stages or prove complete source Z1
coverage, Condition 5.2, higher-rank induction or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The original rooted H1 rank-two FULL proper-coset EGraph has
exactly paired signed outgoing labels, using no global retractability
of the ambient group. This follows from the local Γ[A] theorem and
the actual bijection of all old and completed signed edge tokens. -/
theorem rootedAmbientAllProperMultiCoset_locallyPairedLabels
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex) :
    (K.rootedAmbientMultiCosetCompletedEGraph A hcard hret root
      (allProperCosetFamily A)).LocallyPairedLabels := by
  let P := allProperCosetFamily A
  let L := K.rootedLocalMultiCosetCompletedEGraph A hcard hret root P
  let M := K.rootedAmbientMultiCosetCompletedEGraph A hcard hret root P
  let f := K.rootedMultiCosetCompletedEGraphHom A hcard hret root P
  have hb := K.rootedMultiCosetCompletedEGraphHom_bijective
    A hcard hret root P
  have hp : L.LocallyPairedLabels :=
    K.rootedLocalAllProperMultiCoset_locallyPairedLabels
      A hcard hret root
  exact L.locallyPairedLabels_of_bijective M f hb.1 hb.2 hp

/-- The actual COMPLETE signed action of the local Γ[A]
multi-coset quotient, adding only missing stationary loops. -/
noncomputable abbrev rootedLocalAllProperCompletedStage
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex) :=
  (K.rootedLocalMultiCosetCompletedEGraph A hcard hret root
    (allProperCosetFamily A)).trivialLoopCompletion
      (K.rootedLocalAllProperMultiCoset_locallyPairedLabels
        A hcard hret root)

/-- The honest COMPLETE source-rooted action, where every
missing pair of signed edges contributes stationary loops,
not any artificial nonloop source H1-Cayley edges. -/
noncomputable abbrev rootedAmbientAllProperCompletedStage
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex) :=
  (K.rootedAmbientMultiCosetCompletedEGraph A hcard hret root
    (allProperCosetFamily A)).trivialLoopCompletion
      (K.rootedAmbientAllProperMultiCoset_locallyPairedLabels
        A hcard hret root)

/-- True vertex- and signed-edge-compatible morphism of COMPLETE
source/local P_A stage ACTION graphs. Positive and negative
transitions, formal inverses and fixed-point loops commute. -/
noncomputable def rootedAllProperCompletedStageHom
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex) :
    LabelledGraphHom
      (K.rootedLocalAllProperCompletedStage A hcard hret root).toEGraph.toLabelledGraph
      (K.rootedAmbientAllProperCompletedStage A hcard hret root).toEGraph.toLabelledGraph :=
  (K.rootedLocalMultiCosetCompletedEGraph A hcard hret root
    (allProperCosetFamily A)).trivialLoopCompletionIsoHom
      (K.rootedAmbientMultiCosetCompletedEGraph A hcard hret root
        (allProperCosetFamily A))
      (K.rootedMultiCosetCompletedEGraphHom A hcard hret root
        (allProperCosetFamily A))
      (K.rootedMultiCosetCompletedEGraphHom_bijective A hcard hret root
        (allProperCosetFamily A)).1
      (K.rootedMultiCosetCompletedEGraphHom_bijective A hcard hret root
        (allProperCosetFamily A)).2
      (K.rootedLocalAllProperMultiCoset_locallyPairedLabels A hcard hret root)
      (K.rootedAmbientAllProperMultiCoset_locallyPairedLabels A hcard hret root)

/-- The completed H1 original source stage and its true local
Γ[A] stage are bijective on ALL vertices and oriented signed
edges, including the newly inserted fixed-point loops. -/
theorem rootedAllProperCompletedStageHom_bijective
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex) :
    Function.Bijective
      (K.rootedAllProperCompletedStageHom A hcard hret root).onVertex ∧
    Function.Bijective
      (K.rootedAllProperCompletedStageHom A hcard hret root).onEdge := by
  exact
    (K.rootedLocalMultiCosetCompletedEGraph A hcard hret root
      (allProperCosetFamily A)).trivialLoopCompletionIsoHom_bijective
      (K.rootedAmbientMultiCosetCompletedEGraph A hcard hret root
        (allProperCosetFamily A))
      (K.rootedMultiCosetCompletedEGraphHom A hcard hret root
        (allProperCosetFamily A))
      (K.rootedMultiCosetCompletedEGraphHom_bijective A hcard hret root
        (allProperCosetFamily A)).1
      (K.rootedMultiCosetCompletedEGraphHom_bijective A hcard hret root
        (allProperCosetFamily A)).2
      (K.rootedLocalAllProperMultiCoset_locallyPairedLabels A hcard hret root)
      (K.rootedAmbientAllProperMultiCoset_locallyPairedLabels A hcard hret root)

/-- The completed original source H1 stage realises PRECISELY
the signed words/path endpoints of its local Γ[A] stage.
This is a true path equivalence, not agreement modulo an
ambient group word kernel. -/
theorem rootedAllProperCompletedStageHom_follows_iff
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (u v : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (w : LabelWord ι) :
    (K.rootedLocalAllProperCompletedStage A hcard hret root).toEGraph.Follows
      u w v ↔
    (K.rootedAmbientAllProperCompletedStage A hcard hret root).toEGraph.Follows
      ((K.rootedAllProperCompletedStageHom A hcard hret root).onVertex u)
      w
      ((K.rootedAllProperCompletedStageHom A hcard hret root).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (K.rootedAllProperCompletedStageHom A hcard hret root)
    (K.rootedAllProperCompletedStageHom_bijective A hcard hret root).1
    (K.rootedAllProperCompletedStageHom_bijective A hcard hret root).2
    u v w

end CayleySubgraphSpec
end ABO
end PSTSEPPA
