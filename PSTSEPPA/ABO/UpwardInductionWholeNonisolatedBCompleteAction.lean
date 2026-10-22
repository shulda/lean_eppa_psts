import PSTSEPPA.ABO.UpwardInductionOutsideBComponentPermutations
import PSTSEPPA.ABO.UpwardInductionPermutationExtensionToFreshCoset
import PSTSEPPA.ABO.UpwardInductionWholeBComponentReplacementCarrier
import PSTSEPPA.ABO.AugmentedClusterTrivialStage

/-!
# ACTUAL complete signed action of the nonisolated whole-B-component H augmentation

This builds the concrete COMPLETE signed EGraph underlying the
corrected ABO Theorem 4.7(iii) full-B-coset blow-up of an ENTIRE
ORIGINAL B-component, not a misleading isolated-root gluing.

Start with an incomplete deterministic signed old H EGraph G,
locally paired positive/negative labels, a CHOSEN REAL original
B-connected component (all ORIGINAL quotient tags retained),
and an injective signed-cluster group-coordinate map from
that component into ONE genuine full H[B] coset.

The previously certified exact carrier is
  (original OLD vertices OUTSIDE chosen true B-component)
        ⊕ (ENTIRE H[B] coset).
The original old-vertex embedding is injective; the right
coset inclusion is also injective.

For EVERY generator i the stage defines a REAL permutation:
* i∈B: take the disjoint sum of (a) the original legal
  signed i-action RESTRICTED to the outside of the
  chosen B-component (certified invariant by #925/#926)
  and (b) the TRUE full coset i-permutation of the
  actual signed H[B] Cayley coset, including all old
  selected-component vertices and newly fresh ones.
* i∉B: extend the actual old signed i-permutation of G
  ALONG its INJECTIVE old-vertex map, fixing all
  genuinely fresh full-coset vertices. This retains
  old transitions crossing the selected B-component
  boundary, which the naive outside/coset disjoint
  union construction would incorrectly destroy.

The resulting `actionGraph` is a genuine complete signed
EGraph on exactly the intended old+fresh carrier, with
both oriented edge tokens and inverse generator actions.
This is a CONCRETE, not assumed, completed action stage.

Remaining: prove that the actual old G signed edge-token
graph maps into this stage using compatibility of the
certified canonical B-component coordinates with old
B-edges; construct the full-coset signed embedding and
the correctly based Cayley(G) cover. The generated full
reflection and PSTS EPPA are not asserted here.
-/

namespace PSTSEPPA
namespace ABO

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace IsolatedCosetGluing

/-- The literal signed full coset has paired outgoing
positive/negative labels at every point: each B-generator
appears in BOTH directions and no outside-B generator
appears in either direction. Thus LEGAL completion only
adds stationary loops on the latter labels. -/
theorem fullCoset_locallyPairedLabels
    (gen : ι → Γ) (B : Finset ι) (g : Γ) :
    ((fullCosetSubgraph gen B g).toEGraph).LocallyPairedLabels := by
  apply (fullCosetSubgraph gen B g).locallyPairedLabels_of_sameSourceOpposite
  intro e he
  refine ⟨he.1, ?_⟩
  change signedBase (PSTS.SignedLetter.inv e.2) ∈ B
  simpa only [signedBase_inv] using he.2

/-- The ACTUAL complete signed full H[B]-coset action.
Every B-labelled signed edge was already genuinely
present; only missing outside-B labels become loops. -/
noncomputable def fullBCosetCompleteAction
    (gen : ι → Γ) (B : Finset ι) (g : Γ) :
    CompleteEGraph (CosetPoint gen B g)
      (ActionEdge (CosetPoint gen B g) ι) ι :=
  ((fullCosetSubgraph gen B g).toEGraph).trivialLoopCompletion
    (fullCoset_locallyPairedLabels gen B g)

end IsolatedCosetGluing

namespace EGraph

/-- The actual complete signed action of a SINGLE original
nonisolated component replacement. All i∈B actions are
REAL full H[B] coset actions or unchanged old complement
actions; all i∉B actions are genuine old H permutations
extended along an INJECTION and fix only truly fresh
new coset points. No fictional old signed edge is used. -/
noncomputable def wholeOriginalBComponentAugmentedStage
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (hcoord : Function.Injective coord) :
    CompleteEGraph
      (G.FullBComponentReplacementVertex gen B anchor g)
      (ActionEdge
        (G.FullBComponentReplacementVertex gen B anchor g) ι) ι :=
  actionGraph (fun i =>
    if hi : i ∈ B then
      Equiv.Perm.sumCongr
        (G.loopCompletedOutsideBPermutation
          hpaired B anchor i hi)
        ((IsolatedCosetGluing.fullBCosetCompleteAction
          gen B g).letterPerm (.pos i))
    else
      extendPermAlongEmbedding
        (G.originalVertexToFullBReplacement gen B anchor g coord)
        (G.originalVertexToFullBReplacement_injective
          gen B anchor g coord hcoord)
        (G.loopCompletedPermutation hpaired i))

/-- For i∈B the complete nonisolated augmented H stage
ACTUALLY acts on a right-summand full B-coset point
by the original full coset i-permutation. No fixed-loop
substitution or old-component coordinate collapse. -/
theorem wholeOriginalBComponentAugmentedStage_B_on_coset
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (hcoord : Function.Injective coord)
    (i : ι) (hi : i ∈ B)
    (p : IsolatedCosetGluing.CosetPoint gen B g) :
    (G.wholeOriginalBComponentAugmentedStage
        hpaired gen B anchor g coord hcoord).letterPerm (.pos i)
      (Sum.inr p) =
    Sum.inr
      ((IsolatedCosetGluing.fullBCosetCompleteAction
        gen B g).letterPerm (.pos i) p) := by
  change
    (if h : i ∈ B then
      Equiv.Perm.sumCongr
        (G.loopCompletedOutsideBPermutation
          hpaired B anchor i h)
        ((IsolatedCosetGluing.fullBCosetCompleteAction
          gen B g).letterPerm (.pos i))
     else
       extendPermAlongEmbedding
         (G.originalVertexToFullBReplacement gen B anchor g coord)
         (G.originalVertexToFullBReplacement_injective
           gen B anchor g coord hcoord)
         (G.loopCompletedPermutation hpaired i)) (Sum.inr p) =
      Sum.inr
        ((IsolatedCosetGluing.fullBCosetCompleteAction
          gen B g).letterPerm (.pos i) p)
  rw [dif_pos hi]
  rfl

/-- On each old vertex OUTSIDE the chosen true B-component,
every i∈B transition is EXACTLY the old legal completed
H i-permutation restricted to that outside subset. -/
theorem wholeOriginalBComponentAugmentedStage_B_on_oldOutside
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (hcoord : Function.Injective coord)
    (i : ι) (hi : i ∈ B)
    (p : G.OutsideOriginalBComponent B anchor) :
    (G.wholeOriginalBComponentAugmentedStage
        hpaired gen B anchor g coord hcoord).letterPerm (.pos i)
      (Sum.inl p) =
    Sum.inl
      (G.loopCompletedOutsideBPermutation
        hpaired B anchor i hi p) := by
  change
    (if h : i ∈ B then
      Equiv.Perm.sumCongr
        (G.loopCompletedOutsideBPermutation
          hpaired B anchor i h)
        ((IsolatedCosetGluing.fullBCosetCompleteAction
          gen B g).letterPerm (.pos i))
     else
       extendPermAlongEmbedding
         (G.originalVertexToFullBReplacement gen B anchor g coord)
         (G.originalVertexToFullBReplacement_injective
           gen B anchor g coord hcoord)
         (G.loopCompletedPermutation hpaired i)) (Sum.inl p) =
      Sum.inl
        (G.loopCompletedOutsideBPermutation
          hpaired B anchor i hi p)
  rw [dif_pos hi]
  rfl

/-- Crucially a generator i OUTSIDE B still performs the
EXACT original H transition on the embedded OLD vertex,
even if the old edge crosses into/out of the selected
nonisolated B-component. Its inverse is likewise the
real old negative signed transition. -/
theorem wholeOriginalBComponentAugmentedStage_outsideB_old
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (hcoord : Function.Injective coord)
    (i : ι) (hi : i ∉ B) (v : V) :
    (G.wholeOriginalBComponentAugmentedStage
        hpaired gen B anchor g coord hcoord).letterPerm (.pos i)
      (G.originalVertexToFullBReplacement gen B anchor g coord v) =
    G.originalVertexToFullBReplacement gen B anchor g coord
      (G.loopCompletedStep (.pos i) v) := by
  change
    (if h : i ∈ B then
      Equiv.Perm.sumCongr
        (G.loopCompletedOutsideBPermutation
          hpaired B anchor i h)
        ((IsolatedCosetGluing.fullBCosetCompleteAction
          gen B g).letterPerm (.pos i))
     else
       extendPermAlongEmbedding
         (G.originalVertexToFullBReplacement gen B anchor g coord)
         (G.originalVertexToFullBReplacement_injective
           gen B anchor g coord hcoord)
         (G.loopCompletedPermutation hpaired i))
       (G.originalVertexToFullBReplacement gen B anchor g coord v) =
     G.originalVertexToFullBReplacement gen B anchor g coord
       (G.loopCompletedStep (.pos i) v)
  rw [dif_neg hi]
  exact extendPermAlongEmbedding_old_action
    (G.originalVertexToFullBReplacement gen B anchor g coord)
    (G.originalVertexToFullBReplacement_injective
      gen B anchor g coord hcoord)
    (G.loopCompletedPermutation hpaired i) v

end EGraph
end ABO
end PSTSEPPA
