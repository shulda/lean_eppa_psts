import PSTSEPPA.ABO.UpwardInductionWholeNonisolatedBCompleteAction

/-!
# TRUE signed full H[B]-coset embedding into the nonisolated completed augmentation

The new entire-component augmented H-stage is a REAL complete
signed action on old vertices outside a chosen original B-component
and all vertices of ONE full H[B] coset. Unlike the isolated-root
model, genuine old signed B-edges already exist inside the original
chosen component and are retained through their signed canonical
full-coset embedding.

This module shows that the new completed action contains the
entire genuine full H[B] coset as an ACTUAL signed graph subobject:
for BOTH positive AND formal inverse negative B edge labels,
the corresponding augmented-stage action on the right coset
summand is EXACTLY the full H[B]-coset permutation.

We then construct a REAL `LabelledGraphHom` from the original
INCOMPLETE full H[B]-coset EGraph into the COMPLETE new
nonisolated augmented H-stage, preserving actual directed
signed edge tokens, source, target and formal inverses.
Its vertex map is literally `Sum.inr` and is injective.

We do NOT embed the entire loop-completed stage in
Cayley(H): an outside-B old edge or newly stationary
loop would generally prohibit such a map. We only embed
the actual full B-coset, precisely as needed in the
published upward Theorem 4.7(iii) H-word reflection.
The old-H→new-stage morphism and based Cayley(G) cover
remain separate source-geometric proof steps.
-/

namespace PSTSEPPA
namespace ABO

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace IsolatedCosetGluing

/-- An ORIGINAL signed full coset edge stays an ACTUAL
signed edge after legal completion. Its completed-stage
signed permutation sends the genuine source to precisely
the original full coset target. -/
theorem fullBCosetCompleteAction_existing_signed_step
    (gen : ι → Γ) (B : Finset ι) (g : Γ)
    (e : (fullCosetSubgraph gen B g).Edge) :
    (fullBCosetCompleteAction gen B g).letterPerm
        ((fullCosetSubgraph gen B g).toEGraph.label e)
        ((fullCosetSubgraph gen B g).toEGraph.source e) =
      (fullCosetSubgraph gen B g).toEGraph.target e := by
  let K := (fullCosetSubgraph gen B g).toEGraph
  let T := fullBCosetCompleteAction gen B g
  have hOriginal :
      T.target (K.source e, K.label e) = K.target e := by
    exact K.trivialLoopCompletion_target_existing
      (fullCoset_locallyPairedLabels gen B g) e
  have hEdgeAt :
      T.edgeAt (K.source e) (K.label e) = (K.source e, K.label e) := by
    apply T.edgeAt_eq
    · rfl
    · rfl
  change T.target (T.edgeAt (K.source e) (K.label e)) = K.target e
  exact (congrArg T.target hEdgeAt).trans hOriginal

end IsolatedCosetGluing

namespace EGraph

/-- The fully constructed NONISOLATED whole-component
augmented stage agrees with the genuine complete full
H[B]-coset on every TRUE B-supported signed label,
including its formal inverse NEGATIVE orientation. -/
theorem wholeOriginalBComponentAugmentedStage_signed_B_on_coset
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (hcoord : Function.Injective coord)
    (s : SignedLabel ι) (hs : signedBase s ∈ B)
    (p : IsolatedCosetGluing.CosetPoint gen B g) :
    (G.wholeOriginalBComponentAugmentedStage
      hpaired gen B anchor g coord hcoord).letterPerm s
        (Sum.inr p) =
      Sum.inr
        ((IsolatedCosetGluing.fullBCosetCompleteAction
          gen B g).letterPerm s p) := by
  let T := G.wholeOriginalBComponentAugmentedStage
    hpaired gen B anchor g coord hcoord
  let C := IsolatedCosetGluing.fullBCosetCompleteAction gen B g
  cases s with
  | pos i =>
      change i ∈ B at hs
      exact G.wholeOriginalBComponentAugmentedStage_B_on_coset
        hpaired gen B anchor g coord hcoord i hs p
  | neg i =>
      change i ∈ B at hs
      have hTNeg : T.letterPerm (.neg i) =
          (T.letterPerm (.pos i)).symm :=
        T.letterPerm_inv (.pos i)
      have hCNeg : C.letterPerm (.neg i) =
          (C.letterPerm (.pos i)).symm :=
        C.letterPerm_inv (.pos i)
      have hTBack :
          T.letterPerm (.pos i)
            (T.letterPerm (.neg i) (Sum.inr p)) =
              Sum.inr p := by
        rw [hTNeg]
        exact (T.letterPerm (.pos i)).apply_symm_apply (Sum.inr p)
      have hCBack :
          C.letterPerm (.pos i) (C.letterPerm (.neg i) p) = p := by
        rw [hCNeg]
        exact (C.letterPerm (.pos i)).apply_symm_apply p
      have hForward :
          T.letterPerm (.pos i)
              (Sum.inr (C.letterPerm (.neg i) p)) =
            Sum.inr (C.letterPerm (.pos i)
              (C.letterPerm (.neg i) p)) :=
        G.wholeOriginalBComponentAugmentedStage_B_on_coset
          hpaired gen B anchor g coord hcoord i hs
            (C.letterPerm (.neg i) p)
      apply (T.letterPerm (.pos i)).injective
      calc
        T.letterPerm (.pos i)
            (T.letterPerm (.neg i) (Sum.inr p)) =
              Sum.inr p := hTBack
        _ = Sum.inr
              (C.letterPerm (.pos i) (C.letterPerm (.neg i) p)) :=
                congrArg Sum.inr hCBack.symm
        _ = T.letterPerm (.pos i)
              (Sum.inr (C.letterPerm (.neg i) p)) :=
                hForward.symm

/-- An actual signed full B-coset directed edge gives
exactly the same target in the new nonisolated complete
stage when the source is included by `Sum.inr`. -/
theorem wholeOriginalBComponentAugmentedStage_fullBCoset_target
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (hcoord : Function.Injective coord)
    (e : (IsolatedCosetGluing.fullCosetSubgraph gen B g).Edge) :
    (G.wholeOriginalBComponentAugmentedStage
       hpaired gen B anchor g coord hcoord).target
      (Sum.inr
        ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph.source e),
        (IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph.label e) =
      Sum.inr
        ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph.target e) := by
  let T := G.wholeOriginalBComponentAugmentedStage
    hpaired gen B anchor g coord hcoord
  let K := (IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph
  have hs : signedBase (K.label e) ∈ B := e.2.2
  have hStageStep :
      T.target (Sum.inr (K.source e), K.label e) =
        T.letterPerm (K.label e) (Sum.inr (K.source e)) := by
    have hEdgeAt :
        T.edgeAt (Sum.inr (K.source e)) (K.label e) =
          (Sum.inr (K.source e), K.label e) := by
      apply T.edgeAt_eq
      · rfl
      · rfl
    calc
      T.target (Sum.inr (K.source e), K.label e) =
        T.target (T.edgeAt (Sum.inr (K.source e)) (K.label e)) :=
          congrArg T.target hEdgeAt.symm
      _ = T.letterPerm (K.label e) (Sum.inr (K.source e)) := rfl
  rw [hStageStep]
  rw [G.wholeOriginalBComponentAugmentedStage_signed_B_on_coset
    hpaired gen B anchor g coord hcoord (K.label e) hs (K.source e)]
  exact congrArg Sum.inr
    (IsolatedCosetGluing.fullBCosetCompleteAction_existing_signed_step
      gen B g e)

/-- The actual FULL ORIGINAL signed H[B]-coset embeds in the
new whole-component complete stage as a label/source/inverse
preserving EGraph morphism. No condition of OLD B-edge
absence and no globally injective original H CE projection. -/
noncomputable def fullBCosetToWholeOriginalBComponentStageHom
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (hcoord : Function.Injective coord) :
    LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph).toLabelledGraph
      (G.wholeOriginalBComponentAugmentedStage
        hpaired gen B anchor g coord hcoord).toEGraph.toLabelledGraph where
  onVertex := Sum.inr
  onEdge e :=
    (Sum.inr
      ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph.source e),
      (IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph.label e)
  map_source e := rfl
  map_inv e := by
    apply Prod.ext
    · exact
        (G.wholeOriginalBComponentAugmentedStage_fullBCoset_target
          hpaired gen B anchor g coord hcoord e).symm
    · exact
        ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph).label_inv e
  map_label e := rfl

/-- Injectivity of the TRUE full H[B]-coset inclusion into
the actual completed nonisolated whole-component stage. -/
theorem fullBCosetToWholeOriginalBComponentStageHom_vertex_injective
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (hcoord : Function.Injective coord) :
    Function.Injective
      (G.fullBCosetToWholeOriginalBComponentStageHom
        hpaired gen B anchor g coord hcoord).onVertex := by
  intro p q hpq
  exact Sum.inr.inj hpq

end EGraph
end ABO
end PSTSEPPA
