import PSTSEPPA.ABO.UpwardInductionOriginalBComponentSignedFullCosetEmbedding
import PSTSEPPA.ABO.UpwardInductionWholeNonisolatedBCosetSignedHom

/-!
# ACTUAL original signed H EGraph embeds in the nonisolated whole-B H-stage

The corrected source ABO upward Theorem 4.7(iii), proper n>=2 case,
blows up an ENTIRE actual original H B-component, not just an
isolated old point. The newly constructed COMPLETE H-stage has
vertex carrier (old ORIGINAL vertices outside component) ⊕ full H[B] coset.

The SOURCE forward Theorem4.5 supplies a real vertex-and-SIGNED-
EDGE-bijective isomorphism of the selected ORIGINAL old H B-component
with a canonical root-translated B-cluster. The certified canonical
cluster→full H[B] inclusion gives a TRUE ORIGINAL signed B-component
morphism cHom into the full coset, injective on ORIGINAL tagged vertices.

Using exactly this signed component morphism, we prove that EVERY
ACTUAL original signed H edge (not just vertices!) is preserved by
the concrete COMPLETE nonisolated H-stage:
  * for a label outside B, the original old permutation is
    extended ALONG THE INJECTIVE ORIGINAL-vertex inclusion.
    This works even for original old edges crossing the chosen
    B-component boundary;
  * for a B-labelled edge whose ORIGINAL source is outside
    the chosen B-component, its target is outside too, and
    the old restricted complement permutation is preserved;
  * for a B-labelled edge whose ORIGINAL source belongs to
    the selected component, the genuine original signed
    B-component→full coset graph morphism, followed by the
    ACTUAL signed full coset→new stage embedding, carries
    the original old directed edge and its TRUE target.
  * inverse NEGATIVE oriented edges are preserved by applying
    the positive case to the genuine formal inverse old edge,
    then using the already-certified inverse permutation law.

We then construct the REAL labelled EGraph morphism from the
ENTIRE original incomplete signed H graph to the completed
new H-stage, preserving every original vertex and both oriented
old edge tokens. Original unrelated component tags are never
identified by equality of ambient H group coordinates.

This is the actual old-H inclusion i needed alongside the
full-coset inclusion J (#932) for source Theorem4.7(iii).
The original H stage is not assumed globally injective into
Cayley(H); in particular no nonexistent old edge is inserted.
The remaining obligations are source selection/history and
the correctly based Cayley(G) cover F.
-/

namespace PSTSEPPA
namespace ABO

variable {V OldEdge W StageEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace EGraph

/-- Any REAL labelled morphism of an arbitrary incomplete signed
old EGraph into a COMPLETE signed EGraph preserves the precise
one-letter transition endpoint. The proof uses a genuine old
signed edge, not a hypothetical edge at a missing label. -/
theorem signedStep_of_labelledHom_into_complete
    (H : EGraph V OldEdge ι)
    (T : CompleteEGraph W StageEdge ι)
    (f : LabelledGraphHom H.toLabelledGraph T.toEGraph.toLabelledGraph)
    (e : OldEdge) :
    T.letterPerm (H.label e) (f.onVertex (H.source e)) =
      f.onVertex (H.target e) := by
  have hOld : H.Follows (H.source e) [H.label e] (H.target e) :=
    EGraph.Follows.cons e rfl rfl (EGraph.Follows.nil (H.target e))
  have hMapped := hOld.map f
  have hUnique :
      T.followWord (f.onVertex (H.source e)) [H.label e] =
        f.onVertex (H.target e) :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord (f.onVertex (H.source e)) [H.label e])
      hMapped
  rw [T.followWord_cons, T.followWord_nil] at hUnique
  exact hUnique

/-- Every ORIGINAL positive i-edge maps to the exact signed
transition of the new entire-component H-stage, with
NO restriction of the source to the chosen B-component.
The actual signed B-component→full H[B] coset morphism is
the only input beyond the genuine old graph and local
paired signed-label completion. -/
theorem wholeOriginalBComponent_positive_old_edge
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (cHom : LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph).toLabelledGraph)
    (hcInjective : Function.Injective cHom.onVertex)
    (e : OldEdge) (i : ι)
    (heLabel : G.label e = .pos i) :
    (G.wholeOriginalBComponentAugmentedStage
      hpaired gen B anchor g cHom.onVertex hcInjective).letterPerm (.pos i)
      (G.originalVertexToFullBReplacement
        gen B anchor g cHom.onVertex (G.source e)) =
    G.originalVertexToFullBReplacement
      gen B anchor g cHom.onVertex (G.target e) := by
  let T := G.wholeOriginalBComponentAugmentedStage
    hpaired gen B anchor g cHom.onVertex hcInjective
  let j := G.originalVertexToFullBReplacement
    gen B anchor g cHom.onVertex
  by_cases hi : i ∈ B
  · by_cases hInside : G.source e ∈ G.BComponentVertexSet B anchor
    · have hEdgeB : e ∈ G.BComponentEdgeSet B anchor := by
        constructor
        · rw [heLabel]
          exact hi
        · exact hInside
      have hTargetInside :
          G.target e ∈ G.BComponentVertexSet B anchor :=
        G.BComponentEdge_target_mem B anchor e hEdgeB
      let C := G.BComponentEGraph B anchor
      let J := G.fullBCosetToWholeOriginalBComponentStageHom
        hpaired gen B anchor g cHom.onVertex hcInjective
      let F := J.comp cHom
      have hMapped :
          T.letterPerm (.pos i)
            (Sum.inr (cHom.onVertex ⟨G.source e, hInside⟩)) =
          Sum.inr (cHom.onVertex ⟨G.target e, hTargetInside⟩) := by
        have hStep :=
          C.signedStep_of_labelledHom_into_complete
            T F ⟨e, hEdgeB⟩
        change
          T.letterPerm (G.label e)
            (Sum.inr (cHom.onVertex ⟨G.source e, hInside⟩)) =
          Sum.inr (cHom.onVertex ⟨G.target e, hTargetInside⟩) at hStep
        rw [heLabel] at hStep
        exact hStep
      change T.letterPerm (.pos i) (j (G.source e)) = j (G.target e)
      dsimp only [j]
      rw [G.originalVertexToFullBReplacement_inside
        gen B anchor g cHom.onVertex (G.source e) hInside]
      rw [G.originalVertexToFullBReplacement_inside
        gen B anchor g cHom.onVertex (G.target e) hTargetInside]
      exact hMapped
    · have hTargetOutside :
          G.target e ∉ G.BComponentVertexSet B anchor := by
        have hPres := G.loopCompletedStep_outside_BComponent
          hpaired B anchor (.pos i) hi (G.source e) hInside
        simpa only [G.loopCompletedStep_of_edge
          (.pos i) (G.source e) e rfl heLabel] using hPres
      let u : G.OutsideOriginalBComponent B anchor :=
        ⟨G.source e, hInside⟩
      let v : G.OutsideOriginalBComponent B anchor :=
        ⟨G.target e, hTargetOutside⟩
      have hSignedOutside :
          G.loopCompletedOutsideBPermutation
            hpaired B anchor i hi u = v := by
        apply Subtype.ext
        calc
          (G.loopCompletedOutsideBPermutation
              hpaired B anchor i hi u).1 =
              G.loopCompletedStep (.pos i) (G.source e) :=
            G.loopCompletedOutsideBPermutation_value
              hpaired B anchor i hi u
          _ = G.target e :=
            G.loopCompletedStep_of_edge
              (.pos i) (G.source e) e rfl heLabel
      have hAction : T.letterPerm (.pos i) (Sum.inl u) =
          Sum.inl (G.loopCompletedOutsideBPermutation
            hpaired B anchor i hi u) :=
        G.wholeOriginalBComponentAugmentedStage_B_on_oldOutside
          hpaired gen B anchor g cHom.onVertex hcInjective i hi u
      change T.letterPerm (.pos i) (j (G.source e)) = j (G.target e)
      calc
        T.letterPerm (.pos i) (j (G.source e)) =
            T.letterPerm (.pos i) (Sum.inl u) := by
          dsimp only [j]
          rw [G.originalVertexToFullBReplacement_outside
            gen B anchor g cHom.onVertex (G.source e) hInside]
        _ = Sum.inl
              (G.loopCompletedOutsideBPermutation
                hpaired B anchor i hi u) := hAction
        _ = Sum.inl v := congrArg Sum.inl hSignedOutside
        _ = j (G.target e) := by
          dsimp only [j]
          rw [G.originalVertexToFullBReplacement_outside
            gen B anchor g cHom.onVertex (G.target e) hTargetOutside]
  · have hOld := G.wholeOriginalBComponentAugmentedStage_outsideB_old
      hpaired gen B anchor g cHom.onVertex hcInjective
      i hi (G.source e)
    have hStep :
        G.loopCompletedStep (.pos i) (G.source e) = G.target e :=
      G.loopCompletedStep_of_edge (.pos i) (G.source e) e rfl heLabel
    exact hOld.trans (congrArg j hStep)

/-- EVERY ORIGINAL signed directed old edge, including NEGATIVE
inverse tokens, has its exact original target in the new
whole-component nonisolated complete H-stage. -/
theorem wholeOriginalBComponent_old_signed_edge
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (cHom : LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph).toLabelledGraph)
    (hcInjective : Function.Injective cHom.onVertex)
    (e : OldEdge) :
    (G.wholeOriginalBComponentAugmentedStage
      hpaired gen B anchor g cHom.onVertex hcInjective).letterPerm
        (G.label e)
      (G.originalVertexToFullBReplacement
        gen B anchor g cHom.onVertex (G.source e)) =
    G.originalVertexToFullBReplacement
      gen B anchor g cHom.onVertex (G.target e) := by
  let T := G.wholeOriginalBComponentAugmentedStage
    hpaired gen B anchor g cHom.onVertex hcInjective
  let j := G.originalVertexToFullBReplacement
    gen B anchor g cHom.onVertex
  cases hs : G.label e with
  | pos i =>
      exact G.wholeOriginalBComponent_positive_old_edge
        hpaired gen B anchor g cHom hcInjective e i hs
  | neg i =>
      have hInvLabel : G.label (G.inv e) = .pos i := by
        rw [G.label_inv, hs]
        rfl
      have hPositive :=
        G.wholeOriginalBComponent_positive_old_edge
          hpaired gen B anchor g cHom hcInjective
          (G.inv e) i hInvLabel
      have hPositive' :
          T.letterPerm (.pos i) (j (G.target e)) =
            j (G.source e) := by
        simpa only [G.toLabelledGraph.target_inv] using hPositive
      have hNegative :
          T.letterPerm (.neg i) (j (G.source e)) =
            j (G.target e) := by
        apply (T.letterPerm (.pos i)).injective
        rw [T.letterPerm_inv (.pos i)]
        rw [Equiv.apply_symm_apply]
        exact hPositive'.symm
      simpa only [hs] using hNegative

/-- Generic graph-theoretic transport: any vertex map which
respects the TRUE one-letter endpoints of EVERY old signed
directed edge defines an actual labelled morphism from an
INCOMPLETE old graph into a COMPLETE signed EGraph. It uses
the actual old oriented signed edge tokens and the exact
target/inverse incidence, not inferred absent old edges. -/
noncomputable def labelledHomIntoCompleteOfSignedSteps
    (H : EGraph V OldEdge ι)
    (T : CompleteEGraph W StageEdge ι)
    (j : V → W)
    (hsteps : ∀ e : OldEdge,
      T.letterPerm (H.label e) (j (H.source e)) =
        j (H.target e)) :
    LabelledGraphHom H.toLabelledGraph T.toEGraph.toLabelledGraph where
  onVertex := j
  onEdge e := T.edgeAt (j (H.source e)) (H.label e)
  map_source e := T.edgeAt_source _ _
  map_label e := T.edgeAt_label _ _
  map_inv e := by
    have hOldTarget :
        j (H.source (H.inv e)) =
          T.target (T.edgeAt (j (H.source e)) (H.label e)) := by
      change j (H.target e) =
        T.letterPerm (H.label e) (j (H.source e))
      exact (hsteps e).symm
    calc
      T.edgeAt (j (H.source (H.inv e))) (H.label (H.inv e)) =
          T.edgeAt
            (T.target (T.edgeAt (j (H.source e)) (H.label e)))
            (PSTS.SignedLetter.inv (H.label e)) := by
        rw [hOldTarget, H.label_inv e]
      _ = T.inv (T.edgeAt (j (H.source e)) (H.label e)) :=
        T.edgeAt_inv _ _

/-- Construct the ACTUAL source-preserving, signed-label
and formal-inverse-preserving OLD H→new completed H-stage
labelled graph embedding, rather than postulating it. The
only selected-component input is the ORIGINAL genuine
signed B-component→full H[B] coset morphism; that is
constructed from forward source Theorem4.5 canonical
proper-cluster isomorphism in #931.

This old-H morphism preserves ALL original old edges in
both orientations, including edges with labels outside B
that cross between the chosen B-component and other
original old tagged vertices. -/
noncomputable def wholeOriginalBComponentOldSignedHom
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ) (B : Finset ι)
    (anchor : V) (g : Γ)
    (cHom : LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph gen B g).toEGraph).toLabelledGraph)
    (hcInjective : Function.Injective cHom.onVertex) :
    LabelledGraphHom
      G.toLabelledGraph
      (G.wholeOriginalBComponentAugmentedStage
        hpaired gen B anchor g cHom.onVertex hcInjective).toEGraph.toLabelledGraph :=
  G.labelledHomIntoCompleteOfSignedSteps
    (G.wholeOriginalBComponentAugmentedStage
      hpaired gen B anchor g cHom.onVertex hcInjective)
    (G.originalVertexToFullBReplacement
      gen B anchor g cHom.onVertex)
    (G.wholeOriginalBComponent_old_signed_edge
      hpaired gen B anchor g cHom hcInjective)

end EGraph
end ABO
end PSTSEPPA
