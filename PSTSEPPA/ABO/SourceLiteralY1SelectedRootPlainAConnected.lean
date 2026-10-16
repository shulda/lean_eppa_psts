import PSTSEPPA.ABO.RootedComponentCompletedMultiCosetConnectivity
import PSTSEPPA.ABO.RootedSourceAllProperCompletedStageIso
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainStageIso
import PSTSEPPA.ABO.BasedCayleyLocalAlphabetStageCoverage

/-!
# Exact connectedness and local cover of the whole PRINTED rooted P_A stage

True old rooted A-components are signed A-connected.
Our newly verified-or-pending full multiCE connectivity
lifts this property to all genuinely tagged old/fresh
coset vertices, and legal missing-loop completion
preserves it.

Use actual local SourceH₁[A] to original source H₁
and printed T(Y₁) bijective signed graph morphisms
to prove the ENTIRE selected printed P_A complete
stage is reachable from any root by a supported
chronological signed A-word.

Therefore the genuine local T(X₂^all)[A] subgroup
Cayley action, not just the whole first-rank group,
surjects onto every printed selected stage vertex.
No ambient quotient folds differently tagged points.
Theorem 4.7(ii)/(iii), selection equivariance,
Condition 5.2 and PSTS EPPA remain OPEN.
-/

namespace PSTSEPPA
namespace ABO

namespace CompleteEGraph

variable {ι V E W F : Type*}
variable {A : Finset ι}

/-- Every stage point can be reached from each other
by a chronological signed word supported inside A. -/
def AWordConnected (T : CompleteEGraph V E ι) (A : Finset ι) : Prop :=
  ∀ u v : V, ∃ w : LabelWord ι,
    LabelWord.Uses A w ∧ T.followWord u w = v

/-- A genuinely surjective labelled signed stage map
transports full A-word connectedness. -/
theorem AWordConnected_of_surjective
    (G : CompleteEGraph V E ι)
    (H : CompleteEGraph W F ι)
    (f : LabelledGraphHom
      G.toEGraph.toLabelledGraph H.toEGraph.toLabelledGraph)
    (hf : Function.Surjective f.onVertex)
    (hG : G.AWordConnected A) :
    H.AWordConnected A := by
  intro u v
  obtain ⟨x, hx⟩ := hf u
  obtain ⟨y, hy⟩ := hf v
  obtain ⟨w, hw, hxy⟩ := hG x y
  refine ⟨w, hw, ?_⟩
  calc
    H.followWord u w = H.followWord (f.onVertex x) w := by rw [hx]
    _ = f.onVertex (G.followWord x w) := H.hom_followWord G f x w
    _ = f.onVertex y := congrArg f.onVertex hxy
    _ = v := hy

/-- A vertex-injective signed complete stage map
reflects A-word connectedness from its target. -/
theorem AWordConnected_of_injective
    (G : CompleteEGraph V E ι)
    (H : CompleteEGraph W F ι)
    (f : LabelledGraphHom
      G.toEGraph.toLabelledGraph H.toEGraph.toLabelledGraph)
    (hf : Function.Injective f.onVertex)
    (hH : H.AWordConnected A) :
    G.AWordConnected A := by
  intro u v
  obtain ⟨w, hw, hxy⟩ := hH (f.onVertex u) (f.onVertex v)
  refine ⟨w, hw, ?_⟩
  apply hf
  calc
    f.onVertex (G.followWord u w) =
        H.followWord (f.onVertex u) w :=
      (H.hom_followWord G f u w).symm
    _ = f.onVertex v := hxy

end CompleteEGraph

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The actual SourceH₁ rooted P_A COMPLETE stage is
A-connected on every old and fresh signed vertex. -/
theorem sourceH1OriginalRootPlain_AWordConnected
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst) :
    (sourceH1OriginalRootPlainCompleteStage
      src dst base A hcard root).AWordConnected A := by
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let L := K.intrinsicComponentLocalSlice A r
  let hret := sourceH1_twoRetractable src dst
  let P := allProperCosetFamily A
  let hadm := L.admissible_of_card_le_two hcard.le
  let hgen := isGenerated_trivialCompletionGenerator
    (sourceH1Generator src dst) A
  let hretL := retractable_trivialCompletionGenerator_of_kRetractable
    (sourceH1Generator src dst) 2 hret A hcard.le
  let T := K.rootedLocalAllProperCompletedStage A hcard hret r
  let U := K.rootedAmbientAllProperCompletedStage A hcard hret r
  let f := K.rootedAllProperCompletedStageHom A hcard hret r
  have hLocal : T.AWordConnected A := by
    exact L.completedMultiCoset_A_connected_of_old_connected
      P hadm hgen hretL
      (K.rootedLocalAllProperMultiCoset_locallyPairedLabels
        A hcard hret r)
      (K.genuineComponentLocalSlice_connected A r)
  have hAmbient : U.AWordConnected A :=
    T.AWordConnected_of_surjective U f
      (K.rootedAllProperCompletedStageHom_bijective
        A hcard hret r).1.2 hLocal
  exact hAmbient

/-- The TRUE printed paper T(Y₁) selected rooted
P_A plain completed action is one signed A-component,
without collapsing distinct component-tagged points. -/
theorem sourceLiteralY1SelectedRootPlain_AWordConnected
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedRootPlainCompleteStage
      src dst base A hcard root).AWordConnected A := by
  let G := sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root
  let H := sourceH1OriginalRootPlainCompleteStage
    src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root)
  let f := sourceLiteralY1SelectedRootPlainCompleteStageHom
    src dst base A hcard root
  have hSource : H.AWordConnected A :=
    sourceH1OriginalRootPlain_AWordConnected
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root)
  exact G.AWordConnected_of_injective H f
    (sourceLiteralY1SelectedRootPlainCompleteStageHom_bijective
      src dst base A hcard root).1.1 hSource

/-- The actual LOCAL first-rank subgroup
T(X₂^all)[A] maps surjectively to ALL printed
root-selected plain P_A complete-stage vertices.
This proves entire-stage coverage, not just a
partial source orbit. -/
theorem sourceLiteralY1X2AllPrintedPlain_localA_vertex_surjective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A))) :
    Function.Surjective
      (fun x : generatedSubgroup
        (sourceLiteralY1X2AllGenerator src dst) A =>
        (sourceLiteralY1X2AllPrintedPlainCayleyHom
          src dst base A hcard root u).onVertex x.1) := by
  intro v
  have hv :=
    (sourceLiteralY1SelectedRootPlain_AWordConnected
      src dst base A hcard root) u v
  exact ((Set.ext_iff.mp
    (sourceLiteralY1X2AllPrintedPlain_localA_vertex_range
      src dst base A hcard root u)) v).2 hv

end ABO
end PSTSEPPA
