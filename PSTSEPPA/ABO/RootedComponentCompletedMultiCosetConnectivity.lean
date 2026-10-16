import PSTSEPPA.ABO.MultiCosetParentComponentExact
import PSTSEPPA.ABO.IntrinsicComponentLocalSliceIso
import PSTSEPPA.ABO.LocalCosetCayleyPaths
import PSTSEPPA.ABO.TrivialLoopCompletion
import PSTSEPPA.ABO.StandardCosetFamily

/-!
# Entire genuinely rooted A-components and their full multi-coset completions are A-connected

A selected old source component in corrected ABO Theorem 4.7
is determined by genuine signed A-paths, not membership in
a potentially larger ambient A-subgroup coset.

We make a fundamental geometric fact completely explicit:

1. The literal intrinsic old B-component of ANY original
   incomplete signed Cayley skeleton is internally
   B-connected. This uses REAL supported paths in the
   original old graph and their already-certified lifts
   into the component subgraph, not artificial edges.
2. Its genuine translated LOCAL subgroup slice in Γ[B]
   remains B-connected, by the certified signed path
   equivalence for root translations.
3. Any component-tagged full multi-coset extension over
   a connected original A-skeleton, whose constituent
   alphabets all lie inside A, is A-connected ON ALL
   actual old/fresh quotient VERTICES. This uses the
   already-certified characterization of the exact
   A-path components by intrinsic parent component tags.
4. Legally inserting ONLY absent signed stationary loops
   into this weakly complete multi-CE does not destroy
   the actual signed A-paths. Therefore its WHOLE
   completed vertex carrier, not just a guessed ambient
   A-coset, is A-word reachable from ANY chosen root.

These facts are independent of group finiteness and do
not assume global injectivity of ambient coordinates,
generator faithfulness or incorrectly collapse distinct
intrinsic B-component tags. Original inverse signs and
geometric loops are preserved.

For the source rank-two A-root, this is the path from
the accepted LOCAL G[A] orbit coverage lemma to a
FULL reachable-stage Cayley cover. Instantiating the
precise printed T(Y₁) plain P_A completed EGraph
requires transporting connectedness along the actual
already-certified source/local signed graph equivalence;
that is the subsequent source-facing gate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

/-- The actual old B-component is B-CONNECTED on ALL its
inherited original vertices, not just contained in one
ambient B-coset. Even missing original edges remain absent. -/
theorem genuineComponent_connected
    (K : CayleySubgraphSpec gen A)
    (B : Finset ι) (root : K.Vertex) :
    ∀ x y : (K.subalphabetComponentSubgraph B root).Vertex,
      (K.subalphabetComponentSubgraph B root).SubalphabetReachable B x y := by
  intro x y
  obtain ⟨ux, hux, hrootx⟩ := x.2
  obtain ⟨uy, huy, hrooty⟩ := y.2
  have hxy : K.SubalphabetReachable B ux uy :=
    K.subalphabetReachable_trans B
      (K.subalphabetReachable_symm B hrootx) hrooty
  obtain ⟨hrooty', hLift⟩ :=
    K.reachable_lift_component B B (subset_rfl) root ux uy
      hrootx hxy
  have heqx :
      K.componentLiftVertex B root ux hrootx = x :=
    Subtype.ext hux
  have heqy :
      K.componentLiftVertex B root uy hrooty' = y :=
    Subtype.ext huy
  simpa only [heqx, heqy] using hLift

/-- The precise source-rooted old component, translated by
the chosen genuine root to the local generated subgroup
Γ[B], has the SAME internal signed B-connectivity.
No assumption that the original old graph was complete. -/
theorem genuineComponentLocalSlice_connected
    (K : CayleySubgraphSpec gen A)
    (B : Finset ι) (root : K.Vertex) :
    ∀ x y : (K.intrinsicComponentLocalSlice B root).Vertex,
      (K.intrinsicComponentLocalSlice B root).SubalphabetReachable B x y := by
  let M := K.subalphabetComponentSubgraph B root
  intro x y
  exact (M.leftCosetSlice_subalphabetReachable_iff root.1 B x y).mpr
    (K.genuineComponent_connected B root
      ((M.leftCosetSliceHom root.1).onVertex x)
      ((M.leftCosetSliceHom root.1).onVertex y))

/-- If a genuine incomplete A-skeleton is itself
A-connected on its REAL original vertices, then its
FULL tagged multiCE with constituents B⊆A is A-connected
on ALL original and attached quotient vertices. The
proof uses intrinsic A-COMPONENT INDICES rather than
ambient group coordinate equality. -/
theorem multiCosetEGraph_connected_of_old_connected
    (K : CayleySubgraphSpec gen A)
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hConnected : ∀ x y : K.Vertex,
      K.SubalphabetReachable A x y) :
    ∀ x y : K.MultiCosetVertex P hadm hgen hret,
      ∃ w : LabelWord ι,
        LabelWord.Uses A w ∧
          (K.multiCosetEGraph P hadm hgen hret).Follows x w y := by
  have hAll (c d : K.ComponentIndex A) : c = d := by
    induction c using Quotient.inductionOn with
    | h x =>
        induction d using Quotient.inductionOn with
        | h y =>
            exact (K.componentClass_eq_iff A x y).mpr (hConnected x y)
  intro x y
  exact (K.multiCosetEGraph_B_reachable_iff_parent_index
    P hadm hgen hret A
      (fun C hCP => (P.proper C hCP).subset) x y).mpr
        (hAll _ _)

/-- Complete only MISSING signed labels by stationary loops:
the genuine A-connected old/fresh multi-CE remains
A-connected as a complete signed action. No new
nonloop edges are used by the witnessing words. -/
theorem completedMultiCoset_A_connected_of_old_connected
    (K : CayleySubgraphSpec gen A)
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hpaired :
      (K.multiCosetEGraph P hadm hgen hret).LocallyPairedLabels)
    (hConnected : ∀ x y : K.Vertex,
      K.SubalphabetReachable A x y) :
    ∀ x y : K.MultiCosetVertex P hadm hgen hret,
      ∃ w : LabelWord ι,
        LabelWord.Uses A w ∧
          ((K.multiCosetEGraph P hadm hgen hret).trivialLoopCompletion
            hpaired).followWord x w = y := by
  let G := K.multiCosetEGraph P hadm hgen hret
  let T := G.trivialLoopCompletion hpaired
  intro x y
  obtain ⟨w, hw, hOld⟩ :=
    K.multiCosetEGraph_connected_of_old_connected
      P hadm hgen hret hConnected x y
  refine ⟨w, hw, ?_⟩
  have hCompleted : T.toEGraph.Follows x w y :=
    hOld.map (G.trivialLoopCompletionHom hpaired)
  have hCanonical : T.toEGraph.Follows x w (T.followWord x w) :=
    T.follows_followWord x w
  exact T.toEGraph.follows_right_unique hCanonical hCompleted

end CayleySubgraphSpec
end ABO
end PSTSEPPA
