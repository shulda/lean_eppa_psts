import PSTSEPPA.ABO.IsolatedCosetCompletedBOrbitDetector
import PSTSEPPA.ABO.CayleySectionBridgeFreeness
import PSTSEPPA.ABO.IsolatedCosetCompletion

/-!
# Rooted signed old-lift agreement with a genuine type-(2) augmentation

Corrected ABO 4.7(iii) uses TWO different geometric maps:
* an actual ORIGINAL signed G multi-coset EGraph into the
  Cayley graph of a finite labelled G group;
* a genuine labelled map from those ORIGINAL old+fresh
  vertices into the OLD side of a selected H augmentation.

Separately, the source G action on every actual augmented
H stage supplies a based Cayley(G)→completed augmented-stage
labelled graph morphism. All these maps must AGREE on old
vertices, not merely on the ambient H group coordinate.

This file proves a GENERAL ROOTED COMPATIBILITY principle.

If the OLD signed G graph is connected from a chosen root,
and the composite Cayley(G)→completed augmented H-stage
agrees with the old H-image of that root at ONE basepoint,
it agrees with the old H-image of EVERY original G vertex.
Proof: follow a genuine signed old path in two ways;
the actual labelled graph morphisms and determinism force
exactly the same terminal VERTEX, preserving component tags.

Combine this principle with the newly certified type-(2)
detector: for a B-stable labelled quotient G↠H, the
ambient G[B]-coset of any original vertex mapping to
the old augmentation root can meet that connected
old graph in at most ONE ambient group coordinate.
If the original signed G→Cayley(G) map is injective,
the vertex itself is isolated inside that ambient B-orbit.

These are genuine proved SUFFICIENT CONDITIONS, not axioms.
To instantiate them for the full true first-rank rooted
multiCE, one must still build the exact component-restricted
signed old map to the H plain P_A extension and select the
correct actual printed type-(2) augmentation based at each
off-B root. Neither map is invented or assumed to be
automatically available from equality of H coordinates.

This is not yet unconditional Theorem 4.7(iii), the
separate R8 repair, higher ranks, Condition 5.2 or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {X Y Edge OldEdge ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

namespace EGraph

/-- Exact agreement of TWO genuinely signed routes from a
connected original G graph to a selected augmented H stage.

Route (1): original G edge path→ambient Cayley(G)→augmented H.
Route (2): original G edge path→original H old signed graph→
the OLD summand of the genuine H B-coset augmentation→its
LEGAL stationary-loop completion.

Agreement at the chosen old basepoint determines agreement
at EVERY old vertex. No group-coordinate identification
of different old H component tags is made. -/
theorem basedAugmentedOldLift_agrees_of_connected
    (L : EGraph X Edge ι)
    (H : EGraph Y OldEdge ι)
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (B : Finset ι) (g : Δ) (root : Y)
    (hMissing : ∀ e : OldEdge,
      H.source e = root → signedBase (H.label e) ∉ B)
    (hpaired : H.LocallyPairedLabels)
    (S : LabelledGraphHom
      L.toLabelledGraph
      (cayleyGraph genΓ).toEGraph.toLabelledGraph)
    (M : LabelledGraphHom L.toLabelledGraph H.toLabelledGraph)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (IsolatedCosetGluing.completedStage
        H genΔ B g root hMissing hpaired).toEGraph.toLabelledGraph)
    (base : X)
    (hBase : F.onVertex (S.onVertex base) =
      Sum.inl (M.onVertex base))
    (hConnected : ∀ x : X,
      ∃ w : LabelWord ι, L.Follows base w x)
    (x : X) :
    F.onVertex (S.onVertex x) = Sum.inl (M.onVertex x) := by
  let Aug := IsolatedCosetGluing.gluedEGraph
    H genΔ B g root hMissing
  let hAugPaired : Aug.LocallyPairedLabels :=
    IsolatedCosetGluing.glued_locallyPairedLabels
      H genΔ B g root hMissing hpaired
  let T := IsolatedCosetGluing.completedStage
    H genΔ B g root hMissing hpaired
  obtain ⟨w, hPath⟩ := hConnected x
  have hProjected : T.toEGraph.Follows
      (F.onVertex (S.onVertex base)) w
      (F.onVertex (S.onVertex x)) :=
    (hPath.map S).map F
  have hOldCompleted : T.toEGraph.Follows
      (Sum.inl (M.onVertex base)) w
      (Sum.inl (M.onVertex x)) := by
    have hOld : H.Follows
        (M.onVertex base) w (M.onVertex x) :=
      hPath.map M
    have hGlued : Aug.Follows
        (Sum.inl (M.onVertex base)) w
        (Sum.inl (M.onVertex x)) :=
      hOld.map (IsolatedCosetGluing.oldHom
        H genΔ B g root hMissing)
    exact hGlued.map (Aug.trivialLoopCompletionHom hAugPaired)
  rw [hBase] at hProjected
  exact T.toEGraph.follows_right_unique hProjected hOldCompleted

/-- The selected ORIGINAL old graph's ambient G[B]-coset
cannot contain two different OLD-image group coordinates
once a genuine H type-(2) augmented Cayley cover is based
at the correct off-B old H root and Q:G↠H is B-stable.

The compatibility on other old vertices is DEDUCED by
the preceding genuine signed path argument. We do NOT
assume the entire group-to-augmentation Cayley map
sends arbitrary G group points into its OLD part. -/
theorem basedAugmentedOldLift_B_orbit_coordinate_isolated
    (L : EGraph X Edge ι)
    (H : EGraph Y OldEdge ι)
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hStable : Q.StableAt B)
    (g : Δ) (root : Y)
    (hMissing : ∀ e : OldEdge,
      H.source e = root → signedBase (H.label e) ∉ B)
    (hpaired : H.LocallyPairedLabels)
    (S : LabelledGraphHom
      L.toLabelledGraph
      (cayleyGraph genΓ).toEGraph.toLabelledGraph)
    (M : LabelledGraphHom L.toLabelledGraph H.toLabelledGraph)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (IsolatedCosetGluing.completedStage
        H genΔ B g root hMissing hpaired).toEGraph.toLabelledGraph)
    (base : X)
    (hRoot : M.onVertex base = root)
    (hBased : F.onVertex (S.onVertex base) = Sum.inl root)
    (hConnected : ∀ x : X,
      ∃ w : LabelWord ι, L.Follows base w x)
    (x : X)
    (hCoset : S.onVertex x ∈
      generatedLeftCoset genΓ B (S.onVertex base)) :
    S.onVertex x = S.onVertex base := by
  have hBase : F.onVertex (S.onVertex base) =
      Sum.inl (M.onVertex base) := by
    rw [hRoot]
    exact hBased
  have hOldImage : F.onVertex (S.onVertex x) =
      Sum.inl (M.onVertex x) :=
    L.basedAugmentedOldLift_agrees_of_connected
      H genΓ genΔ B g root hMissing hpaired
      S M F base hBase hConnected x
  have hGroupEq :=
    LabelledGroupQuotient.augmentedStage_old_B_orbit_injective
      genΓ genΔ Q B hStable
      H g root hMissing hpaired F
      (S.onVertex base) (S.onVertex x)
      hBased ⟨M.onVertex x, hOldImage⟩ hCoset
  exact hGroupEq.symm

/-- If the ACTUAL original G-graph is already ambient
vertex-embedded (as in the accepted first-rank rooted
component theorem), then the off-B orbit detected above
contains the ORIGINAL old point alone, not just one
ambient group coordinate. -/
theorem basedAugmentedOldLift_B_orbit_vertex_isolated
    (L : EGraph X Edge ι)
    (H : EGraph Y OldEdge ι)
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hStable : Q.StableAt B)
    (g : Δ) (root : Y)
    (hMissing : ∀ e : OldEdge,
      H.source e = root → signedBase (H.label e) ∉ B)
    (hpaired : H.LocallyPairedLabels)
    (S : LabelledGraphHom
      L.toLabelledGraph
      (cayleyGraph genΓ).toEGraph.toLabelledGraph)
    (hInjective : Function.Injective S.onVertex)
    (M : LabelledGraphHom L.toLabelledGraph H.toLabelledGraph)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (IsolatedCosetGluing.completedStage
        H genΔ B g root hMissing hpaired).toEGraph.toLabelledGraph)
    (base : X)
    (hRoot : M.onVertex base = root)
    (hBased : F.onVertex (S.onVertex base) = Sum.inl root)
    (hConnected : ∀ x : X,
      ∃ w : LabelWord ι, L.Follows base w x)
    (x : X)
    (hCoset : S.onVertex x ∈
      generatedLeftCoset genΓ B (S.onVertex base)) :
    x = base := by
  apply hInjective
  exact L.basedAugmentedOldLift_B_orbit_coordinate_isolated
    H genΓ genΔ Q B hStable g root hMissing hpaired
    S M F base hRoot hBased hConnected x hCoset

end EGraph
end ABO
end PSTSEPPA
