import PSTSEPPA.ABO.AugmentedOldComponentCayleyAgreement
import PSTSEPPA.ABO.IsolatedCosetCompletedBOrbitDetector

/-!
# TRUE rooted type-(2) augmentation detector on ONE original signed path

Corrected ABO 4.7(iii) is NOT performed on the entire old
G[A] quotient pullback: the latter may have many original
signed A-components. The already certified generalized
based old-lift agreement requires global connectedness
of the domain original signed EGraph.

We remove that need. Given ANY genuine original signed
EGraph L, two actual signed morphisms
  S : L → Cayley(G)    M : L → H-old,
and a based signed Cayley(G) → legal type-(2) augmented
H completion map F, agreement on ONE old basepoint
forces agreement on ANY second old vertex x connected
to that basepoint by an ACTUAL old signed path.
We do not assume that unrelated L-components are
connected or that the whole pullback embeds.

Combining this with the certified type-(2) B-word
kernel converse and B-stability of labelled G→H
shows: any such reached old vertex x in the ambient
G[B]-coset of that root has exactly the same G group
coordinate. If S is injective on those two specific
old vertices, they are identical.

This is tailored to the accepted SOURCE #648 theorem:
the entire genuine old+fresh G[A] root-selected region
is one A-connected actual EGraph component, although
the full original G[A] multiCE is generally disconnected.

This is a rigorously proved generic *conditional
interface*: source work still needs the actual G/H
full signed old multiCE morphism (the current #655)
and the concrete based source type-(2) augmentation
for each off-B root. It does not add an axiom, make
up original edges, or prove general 4.7(iii), R8,
Condition 5.2, higher ranks, or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {X Y E OldEdge ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

namespace EGraph

/-- Signed old-lift agreement from ONE actually realised
signed path, not from global connectedness of L.
Both OLD signed morphisms are genuine graph morphisms;
the complete-stage map is only used on images of
those actual original edge tokens. -/
theorem basedAugmentedOldLift_agrees_of_path
    (L : EGraph X E ι)
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
    (base x : X)
    (hBased : F.onVertex (S.onVertex base) =
      Sum.inl (M.onVertex base))
    (hRealPath : ∃ w : LabelWord ι, L.Follows base w x) :
    F.onVertex (S.onVertex x) =
      Sum.inl (M.onVertex x) := by
  let Aug := IsolatedCosetGluing.gluedEGraph
    H genΔ B g root hMissing
  let hAugPaired : Aug.LocallyPairedLabels :=
    IsolatedCosetGluing.glued_locallyPairedLabels
      H genΔ B g root hMissing hpaired
  let T := IsolatedCosetGluing.completedStage
    H genΔ B g root hMissing hpaired
  obtain ⟨w, hPath⟩ := hRealPath
  have hProjected : T.toEGraph.Follows
      (F.onVertex (S.onVertex base)) w
      (F.onVertex (S.onVertex x)) :=
    (hPath.map S).map F
  have hOld : H.Follows
      (M.onVertex base) w (M.onVertex x) :=
    hPath.map M
  have hGlued : Aug.Follows
      (Sum.inl (M.onVertex base)) w
      (Sum.inl (M.onVertex x)) :=
    hOld.map (IsolatedCosetGluing.oldHom
      H genΔ B g root hMissing)
  have hOldCompleted : T.toEGraph.Follows
      (Sum.inl (M.onVertex base)) w
      (Sum.inl (M.onVertex x)) :=
    hGlued.map (Aug.trivialLoopCompletionHom hAugPaired)
  rw [hBased] at hProjected
  exact T.toEGraph.follows_right_unique hProjected hOldCompleted

/-- B-stable group quotient plus true original signed
path-based old H compatibility detects UNIQUE G group
coordinate in a selected old basepoint's ambient B-coset.

The only reachability hypothesis is ONE actual old path
base→x. The whole disconnected L is not assumed connected. -/
theorem basedAugmentedOldLift_B_orbit_coordinate_isolated_of_path
    (L : EGraph X E ι)
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
    (base x : X)
    (hOldRoot : M.onVertex base = root)
    (hBased : F.onVertex (S.onVertex base) = Sum.inl root)
    (hRealPath : ∃ w : LabelWord ι, L.Follows base w x)
    (hCoset : S.onVertex x ∈
      generatedLeftCoset genΓ B (S.onVertex base)) :
    S.onVertex x = S.onVertex base := by
  have hBase : F.onVertex (S.onVertex base) =
      Sum.inl (M.onVertex base) := by
    rw [hOldRoot]
    exact hBased
  have hOldImage : F.onVertex (S.onVertex x) =
      Sum.inl (M.onVertex x) :=
    L.basedAugmentedOldLift_agrees_of_path
      H genΓ genΔ B g root hMissing hpaired
      S M F base x hBase hRealPath
  have hGroupEq := LabelledGroupQuotient.augmentedStage_old_B_orbit_injective
    genΓ genΔ Q B hStable
    H g root hMissing hpaired F
    (S.onVertex base) (S.onVertex x)
    hBased ⟨M.onVertex x, hOldImage⟩ hCoset
  exact hGroupEq.symm

/-- Even local vertex injectivity at the PARTICULAR pair
base,x suffices. This matches the first-rank ambient
coordinate map proved injective on ONE rooted A-region,
not on the disconnected full original G multiCE. -/
theorem basedAugmentedOldLift_B_orbit_vertex_isolated_of_path
    (L : EGraph X E ι)
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
    (base x : X)
    (hOldRoot : M.onVertex base = root)
    (hBased : F.onVertex (S.onVertex base) = Sum.inl root)
    (hRealPath : ∃ w : LabelWord ι, L.Follows base w x)
    (hCoset : S.onVertex x ∈
      generatedLeftCoset genΓ B (S.onVertex base))
    (hInjPair : S.onVertex x = S.onVertex base → x = base) :
    x = base := by
  apply hInjPair
  exact L.basedAugmentedOldLift_B_orbit_coordinate_isolated_of_path
    H genΓ genΔ Q B hStable
    g root hMissing hpaired S M F
    base x hOldRoot hBased hRealPath hCoset

end EGraph
end ABO
end PSTSEPPA
