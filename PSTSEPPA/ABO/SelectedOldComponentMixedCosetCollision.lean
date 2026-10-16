import PSTSEPPA.ABO.RootedOldComponentDeterminesHStageCover
import PSTSEPPA.ABO.PullbackAttachedCosetSupportReflection

/-!
# Source-sharp old A-component collision: no globally connected pullback

A subtle but essential scope improvement over the earlier rooted
stage theorem: the canonical G-pullback of an H-skeleton can be
DISCONNECTED in the original A-edge graph, even when the selected
H component is connected. Therefore it is too strong to demand
that EVERY old G vertex be A-connected to one fixed root.

Corrected ABO Theorem 4.7(ii) instead works with ONE selected
genuine old A-component. Here we prove the exact local rule.

Let F:Cayley(G)→the ACTUAL legally completed H multi-coset
stage be a signed labelled cover normalized at the correct
old G root r, i.e., F(1) equals its exact tagged old H image.

For any two genuine attached B/C G-coset vertices p,q:
* require a chosen original old B-anchor x of p and C-anchor
  y of q, and ACTUAL OLD A-paths r→x and r→y;
* require p and q to have the SAME ORIGINAL G-coordinate g;
* require Q:G↠H stable on B and C.

Then the root-normalized cover F(r⁻¹·) agrees with the OLD
H map at x,y by real signed old-path determinism (#611);
the true full B/C coset paths imply that F(r⁻¹ g)
is EXACTLY the tagged H image of p AND of q (#617).
Equality of these TWO H TAGGED vertices follows from
equality of their ORIGINAL G coordinate, NOT from false
global injectivity of H's ambient coset map. Finally
mixed-support reflection (#608) produces ONE actual
tagged old G (B∩C)-support witness. Thus p,q were
already glued in the genuine G coset quotient.

This is the source-critical MIXED-SUPPORT collision for
points lying above one selected old A-component, without
requiring the FULL canonical G pullback to be connected.
It does not construct source-selected Y_k/Z_k stages
or the required complete F, prove arbitrary cross-A
component collisions, condition 5.2, R8 bridge
freeness, higher induction, or ordinary PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- From ONE rooted original signed A-path r→x,
the correctly inverse-root-normalized complete stage
Cayley map equals the exact OLD H component-tagged
image of x, FOR ANY CHOSEN selected B constituent.
No global connectedness of the old pullback required. -/
theorem rootedOldStageCover_agrees_at_reachable_old_point
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (root : (K.pullbackQuotient Q).Vertex)
    (hOne :
      F.onVertex (1 : Γ) =
        (K.pullbackOldToWeakMultiCosetStageHom
          Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex root)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (x : (K.pullbackQuotient Q).Vertex)
    (hPath : (K.pullbackQuotient Q).SubalphabetReachable A root x) :
    F.onVertex (root.1⁻¹ * x.1) =
      K.multiCosetInclude P hAdmH hGenH hRetH B hBP
        (K.attachedOfSkeletonVertex B
          ((K.pullbackQuotientHom Q).onVertex x)) := by
  let old :=
    K.pullbackOldToWeakMultiCosetStageHom
      Q P hAdmH hGenH hRetH hweak B₀ hB₀
  have hAgree :=
    (K.pullbackQuotient Q).basedCayleyStage_agrees_on_old_component
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak)
      old F root hOne x hPath
  calc
    F.onVertex (root.1⁻¹ * x.1) = old.onVertex x := hAgree
    _ = (K.skeletonToMultiCosetHom P hAdmH hGenH hRetH B₀ hB₀).onVertex
          ((K.pullbackQuotientHom Q).onVertex x) := rfl
    _ = (K.skeletonToMultiCosetHom P hAdmH hGenH hRetH B hBP).onVertex
          ((K.pullbackQuotientHom Q).onVertex x) :=
        K.skeletonToMultiCosetHom_vertex_independent
          P hAdmH hGenH hRetH B₀ B hB₀ hBP
          ((K.pullbackQuotientHom Q).onVertex x)
    _ = K.multiCosetInclude P hAdmH hGenH hRetH B hBP
          (K.attachedOfSkeletonVertex B
            ((K.pullbackQuotientHom Q).onVertex x)) := rfl

/-- A genuine tagged attached full B-coset point p is
represented exactly by the one-root G-Cayley cover if
only ONE of its TRUE old B-component anchors x is
A-path-connected to the selected old root r.
All inverse signs and original component tags preserved. -/
theorem rootedOldStageCover_represents_attached_of_reachable_anchor
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (root : (K.pullbackQuotient Q).Vertex)
    (hOne :
      F.onVertex (1 : Γ) =
        (K.pullbackOldToWeakMultiCosetStageHom
          Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex root)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B)
    (x : (K.pullbackQuotient Q).Vertex)
    (hIndex : p.1 = (K.pullbackQuotient Q).componentClass B x)
    (hPath : (K.pullbackQuotient Q).SubalphabetReachable A root x) :
    F.onVertex (root.1⁻¹ * p.2.1) =
      K.multiCosetInclude P hAdmH hGenH hRetH B hBP
        (K.pullbackQuotient_attachedCosetToBase Q B p) := by
  let Froot : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph :=
    F.comp (cayleyLeftTranslateHom genΓ root.1⁻¹)
  have hAnchor :
      Froot.onVertex x.1 =
        K.multiCosetInclude P hAdmH hGenH hRetH B hBP
          (K.attachedOfSkeletonVertex B
            ((K.pullbackQuotientHom Q).onVertex x)) :=
    K.rootedOldStageCover_agrees_at_reachable_old_point
      Q P hAdmH hGenH hRetH hweak B₀ hB₀
      F root hOne B hBP x hPath
  exact K.weakMultiCosetCompletedStage_attached_representation_of_old_anchor
    Q P hAdmH hGenH hRetH hweak B hBP Froot x hAnchor p hIndex

/-- REAL mixed B/C (intersection-supported) tag collision
above ONE chosen old A-component. The two attached
points p,q MAY have entirely distinct B and C tags,
but if their group coordinates agree, they are already
related by one genuine old G (B∩C)-support witness.
No global connectedness or H ambient injectivity. -/
theorem rootedOldStageCover_mixedSupportCollision
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (root : (K.pullbackQuotient Q).Vertex)
    (hOne :
      F.onVertex (1 : Γ) =
        (K.pullbackOldToWeakMultiCosetStageHom
          Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex root)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (hBStable : Q.StableAt B) (hCStable : Q.StableAt C)
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B)
    (q : (K.pullbackQuotient Q).AttachedCosetVertex C)
    (x y : (K.pullbackQuotient Q).Vertex)
    (hIndexB : p.1 = (K.pullbackQuotient Q).componentClass B x)
    (hIndexC : q.1 = (K.pullbackQuotient Q).componentClass C y)
    (hReachX : (K.pullbackQuotient Q).SubalphabetReachable A root x)
    (hReachY : (K.pullbackQuotient Q).SubalphabetReachable A root y)
    (hGroup :
      (K.pullbackQuotient Q).attachedValue B p =
        (K.pullbackQuotient Q).attachedValue C q) :
    (K.pullbackQuotient Q).ShareIntersectionSupport B C p q := by
  have hTagB :=
    K.rootedOldStageCover_represents_attached_of_reachable_anchor
      Q P hAdmH hGenH hRetH hweak
      B₀ hB₀ F root hOne B hBP p x hIndexB hReachX
  have hTagC :=
    K.rootedOldStageCover_represents_attached_of_reachable_anchor
      Q P hAdmH hGenH hRetH hweak
      B₀ hB₀ F root hOne C hCP q y hIndexC hReachY
  have hEqH :
      K.multiCosetInclude P hAdmH hGenH hRetH B hBP
        (K.pullbackQuotient_attachedCosetToBase Q B p) =
      K.multiCosetInclude P hAdmH hGenH hRetH C hCP
        (K.pullbackQuotient_attachedCosetToBase Q C q) := by
    calc
      K.multiCosetInclude P hAdmH hGenH hRetH B hBP
          (K.pullbackQuotient_attachedCosetToBase Q B p) =
        F.onVertex (root.1⁻¹ *
          (K.pullbackQuotient Q).attachedValue B p) := hTagB.symm
      _ = F.onVertex (root.1⁻¹ *
          (K.pullbackQuotient Q).attachedValue C q) :=
        congrArg (fun g : Γ => F.onVertex (root.1⁻¹ * g)) hGroup
      _ = K.multiCosetInclude P hAdmH hGenH hRetH C hCP
          (K.pullbackQuotient_attachedCosetToBase Q C q) := hTagC
  have hShareH :
      K.ShareIntersectionSupport B C
        (K.pullbackQuotient_attachedCosetToBase Q B p)
        (K.pullbackQuotient_attachedCosetToBase Q C q) := by
    have h := Quotient.exact hEqH
    change K.ShareIntersectionSupport B C
      (K.pullbackQuotient_attachedCosetToBase Q B p)
      (K.pullbackQuotient_attachedCosetToBase Q C q) at h
    exact h
  exact K.pullbackQuotient_shareIntersectionSupport_reflect_of_equal_value
    Q B C hBStable hCStable p q hGroup hShareH

/-- Consequently the two original G attached points
are ALREADY equal in the genuine (B∩C)-supported G
full multiCE vertex quotient. This is the actual
vertex-embedding COLLISION conclusion restricted to
the root's old A-component (not to unrelated components). -/
theorem rootedOldStageCover_mixedSupportMultiCE_equal
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (root : (K.pullbackQuotient Q).Vertex)
    (hOne :
      F.onVertex (1 : Γ) =
        (K.pullbackOldToWeakMultiCosetStageHom
          Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex root)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (hBStable : Q.StableAt B) (hCStable : Q.StableAt C)
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B)
    (q : (K.pullbackQuotient Q).AttachedCosetVertex C)
    (x y : (K.pullbackQuotient Q).Vertex)
    (hIndexB : p.1 = (K.pullbackQuotient Q).componentClass B x)
    (hIndexC : q.1 = (K.pullbackQuotient Q).componentClass C y)
    (hReachX : (K.pullbackQuotient Q).SubalphabetReachable A root x)
    (hReachY : (K.pullbackQuotient Q).SubalphabetReachable A root y)
    (hGroup :
      (K.pullbackQuotient Q).attachedValue B p =
        (K.pullbackQuotient Q).attachedValue C q) :
    (K.pullbackQuotient Q).multiCosetInclude P hAdmG hGenG hRetG B hBP p =
      (K.pullbackQuotient Q).multiCosetInclude P hAdmG hGenG hRetG C hCP q := by
  apply Quotient.sound
  exact K.rootedOldStageCover_mixedSupportCollision
    Q P hAdmH hGenH hRetH hweak
    B₀ hB₀ F root hOne B C hBP hCP hBStable hCStable
    p q x y hIndexB hIndexC hReachX hReachY hGroup

end CayleySubgraphSpec
end ABO
end PSTSEPPA
