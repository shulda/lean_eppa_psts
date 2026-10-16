import PSTSEPPA.ABO.SelectedOldComponentMixedCosetCollision

/-!
# Actual full multiCE group-coordinate embedding ON a chosen OLD A-component

Corrected ABO Theorem 4.7(ii) must work with genuinely selected
OLD A-components of the original incomplete G-Cayley cover,
not the entire disconnected pullback. The certified theorem
`rootedOldStageCover_mixedSupportMultiCE_equal` proves exact
pairwise B/C gluing whenever both attached points are anchored
in one such connected old component.

This file packages that result as an honest INJECTIVITY
statement for the entire selected portion of the true
component-tagged G multi-coset vertex quotient.

The selected raw region consists of ALL B-attached original
G-coset points, over ALL chosen proper supports B, such that
their intrinsic original B-component has an actual OLD vertex
reached from one fixed selected original root by a genuine
signed A-path. This retains the full B-coset, NOT merely the
old vertices and NOT an ambient-coordinate quotient.
The region's image in the genuine full ABO (3.10) glued
quotient is independent of choosing particular B anchors.

A single G Cayley cover of the LEGALLY completed true H-stage,
normalized at that original root, makes the ambient G-group
coordinate projection INJECTIVE ON THIS SELECTED IMAGE.
This holds even when the full G-pullback is disconnected,
the H multiCE ambient projection is non-injective, and
different B/C tags share H coordinates.

This is the source-faithful COMPONENT-SCOPED embedding
consequence of the proved #619 collision theorem. It is
not a statement about all unrelated old G A-components,
does not construct the source-selected stage covering,
and does not prove Theorem 4.7(iii) bridge freeness,
Condition 5.2, higher induction or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ Edge : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- ALL original component-tagged attached B-coset points
whose intrinsic B-component meets the original OLD
A-component of the selected root. These are the whole
attached coset constituents, including fresh points,
not just actual old skeleton vertices. -/
def rootedAttachedRawSet
    (L : CayleySubgraphSpec genΓ A)
    (P : CosetFamilySpec A)
    (root : L.Vertex) :
    Set (L.MultiCosetRawVertex P) :=
  { raw | ∃ x : L.Vertex,
      raw.2.1 = L.componentClass raw.1.1 x ∧
      L.SubalphabetReachable A root x }

/-- The actual selected original A-component's
FULL glued multiCE vertex region. A point is
selected iff it has some component-tagged raw
B-coset representative anchored in the root's
true old A-component. This definition does NOT
assert that every quotient representation is selected. -/
def rootedMultiCosetImage
    (L : CayleySubgraphSpec genΓ A)
    (P : CosetFamilySpec A)
    (hAdm : L.AdmissibleForCosetExtension)
    (hGen : IsGenerated genΓ) (hRet : Retractable genΓ)
    (root : L.Vertex) :
    Set (L.MultiCosetVertex P hAdm hGen hRet) :=
  Set.image
    (fun raw : L.MultiCosetRawVertex P =>
      L.multiCosetInclude P hAdm hGen hRet
        raw.1.1 raw.1.2 raw.2)
    (L.rootedAttachedRawSet P root)

/-- CORRECTED rank-k Theorem 4.7(ii) geometric base, in
its honest ROOTED COMPONENT scope: the full group
coordinate map of the ACTUAL glued multiCE is
injective on the selected old A-component's entire
multi-alphabet attached coset region.

Only one root-compatible labelled G-Cayley cover of
the true LEGALLY completed H multiCE stage is used.
H ambient multiCE injectivity is NOT required, and
the full original G-pullback need NOT be connected.

The hard remaining source work is to build and
align the concrete selected stage, correct A-local
group presentations and all old A-component covers,
then prove separate B-bridge freeness. -/
theorem pullbackQuotient_rootedMultiCosetAmbient_injOn
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hStable : ∀ B : Finset ι, B ∈ P.alphabets → Q.StableAt B)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (root : (K.pullbackQuotient Q).Vertex)
    (hOne :
      F.onVertex (1 : Γ) =
        (K.pullbackOldToWeakMultiCosetStageHom
          Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex root) :
    Set.InjOn
      ((K.pullbackQuotient Q).multiCosetAmbientValue
        P hAdmG hGenG hRetG)
      ((K.pullbackQuotient Q).rootedMultiCosetImage
        P hAdmG hGenG hRetG root) := by
  let L := K.pullbackQuotient Q
  intro u hu v hv huv
  change u ∈ Set.image
    (fun raw : L.MultiCosetRawVertex P =>
      L.multiCosetInclude P hAdmG hGenG hRetG
        raw.1.1 raw.1.2 raw.2)
    (L.rootedAttachedRawSet P root) at hu
  change v ∈ Set.image
    (fun raw : L.MultiCosetRawVertex P =>
      L.multiCosetInclude P hAdmG hGenG hRetG
        raw.1.1 raw.1.2 raw.2)
    (L.rootedAttachedRawSet P root) at hv
  obtain ⟨rawU, hrawU, rfl⟩ := hu
  obtain ⟨rawV, hrawV, rfl⟩ := hv
  rcases rawU with ⟨⟨B, hBP⟩, p⟩
  rcases rawV with ⟨⟨C, hCP⟩, q⟩
  change ∃ x : L.Vertex,
    p.1 = L.componentClass B x ∧ L.SubalphabetReachable A root x at hrawU
  change ∃ y : L.Vertex,
    q.1 = L.componentClass C y ∧ L.SubalphabetReachable A root y at hrawV
  obtain ⟨x, hidxB, hreachX⟩ := hrawU
  obtain ⟨y, hidxC, hreachY⟩ := hrawV
  have hValue : L.attachedValue B p = L.attachedValue C q := by
    simpa only [L.multiCosetAmbientValue_include] using huv
  exact K.rootedOldStageCover_mixedSupportMultiCE_equal
    Q P hAdmH hGenH hRetH
    hAdmG hGenG hRetG
    hweak B₀ hB₀ F root hOne
    B C hBP hCP (hStable B hBP) (hStable C hCP)
    p q x y hidxB hidxC hreachX hreachY hValue

end CayleySubgraphSpec
end ABO
end PSTSEPPA
