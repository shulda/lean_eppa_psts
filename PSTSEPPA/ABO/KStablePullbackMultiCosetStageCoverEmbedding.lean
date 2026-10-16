import PSTSEPPA.ABO.KStablePullbackMultiCosetEmbedding
import PSTSEPPA.ABO.CayleyStageProjection

/-!
# Corrected Theorem 4.7(ii): exact full G-CE embedding from the H-stage COVER

The source's corrected Theorem 4.7(ii) does NOT suppose the
H-level full coset extension is already ambient embedded.
That statement can be false even for admissible skeletons
over retractable groups: separate intrinsic component tags
can share one ambient H-coordinate.

The correct source mechanism uses one actual based labelled
Cayley(G) morphism into the LEGALLY completed H-level
coset-extension stage, preserving the original old signed
component geometry.

We isolate the EXACT necessary compatibility:

  F : Cayley(G) → completed(CE(H,K;P))

is a genuine signed labelled morphism with the ACTUAL
component-tagged quotient vertex type of CE(H,K;P).
For each genuine tagged G B-coset point p, evaluated at its
G group coordinate, F agrees with the EXACT H tagged
image of p under the original G→H quotient.

This is stronger than ordinary surjectivity of F, and
its proof from the source's selected-stage construction
is an explicit remaining induction gate. But ONCE it
holds, equal group coordinates of two arbitrary G-CE
points force equality of their corresponding tagged
H-CE stage points BY EVALUATING THE SAME F AT THE SAME
G VERTEX, with no H-ambient injectivity assumption.

Then the already independently checked mixed B/C tagged
support REFLECTION theorem (#608), which itself uses
the common old support lift (#607), implies the original
G points were already glued over their TRUE (B∩C)
component-index support. Therefore the entire full
G-CE ambient value map is injective.

We also expose a rank-k version, with admissibility
transferred using corrected Theorem 4.7(i) (#603).
All source rank-local generatedness and global
retractability premises are explicit; the global
source groups are only bounded-rank retractable.

These are CONDITIONAL mathematical statements. In
particular we do NOT construct the required selected
source-compatible F, nor claim that every arbitrary
Cayley(G) stage cover automatically satisfies the
crucial pointwise tagged-image compatibility.
Condition 5.2, the separate augmented B-coset
bridge-freeness proof (R8), higher ranks and the
final PSTS EPPA theorem remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ Edge : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- A single ACTUAL labelled G-Cayley cover of the genuine
H-level completed multiCE stage, with the EXACT old
component-tagged vertex values on every G-attached
B-constituent, suffices for FULL embeddedness of the
G-level multiCE.

H-ambient embeddedness is NOT a hypothesis: unlike the
stronger-but-inapplicable previous conditional #609,
this theorem uses only equality of the images of two
G points under one concrete source-compatible stage F.
The hard remaining source step is PROVING this
compatibility from actual canonical old-cover bases. -/
theorem pullbackQuotient_multiCosetAmbient_injective_of_stageCover
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hStable : ∀ B : Finset ι, B ∈ P.alphabets → Q.StableAt B)
    (T : CompleteEGraph
      (K.MultiCosetVertex P hAdmH hGenH hRetH) Edge ι)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (hRepresent :
      ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
        (p : (K.pullbackQuotient Q).AttachedCosetVertex B),
        F.onVertex ((K.pullbackQuotient Q).attachedValue B p) =
          K.multiCosetInclude P hAdmH hGenH hRetH B hBP
            (K.pullbackQuotient_attachedCosetToBase Q B p)) :
    Function.Injective
      ((K.pullbackQuotient Q).multiCosetAmbientValue
        P hAdmG hGenG hRetG) := by
  let L := K.pullbackQuotient Q
  intro u v huv
  induction u using Quotient.inductionOn with
  | h rawU =>
      induction v using Quotient.inductionOn with
      | h rawV =>
          rcases rawU with ⟨⟨B, hBP⟩, p⟩
          rcases rawV with ⟨⟨C, hCP⟩, q⟩
          have hValue : L.attachedValue B p = L.attachedValue C q := huv
          have hEqualH :
              K.multiCosetInclude P hAdmH hGenH hRetH B hBP
                (K.pullbackQuotient_attachedCosetToBase Q B p) =
              K.multiCosetInclude P hAdmH hGenH hRetH C hCP
                (K.pullbackQuotient_attachedCosetToBase Q C q) := by
            calc
              K.multiCosetInclude P hAdmH hGenH hRetH B hBP
                  (K.pullbackQuotient_attachedCosetToBase Q B p) =
                F.onVertex (L.attachedValue B p) :=
                (hRepresent B hBP p).symm
              _ = F.onVertex (L.attachedValue C q) :=
                congrArg F.onVertex hValue
              _ = K.multiCosetInclude P hAdmH hGenH hRetH C hCP
                  (K.pullbackQuotient_attachedCosetToBase Q C q) :=
                hRepresent C hCP q
          have hShareH :
              K.ShareIntersectionSupport B C
                (K.pullbackQuotient_attachedCosetToBase Q B p)
                (K.pullbackQuotient_attachedCosetToBase Q C q) := by
            have hExact := Quotient.exact hEqualH
            change K.ShareIntersectionSupport B C
              (K.pullbackQuotient_attachedCosetToBase Q B p)
              (K.pullbackQuotient_attachedCosetToBase Q C q) at hExact
            exact hExact
          have hShareG :
              L.ShareIntersectionSupport B C p q :=
            K.pullbackQuotient_shareIntersectionSupport_reflect_of_equal_value
              Q B C (hStable B hBP) (hStable C hCP)
              p q hValue hShareH
          apply Quotient.sound
          exact hShareG

/-- Rank-k source-interface version: k-stability
controls all strictly proper selected B⊊A whenever
|A|≤k+1; the genuine G old pullback is admissible
by the previously certified cross-group lift theorem.
Only local generated/retractable group data and the
actual stage F's component-tagged representation
identity remain explicit. -/
theorem pullbackQuotient_multiCosetAmbient_injective_of_kStable_stageCover
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (k : ℕ) (hk : Q.KStable k)
    (hCard : A.card ≤ k + 1)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (T : CompleteEGraph
      (K.MultiCosetVertex P hAdmH hGenH hRetH) Edge ι)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (hRepresent :
      ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
        (p : (K.pullbackQuotient Q).AttachedCosetVertex B),
        F.onVertex ((K.pullbackQuotient Q).attachedValue B p) =
          K.multiCosetInclude P hAdmH hGenH hRetH B hBP
            (K.pullbackQuotient_attachedCosetToBase Q B p)) :
    Function.Injective
      ((K.pullbackQuotient Q).multiCosetAmbientValue P
        (K.pullbackQuotient_admissible_of_kStable
          Q k hk hCard hAdmH) hGenG hRetG) := by
  apply K.pullbackQuotient_multiCosetAmbient_injective_of_stageCover
    Q P hAdmH hGenH hRetH
    (K.pullbackQuotient_admissible_of_kStable
      Q k hk hCard hAdmH)
    hGenG hRetG
    (fun B hBP => hk B
      (Nat.lt_succ_iff.mp
        (lt_of_lt_of_le (Finset.card_lt_card (P.proper B hBP)) hCard)))
    T F hRepresent

end CayleySubgraphSpec
end ABO
end PSTSEPPA
