import PSTSEPPA.ABO.PullbackMultiCosetTaggedVertexNaturality
import PSTSEPPA.ABO.PullbackAttachedCosetSupportReflection
import PSTSEPPA.ABO.KStableTranslatedCosetEquiv
import PSTSEPPA.ABO.MultiCosetVertexQuotient

/-!
# Reflect genuine FULL B-constituent membership across a stable G→H old pullback

The corrected ABO first-rank 4.7(iii) external bridge argument
must split the image of an ORIGINAL G off-B multi-coset vertex
in the H-level plain multiCE into cases:
(1) its H image belongs to a genuine completed H B-constituent;
(2) its H image is ALSO off-B, so a genuine source type-(2)
    isolated full B-coset augmentation may be attached at it.

We show that (1) is IMPOSSIBLE when the G→H quotient is stable
on every selected proper alphabet of the multiCE.

This theorem is NOT a claim that the H ambient coordinate
map is injective. It uses TRUE intrinsic old component indices
and the exact intersection-supported B/C quotient gluing.

First, for ANY H component-tagged full B-coset point pH with
ambient value Q(g), construct an ACTUAL G full B-coset point pG
at EXACTLY g with component-tagged image pH.
Choose a genuine old H B-component witness yH; the labelled
quotient lifts yH inside the TRANSLATED G[B]-coset of g.
The lifted yG is automatically a TRUE ORIGINAL old G vertex
because the old skeleton is the literal Q-pullback.

Second, suppose an actual G C-point has H quotient image in
the H B-constituent. Lift the H B-point over its SAME G group
coordinate as just proved. The H B/C gluing supplies a TRUE
common (B∩C)-support, and the independently certified
stable pullback mixed-support reflection supplies the genuine
G (B∩C) common OLD support. Therefore the original G C-point
was ALREADY inside the G B-constituent at that coordinate.

Consequently the preimage of the H full B-constituent
SUBSET under the TRUE tagged G multiCE→H vertex morphism
is EXACTLY the G full B-constituent subset. In particular,
every G off-B point maps to an H off-B point. This is
stronger than simple pointwise group coordinate projection,
and is useful precisely because ambient H injectivity may
fail even in admissible retractable examples.

Assumptions: true original incomplete signed K, actual Q
old signed pullback, existing G/H multiCE admissibility,
generation/retractability and Q.StableAt for chosen B,C.
NO global A-stability, no full G-pullback connectedness
and no source type-(2) action compatibility are assumed.
The latter still needs to prove the genuine B-orbit
isolation using correctly based augmentations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- For ANY H full B-coset point q whose actual group value
is Q(g), choose a TRUE original G B-component preimage at
the EXACT requested G coordinate g.

The original incomplete G skeleton is the full inverse-image
of the old H vertices/edges, so the translated B-coset
preimage of a genuine old H witness is automatically an
old G vertex, not an invented or completed edge.

No B-stability assumption is needed for this existence
statement; labelled generator preservation suffices. -/
theorem pullbackQuotient_attachedCosetToBase_lift_at_value
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (q : K.AttachedCosetVertex B)
    (g : Γ)
    (hg : Q.hom g = K.attachedValue B q) :
    ∃ p : (K.pullbackQuotient Q).AttachedCosetVertex B,
      (K.pullbackQuotient Q).attachedValue B p = g ∧
      K.pullbackQuotient_attachedCosetToBase Q B p = q := by
  let L := K.pullbackQuotient Q
  obtain ⟨y, hy⟩ := K.componentClass_surjective B q.1
  have hqB : Q.hom g ∈ generatedLeftCoset genΔ B y.1 := by
    have hq : q.2.1 ∈ K.componentAmbientCoset
        B (K.componentClass B y) := by
      simpa only [hy] using q.2.2
    change q.2.1 ∈ generatedLeftCoset genΔ B y.1 at hq
    rw [hg]
    change q.2.1 ∈ generatedLeftCoset genΔ B y.1
    exact hq
  have hyBack : y.1 ∈ generatedLeftCoset genΔ B (Q.hom g) := by
    have hSame := generatedLeftCoset_eq_of_mem genΔ B hqB
    rw [← hSame]
    exact self_mem_generatedLeftCoset genΔ B y.1
  obtain ⟨r, hrB, hrY⟩ :=
    Q.exists_generatedLeftCoset_preimage B g y.1 hyBack
  have hgB : g ∈ generatedLeftCoset genΓ B r := by
    have hSame := generatedLeftCoset_eq_of_mem genΓ B hrB
    rw [← hSame]
    exact self_mem_generatedLeftCoset genΓ B g
  let x : L.Vertex := ⟨r, by
    change Q.hom r ∈ K.vertices
    rw [hrY]
    exact y.2⟩
  let p : L.AttachedCosetVertex B :=
    ⟨L.componentClass B x, ⟨g, hgB⟩⟩
  refine ⟨p, rfl, ?_⟩
  apply K.attachedValue_injective_of_same_index B
  · change K.componentClass B ((K.pullbackQuotientHom Q).onVertex x) =
      q.1
    have hxy : (K.pullbackQuotientHom Q).onVertex x = y :=
      Subtype.ext hrY
    rw [hxy]
    exact hy
  · change Q.hom g = q.2.1
    exact hg

/-- A G multiCE quotient point can have its genuine
intrinsically component-tagged H image inside a full
H B-constituent ONLY if that ORIGINAL G point itself
already belongs to some genuine tagged full G B-constituent.

This is proved for the entire potentially DISCONNECTED
original G pullback without an ambient G-embedding
hypothesis, as a consequence of B/C stability and the
actual common-support reflection mechanism. -/
theorem pullbackQuotient_multiCosetToBase_reflect_full_B
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hStable : ∀ C : Finset ι, C ∈ P.alphabets → Q.StableAt C)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (z : (K.pullbackQuotient Q).MultiCosetVertex
      P hAdmG hGenG hRetG)
    (q : K.AttachedCosetVertex B)
    (hImage :
      K.pullbackQuotient_multiCosetVertexToBase Q P
        hAdmG hGenG hRetG hAdmH hGenH hRetH z =
      K.multiCosetInclude P hAdmH hGenH hRetH B hBP q) :
    ∃ p : (K.pullbackQuotient Q).AttachedCosetVertex B,
      z = (K.pullbackQuotient Q).multiCosetInclude
        P hAdmG hGenG hRetG B hBP p := by
  let L := K.pullbackQuotient Q
  induction z using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨⟨C, hCP⟩, p⟩
      change K.multiCosetInclude P hAdmH hGenH hRetH C hCP
          (K.pullbackQuotient_attachedCosetToBase Q C p) =
        K.multiCosetInclude P hAdmH hGenH hRetH B hBP q at hImage
      have hQval : Q.hom p.2.1 = K.attachedValue B q := by
        have hv := congrArg
          (K.multiCosetAmbientValue P hAdmH hGenH hRetH) hImage
        change Q.hom p.2.1 = K.attachedValue B q at hv
        exact hv
      obtain ⟨pB, hpBval, hpBimage⟩ :=
        K.pullbackQuotient_attachedCosetToBase_lift_at_value
          Q B q p.2.1 hQval
      have hShareH_CB :
          K.ShareIntersectionSupport C B
            (K.pullbackQuotient_attachedCosetToBase Q C p) q := by
        have h := Quotient.exact hImage
        change K.MultiCosetRawRelated P
          (⟨⟨C, hCP⟩,
            K.pullbackQuotient_attachedCosetToBase Q C p⟩ :
              K.MultiCosetRawVertex P)
          (⟨⟨B, hBP⟩, q⟩ : K.MultiCosetRawVertex P) at h
        exact h
      have hShareH :
          K.ShareIntersectionSupport B C
            (K.pullbackQuotient_attachedCosetToBase Q B pB)
            (K.pullbackQuotient_attachedCosetToBase Q C p) := by
        rw [hpBimage]
        exact K.shareIntersectionSupport_symm C B hShareH_CB
      have hpBC : L.attachedValue B pB = L.attachedValue C p := by
        change L.attachedValue B pB = p.2.1
        exact hpBval
      have hShareG :
          L.ShareIntersectionSupport B C pB p :=
        K.pullbackQuotient_shareIntersectionSupport_reflect_of_equal_value
          Q B C (hStable B hBP) (hStable C hCP)
          pB p hpBC hShareH
      refine ⟨pB, ?_⟩
      apply Quotient.sound
      change L.ShareIntersectionSupport C B p pB
      exact L.shareIntersectionSupport_symm B C hShareG

/-- EXACT preimage of a tagged full B-constituent region:
G B-full iff its genuine multiCE H image is H B-full.
This does NOT equate the underlying ambient coordinates of
different H B-component tags. -/
theorem pullbackQuotient_multiCosetToBase_full_B_iff
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hStable : ∀ C : Finset ι, C ∈ P.alphabets → Q.StableAt C)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (z : (K.pullbackQuotient Q).MultiCosetVertex
      P hAdmG hGenG hRetG) :
    (∃ p : (K.pullbackQuotient Q).AttachedCosetVertex B,
      (K.pullbackQuotient Q).multiCosetInclude
        P hAdmG hGenG hRetG B hBP p = z) ↔
    (∃ q : K.AttachedCosetVertex B,
      K.multiCosetInclude P hAdmH hGenH hRetH B hBP q =
      K.pullbackQuotient_multiCosetVertexToBase Q P
        hAdmG hGenG hRetG hAdmH hGenH hRetH z) := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨K.pullbackQuotient_attachedCosetToBase Q B p, ?_⟩
    rw [← hp]
    rfl
  · rintro ⟨q, hq⟩
    obtain ⟨p, hp⟩ :=
      K.pullbackQuotient_multiCosetToBase_reflect_full_B
        Q P hAdmG hGenG hRetG hAdmH hGenH hRetH
        hStable B hBP z q hq.symm
    exact ⟨p, hp.symm⟩

/-- The TRUE complement of the full B-constituent also
transports exactly under the labelled stable quotient:
G off-B iff its ORIGINAL tagged H image is H off-B.

This crucially eliminates the formerly open possibility
that a G off-B point could project into an H full B-copy.
The distinct R8 full-B-coset repair of corrected 4.7(iii)
does not become trivial from this lemma: it governs
different higher-rank cluster/augmentation alternatives. -/
theorem pullbackQuotient_multiCosetToBase_off_B_iff
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hStable : ∀ C : Finset ι, C ∈ P.alphabets → Q.StableAt C)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (z : (K.pullbackQuotient Q).MultiCosetVertex
      P hAdmG hGenG hRetG) :
    (¬ ∃ p : (K.pullbackQuotient Q).AttachedCosetVertex B,
      (K.pullbackQuotient Q).multiCosetInclude
        P hAdmG hGenG hRetG B hBP p = z) ↔
    (¬ ∃ q : K.AttachedCosetVertex B,
      K.multiCosetInclude P hAdmH hGenH hRetH B hBP q =
      K.pullbackQuotient_multiCosetVertexToBase Q P
        hAdmG hGenG hRetG hAdmH hGenH hRetH z) := by
  exact not_congr (K.pullbackQuotient_multiCosetToBase_full_B_iff
    Q P hAdmG hGenG hRetG hAdmH hGenH hRetH hStable B hBP z)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
