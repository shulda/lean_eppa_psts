import PSTSEPPA.ABO.PullbackAttachedCosetSupportTransport
import PSTSEPPA.ABO.MultiCosetVertexQuotient
import PSTSEPPA.ABO.MultiCosetMorphisms
import PSTSEPPA.ABO.KStablePullbackAdmissibility

/-!
# The TRUE tagged full multiCE vertex map from a G-old pullback to H

The source-corrected ABO Theorem 4.7(iii) requires an ACTUAL
signed OLD graph map from a chosen rooted original G[A]
multi-coset component into the underlying (unaugmented)
H[A] multi-coset EGraph, before invoking the type-(2)
augmentation detector and based Cayley-root compatibility.

At the vertex level there is an exact natural map from the
entire G multi-coset quotient to the entire H multi-coset
quotient, even if the original G/H group quotient is NOT
injective on the full group or on the parent A-subgroup.
This map must retain ALL intrinsically indexed original
old B-components, rather than forget tags and map just
the ambient group values.

We construct it directly from the already certified
component-indexed G→H full B-coset maps and the FORWARD
part of the exact common-(B∩C)-support gluing relation.
This proves well-definedness on the TRUE vertex quotient,
without pretending that the H ambient coordinate map is
injective.

The map:
* sends each real tagged old/fresh attached G B-point
  to its exact tagged H B-point;
* takes its ambient group coordinate via the actual Q;
* carries the original G-old skeleton inclusion to the
  actual H-old skeleton inclusion with identical B-tag
  and the TRUE signed old quotient-cover vertex map.

Constructing its accompanying map on the exact oriented
source+FULL-SIGNED-LABEL EDGE quotient and proving
preservation of formal reversal/targets is a separate
required next step before this can serve as the full
old graph hom in type-(2) augmented root compatibility.
We neither postulate that edge map nor falsely use this
vertex map as a signed graph morphism.

No whole-pullback connectedness, H ambient injectivity,
A-stability, corrected 4.7(iii), R8, higher rank,
Condition 5.2 or PSTS EPPA is concluded here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- The genuine map of complete TAGGED multi-coset vertex
quotients from one original G old-edge pullback to H, for
ANY family of selected proper subalphabets P⊂P(A).

Every component index is mapped by actual old B-path
transport, and B/C gluing is respected because a common
genuine G old (B∩C)-support projects to an actual H
old common support. No reverse gluing reflection is
asserted for arbitrary different G ambient coordinates. -/
noncomputable def pullbackQuotient_multiCosetVertexToBase
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (z : (K.pullbackQuotient Q).MultiCosetVertex P hAdmG hGenG hRetG) :
    K.MultiCosetVertex P hAdmH hGenH hRetH :=
  Quotient.liftOn z
    (fun raw =>
      K.multiCosetInclude P hAdmH hGenH hRetH
        raw.1.1 raw.1.2
        (K.pullbackQuotient_attachedCosetToBase Q raw.1.1 raw.2))
    (by
      intro p q hpq
      change (K.pullbackQuotient Q).ShareIntersectionSupport
        p.1.1 q.1.1 p.2 q.2 at hpq
      apply Quotient.sound
      change K.ShareIntersectionSupport p.1.1 q.1.1
        (K.pullbackQuotient_attachedCosetToBase Q p.1.1 p.2)
        (K.pullbackQuotient_attachedCosetToBase Q q.1.1 q.2)
      exact K.pullbackQuotient_shareIntersectionSupport_forward
        Q p.1.1 q.1.1 p.2 q.2 hpq)

/-- The exact pointwise formula on ANY genuinely selected
component-tagged G B-constituent (old or fresh). This
never forgets the component tag even when two distinct
G B-cosets have the same image H ambient coordinate. -/
@[simp] theorem pullbackQuotient_multiCosetVertexToBase_include
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B) :
    K.pullbackQuotient_multiCosetVertexToBase Q P
        hAdmG hGenG hRetG hAdmH hGenH hRetH
        ((K.pullbackQuotient Q).multiCosetInclude
          P hAdmG hGenG hRetG B hBP p) =
      K.multiCosetInclude P hAdmH hGenH hRetH
        B hBP (K.pullbackQuotient_attachedCosetToBase Q B p) :=
  rfl

/-- The ambient coordinate of the TRUE component-tagged H
quotient image is exactly Q of the original G coordinate.
This is a naturality equation, NOT H ambient injectivity. -/
theorem pullbackQuotient_multiCosetVertexToBase_ambient_value
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (z : (K.pullbackQuotient Q).MultiCosetVertex P hAdmG hGenG hRetG) :
    K.multiCosetAmbientValue P hAdmH hGenH hRetH
      (K.pullbackQuotient_multiCosetVertexToBase Q P
        hAdmG hGenG hRetG hAdmH hGenH hRetH z) =
      Q.hom
        ((K.pullbackQuotient Q).multiCosetAmbientValue
          P hAdmG hGenG hRetG z) := by
  induction z using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨⟨B, hBP⟩, p⟩
      rfl

/-- On each actual old incomplete G skeleton vertex, the
tagged multiCE map commutes EXACTLY with the true
original signed old-vertex G→H quotient cover, not just
with its underlying ambient group projection. -/
theorem pullbackQuotient_multiCosetVertexToBase_old_skeleton
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (x : (K.pullbackQuotient Q).Vertex) :
    K.pullbackQuotient_multiCosetVertexToBase Q P
      hAdmG hGenG hRetG hAdmH hGenH hRetH
      (((K.pullbackQuotient Q).skeletonToMultiCosetHom
        P hAdmG hGenG hRetG B hBP).onVertex x) =
    (K.skeletonToMultiCosetHom
      P hAdmH hGenH hRetH B hBP).onVertex
      ((K.pullbackQuotientHom Q).onVertex x) := by
  change K.multiCosetInclude P hAdmH hGenH hRetH B hBP
      (K.pullbackQuotient_attachedCosetToBase Q B
        ((K.pullbackQuotient Q).attachedOfSkeletonVertex B x)) =
    K.multiCosetInclude P hAdmH hGenH hRetH B hBP
      (K.attachedOfSkeletonVertex B
        ((K.pullbackQuotientHom Q).onVertex x))
  rw [K.pullbackQuotient_attachedCosetToBase_skeleton]

end CayleySubgraphSpec
end ABO
end PSTSEPPA
