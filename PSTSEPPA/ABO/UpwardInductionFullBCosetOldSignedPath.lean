import PSTSEPPA.ABO.KStablePullbackIntrinsicBComponents
import PSTSEPPA.ABO.KStablePullbackAdmissibility
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# ABO Theorem 4.7(iii), correction R8: skeleton-meeting FULL B-coset paths

The published upward proof MUST split the case where a signed
H-level B-component meets the original old H-skeleton. In that
case it is a FULL B-coset, NOT a multi-constituent proper cluster.

Its essential first lifting step is as follows. Suppose old
vertices x,y of the actual signed G→H pullback skeleton have
(i) coordinates in the SAME genuine G[B] left coset, and
(ii) a REAL old H-skeleton B-labelled path between their H-images.
If G→H is k-stable and |B|≤k, the H-old B-path lifts exactly to
a TRUE old G B-path from x to y (rather than merely a path
to some other lift of the same H vertex). Mapping that old
path through the actual old/fresh coset-extension skeleton
homomorphism produces a REAL original signed B-path
between their images inside the G multiCE. Both positive
and inverse directed edges and genuine source tags survive.

This is the source R8 FULL-coset BRIDGE-LIFT step at OLD
skeleton endpoints. It does NOT on its own prove the whole
Theorem 4.7(iii): one must still show the endpoints of a
bridge configuration can be reduced to the SAME old G[B]
coset and prove the alternative off-skeleton multi-piece and
single-piece proper cluster cases using the H B-augmented
source G-Cayley cover. No fake missing old signed edge,
unjustified H-coordinate injectivity, extra axiom or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- Source corrected Theorem 4.7(iii), original-skeleton FULL
B-coset path lift: an actual H old signed B-path between two
pullback G old vertices, together with a genuine SAME G[B]
coset condition and k-stability, yields an ACTUAL original
signed B-path in the completed G multiCE between their
two old-skeleton inclusion vertices.

The G input here is allowed to be the TRUE generated local
G[A] group; no global E-wide G retractability is required.
The explicit original coset-extension hypotheses are
satisfied locally by the accepted R1 package. -/
theorem upwardFullBCoset_oldSkeleton_signedPathLift
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (k : ℕ) (hk : Q.KStable k)
    (hA : A.card ≤ k + 1)
    (B : Finset ι) (hBA : B ⊂ A)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ)
    (hRetG : Retractable genΓ)
    (hBP : B ∈ P.alphabets)
    (x y : (K.pullbackQuotient Q).Vertex)
    (hyCoset : y.1 ∈ generatedLeftCoset genΓ B x.1)
    (hRealH : K.SubalphabetReachable B
      ((K.pullbackQuotientHom Q).onVertex x)
      ((K.pullbackQuotientHom Q).onVertex y)) :
    ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      ((K.pullbackQuotient Q).multiCosetEGraph P
        (K.pullbackQuotient_admissible_of_kStable
          Q k hk hA hAdmH)
        hGenG hRetG).Follows
          (((K.pullbackQuotient Q).skeletonToMultiCosetHom P
            (K.pullbackQuotient_admissible_of_kStable
              Q k hk hA hAdmH) hGenG hRetG B hBP).onVertex x)
          w
          (((K.pullbackQuotient Q).skeletonToMultiCosetHom P
            (K.pullbackQuotient_admissible_of_kStable
              Q k hk hA hAdmH) hGenG hRetG B hBP).onVertex y) := by
  let L := K.pullbackQuotient Q
  let hAdmG := K.pullbackQuotient_admissible_of_kStable
    Q k hk hA hAdmH
  have hB : B.card ≤ k := by
    have hlt : B.card < A.card := Finset.card_lt_card hBA
    omega
  have hOld : L.SubalphabetReachable B x y :=
    (K.pullbackQuotient_subalphabetReachable_iff_of_kStable
      Q k hk B hB x y hyCoset).mpr hRealH
  obtain ⟨w, hw, hPath⟩ := hOld
  let f := L.skeletonToMultiCosetHom
    P hAdmG hGenG hRetG B hBP
  exact ⟨w, hw, hPath.map f⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
