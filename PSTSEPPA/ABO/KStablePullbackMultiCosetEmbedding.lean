import PSTSEPPA.ABO.PullbackAttachedCosetSupportReflection
import PSTSEPPA.ABO.MultiCosetVertexQuotient
import PSTSEPPA.ABO.KStablePullbackAdmissibility

/-!
# Corrected ABO Theorem 4.7(ii): preserve embeddedness of the FULL multi-CE

Let Q:G↠H be a genuine generator-preserving labelled group
quotient and K an ACTUAL incomplete H-Cayley A-skeleton.
Let L=Q⁻¹(K) be its exact ORIGINAL signed-edge pullback,
not a fictitious completed X₁ skeleton.

Assume each labelled group is retractable/generated,
and the real multi-coset extensions CE(H,K;P) and
CE(G,L;P) are formed with the correct admissibility
and true component-tagged intersection-support Setoids.
Assume the H-level full multi-CE is EMBEDDED in Cayley(H):
its canonical ambient H coordinate map is injective.
Assume Q stable on each selected support B∈P.

Then the entire G-level full multi-CE ambient coordinate
map is INJECTIVE. This is not simply an assumption of
injective ambient coordinates! It follows by identifying
two arbitrary G quotient points with equal G values:
their H images have equal values; the H embeddedness
gives actual common (B∩C)-tagged support downstairs;
the separately proven mixed-support reflection lemma
produces the genuine original OLD common G
(B∩C)-support upstairs (because G values are equal);
therefore the TWO G tagged raw points are already
equivalent by the actual ABO (3.10) gluing Setoid.

The proof holds for any selected proper alphabet family
P, including B=C, B=∅, signed loops, nonfaithful and
repeated labels. The ambient full group retractability
hypotheses are explicit, and are NOT smuggled into
the weaker k-retractability of a source global group.
The source uses LOCAL generated groups G[A], H[A]
which ARE retractable by their bounded-rank hypotheses;
that localization is a further application gate.

Theorem 4.7(iii) bridge freeness, full-B-coset R8
augmentation, Condition 5.2, higher k induction,
and unconditional PSTS EPPA remain OPEN.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- Embedding of the ACTUAL full component-tagged G
multi-coset extension into Cayley(G) is inherited
from the embedded ACTUAL H multi-coset extension,
provided the quotient is stable on every selected
constituent alphabet. The proof checks arbitrary
mixed-support B/C tags via true (B∩C) gluing.
No global injectivity of the group quotient is
assumed. -/
theorem pullbackQuotient_multiCosetAmbient_injective_of_stable
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hStable : ∀ B : Finset ι, B ∈ P.alphabets → Q.StableAt B)
    (hEmbeddedH :
      Function.Injective
        (K.multiCosetAmbientValue P hAdmH hGenH hRetH)) :
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
          let pH := K.pullbackQuotient_attachedCosetToBase Q B p
          let qH := K.pullbackQuotient_attachedCosetToBase Q C q
          have hAmbientH :
              K.multiCosetAmbientValue P hAdmH hGenH hRetH
                (K.multiCosetInclude P hAdmH hGenH hRetH B hBP pH) =
              K.multiCosetAmbientValue P hAdmH hGenH hRetH
                (K.multiCosetInclude P hAdmH hGenH hRetH C hCP qH) := by
            rw [K.multiCosetAmbientValue_include,
              K.multiCosetAmbientValue_include,
              K.pullbackQuotient_attachedCosetToBase_value,
              K.pullbackQuotient_attachedCosetToBase_value]
            exact congrArg Q.hom hValue
          have hEqH :
              K.multiCosetInclude P hAdmH hGenH hRetH B hBP pH =
              K.multiCosetInclude P hAdmH hGenH hRetH C hCP qH :=
            hEmbeddedH hAmbientH
          have hShareH : K.ShareIntersectionSupport B C pH qH := by
            have hExact := Quotient.exact hEqH
            change K.ShareIntersectionSupport B C pH qH at hExact
            exact hExact
          have hShareG :
              L.ShareIntersectionSupport B C p q :=
            K.pullbackQuotient_shareIntersectionSupport_reflect_of_equal_value
              Q B C (hStable B hBP) (hStable C hCP)
              p q hValue hShareH
          apply Quotient.sound
          exact hShareG

/-- Source-rank form: k-stability plus |A|≤k+1
automatically gives stability on every selected
proper B⊊A. The actual G-pullback is admissible
by the separately certified corrected Theorem
4.7(i) transfer, so this is the (i)+(ii) interface
under explicit local generated/retractable group
hypotheses and the H multiCE embeddedness premise. -/
theorem pullbackQuotient_multiCosetAmbient_injective_of_kStable
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (k : ℕ) (hk : Q.KStable k)
    (hCard : A.card ≤ k + 1)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hEmbeddedH :
      Function.Injective
        (K.multiCosetAmbientValue P hAdmH hGenH hRetH)) :
    Function.Injective
      ((K.pullbackQuotient Q).multiCosetAmbientValue P
        (K.pullbackQuotient_admissible_of_kStable
          Q k hk hCard hAdmH) hGenG hRetG) := by
  apply K.pullbackQuotient_multiCosetAmbient_injective_of_stable
    Q P hAdmH hGenH hRetH
    (K.pullbackQuotient_admissible_of_kStable
      Q k hk hCard hAdmH)
    hGenG hRetG
  · intro B hBP
    have hlt : B.card < k + 1 :=
      lt_of_lt_of_le (Finset.card_lt_card (P.proper B hBP)) hCard
    exact hk B (Nat.lt_succ_iff.mp hlt)
  · exact hEmbeddedH

end CayleySubgraphSpec
end ABO
end PSTSEPPA
