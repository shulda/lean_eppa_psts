import PSTSEPPA.ABO.NestedComponentBridgeFreeHeredity
import PSTSEPPA.ABO.ExactSignedSmallRankClusterBase

/-!
# ABO Theorem 4.5: FULL forward induction over the parent alphabet

We now combine three fully explicit source steps:
* the exact signed Definition-3.22 cluster-property base for
  cardinality at most 2 (including empty and one-letter cases);
* Lemma 4.3, deriving the full signed cluster property of a
  parent skeleton from bridge-free AND cluster lower rooted stages;
* genuine original signed component FLATTENING, which proves
  that the source lower rooted bridge-free assumption is
  HEREDITARY when descending into any selected proper component.

Hence strong induction on the number of source labels |A|
is mathematically legitimate WITHOUT the extra assumption
that each iterated nested lower component is separately
bridge-free. The needed lower cluster properties are supplied
by the induction hypothesis, the needed lower bridge-free
properties by the inherited ORIGINAL source hypothesis.

The result is an unconditional-forward-in-cluster-property
THEOREM GIVEN precisely the printed lower bridge-free premises,
not a conditional Lemma-4.3 restatement with extra lower
cluster hypotheses. Every off-skeleton full B-coset and proper
B-cluster has an ATTAINED minimum ORIGINAL old-component
support; real oriented signed edges and original component tags
are preserved.

This first theorem uses a FINITE GLOBALLY generated/retractable
labelled Γ as the chosen actual ambient group. The paper also
uses just retractability of H[A]; source-ready Γ[A] localization
and group transport are already separate certified APIs.
The k-local ambient formulation and upward Theorem 4.7
remain separate steps. No new axioms, sorry, imaginary
old source edges or ambient-coordinate tag collapse.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Source Theorem 4.5, globally generated/retractable instance:
the exact signed whole-component cluster property follows from
the ORIGINAL bridge-free extensions of all proper rooted
subalphabet components, with NO independent lower cluster
property hypothesis.

The proof uses strong induction on |A|, actual nested signed
component identities and their bridge-free heredity, and
the previously certified exact higher Lemma 4.3. -/
theorem exactSignedClusterProperty_of_allLowerRootedBridgeFree
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hBridge : K.HasAllLowerRootedBridgeFree
      hadm hgen hret) :
    K.HasExactSignedWholeComponentClusterProperty
      hadm hgen hret := by
  have hInduction :
      ∀ (n : ℕ)
        (S : Finset ι)
        (T : CayleySubgraphSpec gen S)
        (hAdmT : T.AdmissibleForCosetExtension),
          S.card = n →
          T.HasAllLowerRootedBridgeFree hAdmT hgen hret →
          T.HasExactSignedWholeComponentClusterProperty
            hAdmT hgen hret := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S T hAdmT hCardT hBridgeT
        by_cases hSmall : S.card ≤ 2
        · exact T.card_le_two_hasExactSignedWholeComponentClusterProperty
            hSmall hgen hret
        · have hHigh : 3 ≤ S.card := by omega
          apply T.hasExactSignedWholeComponentClusterProperty_of_lowerClusters
            hAdmT hgen hret hHigh hBridgeT
          intro C hCP root
          have hCS : C ⊂ S :=
            (mem_allProperCosetFamily S C).mp hCP
          have hCcard : C.card < n := by
            have hLess : C.card < S.card := Finset.card_lt_card hCS
            omega
          have hAdmChild :=
            T.subalphabetComponentSubgraph_admissible
              hAdmT C hCS root
          have hBridgeChild :=
            T.lowerRootedBridgeFree_hereditary
              hAdmT hgen hret hBridgeT C hCS root
          exact ih C.card hCcard C
            (T.subalphabetComponentSubgraph C root)
            hAdmChild rfl hBridgeChild
  exact hInduction A.card A K hadm rfl hBridge

end CayleySubgraphSpec
end ABO
end PSTSEPPA
