import PSTSEPPA.ABO.Lemma43HigherRankSignedDichotomyStrictLower

/-!
# Source ABO forward-induction input: strict lower-rank component data

The published Theorem 4.5 derives the cluster property of the
full proper A-coset extension using the already established
Lemma 4.3 and lower-rank hypotheses. The accepted formalization
of Lemma 4.3 now gives a TRUE original signed full-B-coset
versus proper B-cluster EGraph dichotomy under lower-rank
bridge-freeness and MINIMUM tagged supports at exactly the
STRICT lower intersection alphabets D=B∩C⊊C.

In the paper, the lower hypotheses apply UNIFORMLY as B ranges
over all proper alphabets of A. This file exposes one reusable
uniform assumption rather than supplying the same collection
of lower rooted C-component data separately for every B.

It proves:

* the uniform lower input implies the exact per-B strict
  Lemma-4.3 inductive assumptions, without demanding an
  impossible proper support for D=C (a complete C-coset);
* hence EVERY genuine original signed B-component of the
  parent extension satisfies the published full-vs-proper
  signed coset/cluster dichotomy, for ALL B⊊A;
* in the source non-full-B-coset branch there is in addition
  one ATTAINED original-component-tagged minimum support
  for the ENTIRE signed B-component, and a genuine proper
  translated signed B-cluster isomorphism on all original
  vertices and directed signed edge tokens.

This is a source-faithful UNIFORM FORWARD STEP under explicit
lower COMPONENT MINIMUM hypotheses. It does NOT yet prove
the full Theorem 4.5, which assumes only lower bridge-freeness
plus embeddedness and DERIVES these lower component minima
from the lower cluster property by induction on |A|.

The remaining source naturality of the true old/fresh
component-tagged full proper CE under local subgroup H[C]
is also not assumed here. The generic Γ in this module is
globally generated and retractable; paper-local H[A]
retractability is handled algebraically in the separate
localization API.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- One UNIFORM lower-rank hypothesis for the source forward
step. Every ACTUAL rooted C-component's lower P_C CE is
bridge-free; its genuine signed D-components have attained
minimum old-component-tagged support strictly below C ONLY
WHEN D⊊C.

Unlike a per-B hypothesis, this is suitable for recursion
through all proper B⊊A in the source Theorem 4.5.

It is a predicate, not an added Lean axiom. -/
def HasUniformStrictLowerComponentInput
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) : Prop :=
  (∀ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (root : K.Vertex),
      (K.subalphabetComponentSubgraph C root).MultiCosetBridgeFree
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
        hgen hret) ∧
  (∀ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (D : Finset ι) (hDC : D ⊂ C)
      (root : K.Vertex),
      ∀ x₀ : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
        hgen hret,
      ∃ (M : Finset ι) (hMC : M ⊂ C)
        (m : (K.subalphabetComponentSubgraph C root).ComponentIndex M),
        (K.subalphabetComponentSubgraph C root).IsMinimalTaggedSupportFor
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
          hgen hret
          {x | ∃ w : LabelWord ι, LabelWord.Uses D w ∧
            ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
              (allProperCosetFamily C)
              (K.subalphabetComponentSubgraph_admissible
                hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
              hgen hret).Follows x₀ w x}
          M m)

/-- Uniform bridge-free + strict-D minimum data provide exactly
the hypotheses needed by the already certified Lemma 4.3
for any chosen B⊊A. No minimum is required for D=C. -/
theorem strictLowerLemma43Induction_of_uniform
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hUniform : K.HasUniformStrictLowerComponentInput
      hadm hgen hret)
    (B : Finset ι) :
    K.HasStrictLowerLemma43Induction hadm hgen hret B := by
  refine ⟨hUniform.1, ?_⟩
  intro C hCP hDC root x₀
  exact hUniform.2 C hCP (B ∩ C) hDC root x₀

/-- The source ABO Lemma-4.3 SIGNED dichotomy is valid
UNIFORMLY for ALL proper B⊊A under one set of
lower rooted component hypotheses: an original
full B-coset OR an actual translated proper
B-cluster labelled-graph isomorphism on VERTICES
and all genuine ORIENTED signed EDGE TOKENS. -/
theorem allProperCoset_uniform_forward_signed_dichotomy
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (hUniform : K.HasUniformStrictLowerComponentInput
      hadm hgen hret) :
    ∀ (B : Finset ι)
      (_hBP : B ∈ (allProperCosetFamily A).alphabets)
      (anchor : K.MultiCosetVertex
        (allProperCosetFamily A) hadm hgen hret),
      K.HasFullSignedBCosetAlternative
        hadm hgen hret B anchor ∨
      K.HasProperSignedBClusterAlternative
        hadm hgen hret B anchor := by
  intro B hBP anchor
  exact K.allProperCoset_higher_rank_signed_cluster_dichotomy_of_strict_lower
    hadm hgen hret hAcard B hBP anchor
    (K.strictLowerLemma43Induction_of_uniform
      hadm hgen hret hUniform B)

/-- In the non-full-B branch, the same uniform lower
induction supplies BOTH the whole-component's attained
ORIGINAL tagged MINIMUM and its actual PROPER signed
cluster graph isomorphism. This is the source Definition
3.22 minimum-support content, not merely graph shape. -/
theorem allProperCoset_uniform_forward_noFull_minimum_and_signed_cluster
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (hUniform : K.HasUniformStrictLowerComponentInput
      hadm hgen hret)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (hNoFull :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C anchor) :
    ∃ (M : Finset ι) (m : K.ComponentIndex M),
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
        M m ∧
      K.HasProperSignedBClusterAlternative
        hadm hgen hret B anchor := by
  obtain ⟨hBridge, hMin⟩ := hUniform
  obtain ⟨M, m, hM⟩ :=
    K.allProperCoset_noFull_B_component_minimum_of_strict_lower_induction
      hadm hgen hret hAcard B hBP anchor hNoFull
      hBridge
      (fun C hCP hDlocal root x₀ =>
        hMin C hCP (B ∩ C) hDlocal root x₀)
  exact ⟨M, m, hM,
    K.allProperCoset_no_full_B_component_signedClusterIso_of_minimum
      hadm hgen hret (by omega) B M anchor m hNoFull hM⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
