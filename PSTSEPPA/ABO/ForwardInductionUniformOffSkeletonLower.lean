import PSTSEPPA.ABO.Lemma43SignedDichotomyOffSkeletonLower

/-!
# Corrected ABO forward induction: lower minima ONLY off lower old skeletons

Published Definition 3.22 supplies a whole-component minimum support
only for components DISJOINT from the original OLD skeleton. Previously
accepted stronger auxiliary hypotheses incorrectly requested such minima
for every lower D-component, even when D⊊C; that is not source-derived.

We now prove the uniform forward signed cluster induction under the
correct assumptions:
* all genuine lower rooted C-stages are bridge-free;
* for each proper lower D⊊C, a minimum of the lower D-component is
  required ONLY when the actual lower D-component avoids the old
  C-skeleton.

The per-B corrected Lemma 4.3 signed B-coset / translated proper
B-cluster theorem follows, for every B⊊A. The no-full-B branch
also has an ATTAINED minimum original tagged support of its whole
true B-component; its actual oriented signed edge graph is isomorphic
to the corresponding proper cluster.

The substantive lower off-skeleton premise is derived geometrically
via genuinely realized old/fresh signed paths in the predecessor
Lemma43LowerOffSkeletonGate and its source induction successors.
These are source-exact conditional forward implications: higher
bridgefreeness and unconditional PSTS EPPA are not claimed.
No invented old edges, global ambient-coordinate tag collapse,
new axioms, or sorry.
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
def HasUniformOffSkeletonLowerComponentInput
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
        (¬ ∃ (v : (K.subalphabetComponentSubgraph C root).Vertex)
          (w : LabelWord ι),
          LabelWord.Uses D w ∧
          ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
            (allProperCosetFamily C)
            (K.subalphabetComponentSubgraph_admissible
              hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
            hgen hret).Follows
              (((K.subalphabetComponentSubgraph C root).skeletonToMultiCosetHom
                (allProperCosetFamily C)
                (K.subalphabetComponentSubgraph_admissible
                  hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
                hgen hret D
                ((mem_allProperCosetFamily C D).mpr hDlocal)).onVertex v)
              w x₀) →
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
theorem offSkeletonLowerLemma43Induction_of_uniform
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hUniform : K.HasUniformOffSkeletonLowerComponentInput
      hadm hgen hret)
    (B : Finset ι) :
    K.HasOffSkeletonLowerLemma43Induction hadm hgen hret B := by
  refine ⟨hUniform.1, ?_⟩
  intro C hCP hDC root x₀ hOff
  exact hUniform.2 C hCP (B ∩ C) hDC root x₀ hOff

/-- The source ABO Lemma-4.3 SIGNED dichotomy is valid
UNIFORMLY for ALL proper B⊊A under one set of
lower rooted component hypotheses: an original
full B-coset OR an actual translated proper
B-cluster labelled-graph isomorphism on VERTICES
and all genuine ORIENTED signed EDGE TOKENS. -/
theorem allProperCoset_uniform_forward_signed_dichotomy_of_off_skeleton_lower
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (hUniform : K.HasUniformOffSkeletonLowerComponentInput
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
  exact K.allProperCoset_higher_rank_signed_cluster_dichotomy_of_off_skeleton_lower
    hadm hgen hret hAcard B hBP anchor
    (K.offSkeletonLowerLemma43Induction_of_uniform
      hadm hgen hret hUniform B)

/-- In the non-full-B branch, the same uniform lower
induction supplies BOTH the whole-component's attained
ORIGINAL tagged MINIMUM and its actual PROPER signed
cluster graph isomorphism. This is the source Definition
3.22 minimum-support content, not merely graph shape. -/
theorem allProperCoset_uniform_forward_noFull_minimum_and_signed_cluster_off_skeleton
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (hUniform : K.HasUniformOffSkeletonLowerComponentInput
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
    K.allProperCoset_noFull_B_component_minimum_of_off_skeleton_lower_induction
      hadm hgen hret hAcard B hBP anchor hNoFull
      hBridge
      (fun C hCP hDlocal root x₀ hOff =>
        hMin C hCP (B ∩ C) hDlocal root x₀ hOff)
  exact ⟨M, m, hM,
    K.allProperCoset_no_full_B_component_signedClusterIso_of_minimum
      hadm hgen hret (by omega) B M anchor m hNoFull hM⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
