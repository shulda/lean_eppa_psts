import PSTSEPPA.ABO.Lemma43FullBCosetSignedEdgeCompleteness
import PSTSEPPA.ABO.Lemma43NoFullComponentSignedClusterIsoFromMinimum

/-!
# ABO Lemma 4.3: the actual oriented signed B-component dichotomy

This is the literal TWO-CASE split of the EXISTING PUBLISHED ABO I
Lemma 4.3, expressed on the ORIGINAL incomplete old+fresh multi-CE
with exact intrinsic skeleton component tags and REAL oriented signed
edge tokens.

* If some selected C-constituent with B ⊆ C actually supports the
  component anchor, the B-component is the FULL component-tagged
  B-coset. The accepted exact vertex classification and signed edge
  completeness show that ALL original B-edges are completed edges of
  that SAME C-copy and that EVERY positive/inverse signed B-step from
  every component vertex exists INSIDE the original multiCE.

* Otherwise no selected E⊇B supports its anchor. Once the SOURCE
  lower-rank induction supplies the ENTIRE component's attained
  original component-tagged minimum support, the previously certified
  source #773 identifies its ORIGINAL oriented signed B-component
  with a genuine translated PROPER B-cluster graph by a labelled
  graph morphism BIJECTIVE on both vertex and oriented signed edge
  tokens. In this branch, every actual active coatom intersection
  alphabet B∩E is a PROPER subset of B, and a genuine common-core
  quotient vertex belongs to all tagged constituent slices.

The choice between the two cases needs NO extra hypothesis.
The only inductive input is the explicit implication
"if no full B-constituent supports the anchor, then the whole
component has an attained minimum tagged support."

This theorem does NOT assume or claim that that lower-rank minimum
exists for every arbitrary incomplete skeleton: obtaining it from
source Lemma 4.3's exact lower bridge-free/cluster hypotheses, and
localizing the printed rank-k retractability to H[A], remain
separate formalization steps. No new axiom, sorry, global Cayley
injection, or artificial old edge is involved.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The FULL-coset alternative of published Lemma 4.3 on
the actual original signed multiCE graph.

The selected C-copy has the correct original OLD C-component
tag; EVERY genuine signed B-component edge is such a C-edge,
and EVERY signed positive/inverse B-step exists from any
real B-component vertex inside the original extension. -/
def HasFullSignedBCosetAlternative
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) : Prop :=
  ∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets),
    B ⊆ C ∧
    ∃ (p : K.AttachedCosetVertex C),
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP p = anchor ∧
      (∀ e : K.MultiCosetEdgeVertexIncidenceQuotient
          (allProperCosetFamily A) hadm hgen hret,
        e ∈ (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).BComponentEdgeSet B anchor →
        ∃ (q : K.AttachedCosetVertex C)
          (s : {s : SignedLabel ι // signedBase s ∈ C}),
          q.1 = p.1 ∧
          e = K.multiCosetEdgeInclude (allProperCosetFamily A)
            hadm hgen hret C hCP (Sum.inr (q, s))) ∧
      (∀ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        y ∈ (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).BComponentVertexSet B anchor →
        ∀ (s : SignedLabel ι), signedBase s ∈ B →
          ∃ e : K.MultiCosetEdgeVertexIncidenceQuotient
            (allProperCosetFamily A) hadm hgen hret,
            e ∈ (K.multiCosetEGraph (allProperCosetFamily A)
              hadm hgen hret).BComponentEdgeSet B anchor ∧
            (K.multiCosetEGraph (allProperCosetFamily A)
              hadm hgen hret).source e = y ∧
            (K.multiCosetEGraph (allProperCosetFamily A)
              hadm hgen hret).label e = s)

/-- The PROPER-cluster alternative of published Lemma 4.3,
with the literal ORIGINAL signed B-component graph.

An actual common-core quotient vertex is B-reachable from the
anchor and lies in every original coatom-tagged constituent
meeting the component. The translated cluster target is
a genuine signed EGraph and its labelled morphism is
bijective on BOTH ORIGINAL vertices and signed edge tokens.

The hProper index proof guarantees proper B-cluster constituent
alphabets, not merely proper subalphabets of A. -/
def HasProperSignedBClusterAlternative
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) : Prop :=
  ∃ (core : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret)
    (hProper :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B),
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows anchor w core) ∧
    (∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
      core ∈ K.properCosetTagSlice hadm hgen hret B anchor t) ∧
    ∃ (T : EGraph
        {g : Γ // g ∈
          ClusterSpec.LeftTranslateSet
            (K.multiCosetAmbientValue
              (allProperCosetFamily A) hadm hgen hret core)
            ((K.activeTaggedLowerClusterSpec
              hadm hgen hret B anchor hProper).VertexSet gen)}
        {a : ActionEdge Γ ι // a ∈
          ClusterSpec.LeftTranslateEdgeSet
            (K.multiCosetAmbientValue
              (allProperCosetFamily A) hadm hgen hret core)
            ((K.activeTaggedLowerClusterSpec
              hadm hgen hret B anchor hProper).EdgeSet gen)} ι)
      (f : LabelledGraphHom
        ((K.multiCosetEGraph
          (allProperCosetFamily A) hadm hgen hret).BComponentEGraph
            B anchor).toLabelledGraph
        T.toLabelledGraph),
      Function.Bijective f.onVertex ∧
      Function.Bijective f.onEdge

/-- SOURCE Lemma 4.3, exact signed FULL-vs-PROPER dichotomy.

The FULL branch is obtained directly from a supporting selected
constituent E⊇B. Otherwise the ONLY necessary inductive input
is a minimum tagged support of the original whole B-component,
supplied conditionally by the lower-rank source induction.

There are NO further hidden path or common-core hypotheses.
This is a mathematical source theorem about the original signed
old+fresh quotient, not just equality of ambient Cayley coordinates. -/
theorem allProperCoset_signed_full_or_proper_cluster_of_minimum
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hMinIfNoFull :
      (∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C anchor) →
      ∃ (M : Finset ι) (m : K.ComponentIndex M),
        K.IsMinimalTaggedSupportFor
          (allProperCosetFamily A) hadm hgen hret
          {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
            (K.multiCosetEGraph (allProperCosetFamily A)
              hadm hgen hret).Follows anchor w y}
          M m) :
    K.HasFullSignedBCosetAlternative
      hadm hgen hret B anchor ∨
    K.HasProperSignedBClusterAlternative
      hadm hgen hret B anchor := by
  classical
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  by_cases hFull :
      ∃ (C : Finset ι) (hCP : C ∈ P.alphabets),
        B ⊆ C ∧
        K.MultiCosetVertexSupported P hadm hgen hret C anchor
  · left
    obtain ⟨C, hCP, hBC, ⟨_hC, p, hp⟩⟩ := hFull
    refine ⟨C, hCP, hBC, p, hp, ?_, ?_⟩
    · intro e he
      have he' :
          e ∈ G.BComponentEdgeSet B
            (K.multiCosetInclude P hadm hgen hret C hCP p) := by
        simpa only [hp] using he
      exact K.multiCoset_full_B_component_all_signed_edges_in_C
        P hadm hgen hret C hCP B hBC p e he'
    · intro y hy s hs
      have hy' :
          y ∈ G.BComponentVertexSet B
            (K.multiCosetInclude P hadm hgen hret C hCP p) := by
        simpa only [hp] using hy
      obtain ⟨e, he, heSource, heLabel⟩ :=
        K.multiCoset_full_B_component_all_signed_steps_exist
          P hadm hgen hret C hCP B hBC p y hy' s hs
      refine ⟨e, ?_, heSource, heLabel⟩
      simpa only [hp] using he
  · right
    have hNoFull :
        ∀ (C : Finset ι) (hCP : C ∈ P.alphabets),
          B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            P hadm hgen hret C anchor := by
      intro C hCP hBC hSupported
      exact hFull ⟨C, hCP, hBC, hSupported⟩
    obtain ⟨M, m, hMin⟩ := hMinIfNoFull hNoFull
    exact K.allProperCoset_no_full_B_component_signedClusterIso_of_minimum
      hadm hgen hret hcard B M anchor m hNoFull hMin

end CayleySubgraphSpec
end ABO
end PSTSEPPA
