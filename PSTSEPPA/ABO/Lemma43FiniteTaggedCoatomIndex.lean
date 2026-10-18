import PSTSEPPA.ABO.CoatomEdgeCover
import PSTSEPPA.ABO.FiniteRankTwoType2Stages
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.Lemma43TaggedSliceOverlapByDeletion

/-!
# ABO Lemma 4.3: finite universe of genuine tagged proper constituents

The source's finite maximal-constituent covering is not a cover
by UNTAGGED ambient group cosets: every constituent carries one
intrinsic old skeleton component index. Here we expose the
appropriate finite index type and the exact old/fresh signed
coatom edge-cover witnesses.

An index is a pair (C,c), with C an ACTUAL selected proper
alphabet of A and c an original K.C-component. It is finite
whenever the ambient labelled group Γ is finite: K.Vertex is a
subtype of Γ and every K.C-component index is a quotient of it.

For every true oriented signed edge of the original
full proper-alphabet coset extension, certified CoatomEdgeCover
provides an exact completed coatom edge (C,p,s) equal as an
ORIENTED edge token, not just ambient group coordinates.
The two endpoints of that edge are in the SAME original
old-C-component-tagged completed constituent. We prove
this with the actual deterministic signed EGraph and the
certified selected-full-C edge closure lemma.

A similar true coatom tag exists for every quotient vertex.
Neither construction assumes the whole cluster property,
global Cayley injectivity, or any false old edge completion.

These are the finite-indexed source ingredients needed to
select one finite coatom-covering family for a particular
B-component Q and then use the already certified
Q-local edge-cover connectivity and finite common-core induction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact original-component-tagged selected proper constituent
index, including the alphabet and its GENUINE intrinsic old
skeleton connected-component index. This is deliberately not
a pair of an alphabet and an untagged ambient Cayley coordinate. -/
abbrev ProperCosetTag :=
  Σ C : {C : Finset ι //
    C ∈ (allProperCosetFamily A).alphabets},
    K.ComponentIndex C.1

/-- The selected alphabet of a genuine original tagged constituent. -/
def properCosetTagAlphabet (t : K.ProperCosetTag) : Finset ι :=
  t.1.1

/-- The alphabet carried by a genuine tag is selected. -/
theorem properCosetTagAlphabet_mem
    (t : K.ProperCosetTag) :
    K.properCosetTagAlphabet t ∈
      (allProperCosetFamily A).alphabets :=
  t.1.2

/-- The exact intrinsic original connected-component index. -/
def properCosetTagIndex (t : K.ProperCosetTag) :
    K.ComponentIndex (K.properCosetTagAlphabet t) :=
  t.2

/-- The selected original component-tagged B-component slice. -/
def properCosetTagSlice
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (t : K.ProperCosetTag) :
    Set (K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :=
  K.allProperCoset_taggedConstituentSlice
    hadm hgen hret B anchor
    (K.properCosetTagAlphabet t)
    (K.properCosetTagAlphabet_mem t)
    (K.properCosetTagIndex t)

/-- Finite original group means there are only finitely many
ORIGINAL component-tagged selected proper constituent identities. -/
theorem finite_properCosetTag
    [Finite Γ] : Finite K.ProperCosetTag := by
  classical
  change Finite (Σ C : {C : Finset ι //
    C ∈ (allProperCosetFamily A).alphabets}, K.ComponentIndex C.1)
  exact @Finite.instSigma _ _
    (inferInstance : Finite {C : Finset ι //
      C ∈ (allProperCosetFamily A).alphabets})
    (fun C => K.finite_componentIndex C.1)

/-- For finite Γ, the actual ORIENTED SIGNED old+fresh edge-token
quotient of the full proper coset extension is itself finite.
No artificial old edges have been added. -/
theorem finite_allProper_signed_edge_tokens
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Finite (K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret) := by
  classical
  let P := allProperCosetFamily A
  letI : Fintype Γ := Fintype.ofFinite _
  letI : Finite (ActionEdge Γ ι) := finite_actionEdge
  letI : Finite K.Edge :=
    Finite.of_injective (fun e : K.Edge => e.1)
      (fun _ _ h => Subtype.ext h)
  have hOutside (C : Finset ι) : Finite (K.OutsideEdge C) := by
    exact Finite.of_injective
      (fun e : K.OutsideEdge C => e.1)
      (fun _ _ h => Subtype.ext h)
  have hCoset (C : Finset ι) : Finite (K.CosetEdge C) := by
    letI : Finite (K.AttachedCosetVertex C) :=
      K.finite_attachedCosetVertex C
    letI : Finite {s : SignedLabel ι // signedBase s ∈ C} :=
      Finite.of_injective
        (fun s : {s : SignedLabel ι // signedBase s ∈ C} => s.1)
        (fun _ _ h => Subtype.ext h)
    letI : Fintype (K.AttachedCosetVertex C) := Fintype.ofFinite _
    letI : Fintype {s : SignedLabel ι // signedBase s ∈ C} :=
      Fintype.ofFinite _
    exact Fintype.finite
      (inferInstance :
        Fintype (K.AttachedCosetVertex C ×
          {s : SignedLabel ι // signedBase s ∈ C}))
  letI : Finite (K.MultiCosetRawEdge P) := by
    change Finite (Σ b : {B : Finset ι // B ∈ P.alphabets},
      K.SingleCosetEdge b.1)
    exact @Finite.instSigma _ _
      (inferInstance : Finite {B : Finset ι // B ∈ P.alphabets})
      (fun b => by
        letI : Finite (K.OutsideEdge b.1) := hOutside b.1
        letI : Finite (K.CosetEdge b.1) := hCoset b.1
        change Finite (K.OutsideEdge b.1 ⊕ K.CosetEdge b.1)
        infer_instance)
  apply Finite.of_surjective
    (fun e : K.MultiCosetRawEdge P =>
      (Quotient.mk (K.multiCosetRawEdgeSetoid P hadm hgen hret) e :
        K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret))
  intro q
  induction q using Quotient.inductionOn with
  | h e => exact ⟨e, rfl⟩

/-- Every TRUE quotient vertex has an original-tagged coatom
constituent presentation (the one needed for a root slice).
All group-coordinate and intrinsic old-component witnesses
are preserved through the selected gluing quotient. -/
theorem allProperCoset_vertex_exists_tagged_coatom
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    ∃ t : K.ProperCosetTag,
      (K.properCosetTagAlphabet t).card + 1 = A.card ∧
      ∃ p : K.AttachedCosetVertex
        (K.properCosetTagAlphabet t),
        p.1 = K.properCosetTagIndex t ∧
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret
          (K.properCosetTagAlphabet t)
          (K.properCosetTagAlphabet_mem t) p = z := by
  obtain ⟨C, hCP, hCard, hSupported⟩ :=
    K.allProperCosetVertex_exists_coatom_support
      hadm hgen hret z
  obtain ⟨_hCP, p, hpz⟩ := hSupported
  let t : K.ProperCosetTag := ⟨⟨C, hCP⟩, p.1⟩
  exact ⟨t, hCard, p, rfl, hpz⟩

/-- Every ACTUAL oriented signed edge lies in some selected coatom
copy, with BOTH genuine endpoints in one original old-component
tag. No source-label overlap is accepted merely from ambient
Cayley coordinates: this uses the certified exact signed edge
presentation and selected-C original edge-closure theorem. -/
theorem allProperCoset_edge_exists_tagged_coatom
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret) :
    ∃ t : K.ProperCosetTag,
      (K.properCosetTagAlphabet t).card + 1 = A.card ∧
      ∃ (p q : K.AttachedCosetVertex
        (K.properCosetTagAlphabet t)),
        p.1 = K.properCosetTagIndex t ∧
        q.1 = K.properCosetTagIndex t ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).source e =
          K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret
            (K.properCosetTagAlphabet t)
            (K.properCosetTagAlphabet_mem t) p ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).target e =
          K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret
            (K.properCosetTagAlphabet t)
            (K.properCosetTagAlphabet_mem t) q := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨C, hCP, p, s, hCard, he⟩ :=
    K.allProperCosetEdge_exists_coatom_completed_presentation
      hadm hgen hret hcard e
  let t : K.ProperCosetTag := ⟨⟨C, hCP⟩, p.1⟩
  have hSource : G.source e =
      K.multiCosetInclude P hadm hgen hret C hCP p := by
    rw [← he]
    rfl
  have hLetter : signedBase (G.label e) ∈ C := by
    rw [← he]
    exact s.2
  obtain ⟨q, hqIndex, hTarget⟩ :=
    K.multiCoset_selected_B_step_stays_in_coset
      P hadm hgen hret C hCP p e hSource hLetter
  exact ⟨t, hCard, p, q, rfl, hqIndex,
    hSource, hTarget⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
