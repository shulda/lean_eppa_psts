import PSTSEPPA.ABO.ProperClusterDoubleRootSignedIso
import PSTSEPPA.ABO.ForwardInductionOriginalCanonicalProperShape
import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedAmbientValue

/-!
# ABO 4.5: canonical ORIGINAL Γ-rooted proper B-cluster, exact signed shape

The source Γ-rooted local normalization constructs an actual signed
graph isomorphism of the ORIGINAL old-component-tagged B-component
onto a canonical *t-translated* proper B-cluster over H[C].
The certified two-root signed graph isomorphism from the preceding
module composes that with the exact ORIGINAL Γ-root translation
`root.1 * (t:Γ)`; this is the actual ambient group coordinate of
the original rooted core, proved by the existing exact naturality
theorem, not an invented ambient identification of old component tags.

We prove a source-facing literal translated Γ signed graph-shape
predicate, preserving entire true B-components, both edge
orientations, formal inversion, labels and signed word paths.
The core and constituent-support clauses here remain LOCAL tagged;
a subsequent source Γ-facing theorem must additionally transport
the original active coatom tags and the full-coset branch before
the full Definition 3.22 is claimed for merely k-retractable Γ.

No global Γ generation/retractability, fake old edge or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The actual ORIGINAL Γ-rooted B-component proper-cluster
SIGNED graph shape, with the exact ORIGINAL ambient
`root * (local core group coordinate)` as translation center,
formulated equivalently via the intrinsic ORIGINAL Γ quotient
ambient value of the matching TRUE old-component-tagged core.

The auxiliary lower coatom/core witnesses remain local H[C]
tags; these must not be misidentified with original source tags. -/
def ArbitraryRankRootedOriginalCanonicalGammaProperSignedAlternative
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret) : Prop :=
  ∃ (core : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
        (allProperCosetFamily C) hadm hgen hret)
    (hProper :
      ∀ s ∈ (K.intrinsicComponentLocalSlice C root).activeTaggedCoatoms
        hadm hgen hret B u,
        B ∩ (K.intrinsicComponentLocalSlice C root).properCosetTagAlphabet s ⊂ B),
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      ((K.intrinsicComponentLocalSlice C root).multiCosetEGraph
        (allProperCosetFamily C) hadm hgen hret).Follows u w core) ∧
    (∀ s ∈ (K.intrinsicComponentLocalSlice C root).activeTaggedCoatoms
        hadm hgen hret B u,
      core ∈ (K.intrinsicComponentLocalSlice C root).properCosetTagSlice
        hadm hgen hret B u s) ∧
    ∃ f : LabelledGraphHom
      ((K.arbitraryRankRootedOriginalCompletedEGraph
        C root (allProperCosetFamily C) hadm hgen hret).BComponentEGraph
        B (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
          C root (allProperCosetFamily C) hadm hgen hret u)).toLabelledGraph
      (((((K.intrinsicComponentLocalSlice C root).activeTaggedLowerClusterSpec
        hadm hgen hret B u hProper).rootTranslatedCayleySubgraph gen
          (K.arbitraryRankRootedOriginalMultiCosetValue
            C root (allProperCosetFamily C) hadm hgen hret
            (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
              C root (allProperCosetFamily C) hadm hgen hret core))).toEGraph).toLabelledGraph),
      Function.Bijective f.onVertex ∧ Function.Bijective f.onEdge

/-- The source ORIGINAL signed entire B-component is actually
isomorphic to the CANONICAL Γ-TRANSLATED proper cluster, with
the correct root and local core center, not just the previous
H[C]-translated cluster. Both genuine oriented signed edge
token maps are bijective. -/
theorem rootedOriginalProperSignedShape_canonicalGamma
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι) (hBC : B ⊆ C)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret)
    (hAlt : K.ArbitraryRankRootedOriginalCanonicalLocalProperSignedAlternative
      C root hadm hgen hret B u) :
    K.ArbitraryRankRootedOriginalCanonicalGammaProperSignedAlternative
      C root hadm hgen hret B u := by
  let L := K.intrinsicComponentLocalSlice C root
  let P := allProperCosetFamily C
  obtain ⟨core, hProper, hReach, hCommon, f, hv, he⟩ := hAlt
  refine ⟨core, hProper, hReach, hCommon, ?_⟩
  let Q := L.activeTaggedLowerClusterSpec hadm hgen hret B u hProper
  let t : generatedSubgroup gen C :=
    L.multiCosetAmbientValue P hadm hgen hret core
  let g := Q.localRootTranslatedClusterHomOfParent
    gen C hBC root.1 t
  have hg := Q.localRootTranslatedClusterHomOfParent_bijective
    gen C hBC root.1 t
  have hCenter :
      K.arbitraryRankRootedOriginalMultiCosetValue
        C root P hadm hgen hret
        (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
          C root P hadm hgen hret core) =
      root.1 * (t : Γ) :=
    K.arbitraryRankRootedOriginalMultiCosetValue_natural
      C root P hadm hgen hret core
  rw [hCenter]
  refine ⟨g.comp f, ?_, ?_⟩
  · change Function.Bijective (g.onVertex ∘ f.onVertex)
    exact ⟨hg.1.1.comp hv.1, hg.1.2.comp hv.2⟩
  · change Function.Bijective (g.onEdge ∘ f.onEdge)
    exact ⟨hg.2.1.comp he.1, hg.2.2.comp he.2⟩

/-- Γ-ROOTED source forward SHAPE from merely k-retractable
finite ambient Γ and actual normalized H[C] lower bridge-free
premises: original off-skeleton B-component has the local
full-B-coset alternative OR a TRUE original Γ root-translated
canonical signed B-cluster graph isomorphism.

Original component-tagged full-coset and active coatom/core
support transfer are separate required final gates. -/
theorem sourceKLocal_originalSignedFullOrCanonicalGammaProper
    (hadm : K.AdmissibleForCosetExtension)
    (k : ℕ) (hk : KRetractable gen k)
    (C : Finset ι) (hCA : C ⊆ A) (hCk : C.card ≤ k)
    (hcard : 2 ≤ C.card)
    (root : K.Vertex)
    (hBridge :
      (K.intrinsicComponentLocalSlice C root).HasAllLowerRootedBridgeFree
        (K.sourceInductionLocalAdmissibility hadm C hCA root)
        (isGenerated_trivialCompletionGenerator gen C)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen k hk C hCk))
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily C).alphabets)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk))
    (hOff : K.ArbitraryRankRootedOriginalOffSkeleton
      C root (allProperCosetFamily C)
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk)
      B
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root (allProperCosetFamily C)
        (K.sourceInductionLocalAdmissibility hadm C hCA root)
        (isGenerated_trivialCompletionGenerator gen C)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen k hk C hCk) u)) :
    (K.intrinsicComponentLocalSlice C root).HasFullSignedBCosetAlternative
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk) B u ∨
    K.ArbitraryRankRootedOriginalCanonicalGammaProperSignedAlternative
      C root
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk) B u := by
  have hShape :=
    K.sourceKLocal_originalSignedFullOrCanonicalLocalProper
      hadm k hk C hCA hCk hcard root hBridge B hBP u hOff
  rcases hShape with hFull | hProper
  · exact Or.inl hFull
  · exact Or.inr
      (K.rootedOriginalProperSignedShape_canonicalGamma
        C root
        (K.sourceInductionLocalAdmissibility hadm C hCA root)
        (isGenerated_trivialCompletionGenerator gen C)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen k hk C hCk)
        B ((mem_allProperCosetFamily C B).mp hBP).subset u hProper)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
