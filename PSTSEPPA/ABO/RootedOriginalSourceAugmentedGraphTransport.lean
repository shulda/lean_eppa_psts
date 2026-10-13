import PSTSEPPA.ABO.RootedFullBAugmentationGraphIso
import PSTSEPPA.ABO.RootedSourceOffCosetNoOldEdges
import PSTSEPPA.ABO.RootedSourceMultiCosetAmbientValue

/-!
# Literal source-rooted B-augmentation signed graph transport at rank two

The ambient original H1 source group is only 2-retractable. Its true
component-tagged old proper-coset extension is signed-EGraph-isomorphic
to the local Γ[A] normalization, |A|=2. The old source/root B-edge
exclusion is certified without global retractability.

Here we instantiate the generic OLD+NEW B-coset augmentation theorem
on the actual K-rooted source components, not on hypothetical Cayley
embeddings. The local old graph is the genuine full proper-coset EGraph
on Γ[A]; the source old graph is the exact tagged quotient over Γ.

At an eligible old vertex z (outside the selected B-coset
constituent), the local attached full B-coset is rooted at the
true local group-coordinate of z, while the original source B-coset
is rooted at its precise TRANSLATED coordinate root.value*localValue(z).
The source value equality is certified independently. Nothing collapses
two differently tagged old vertices with coinciding group coordinates.

This gives a genuine signed EGraph isomorphism of the root-translated
old+new augmented graphs, before stationary-loop completion. The
named exact-source Definition-5.3 API identification and the global
Z1 catalogue/source Condition 5.2 remain separate obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- Local source-eligible augmentation roots have NO outgoing
old signed B-edge in their genuine Γ[A] full proper-coset EGraph.
Uses exact source/local off-B tag equivalence, not ambient values. -/
theorem rootedLocalOffCoset_no_old_B_edge
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z)
    (e : (K.intrinsicComponentLocalSlice A root).
      MultiCosetEdgeVertexIncidenceQuotient
        (allProperCosetFamily A)
        ((K.intrinsicComponentLocalSlice A root).
          admissible_of_card_le_two hcard.le)
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le))
    (hsource :
      (K.rootedLocalMultiCosetCompletedEGraph
        A hcard hret root (allProperCosetFamily A)).source e = z) :
    signedBase
      ((K.rootedLocalMultiCosetCompletedEGraph
        A hcard hret root (allProperCosetFamily A)).label e) ∉ B := by
  let L := K.intrinsicComponentLocalSlice A root
  let P := allProperCosetFamily A
  let hadm := L.admissible_of_card_le_two hcard.le
  let hgen := isGenerated_trivialCompletionGenerator gen A
  let hretL := retractable_trivialCompletionGenerator_of_kRetractable
    gen 2 hret A hcard.le
  have hOffLocal :
      ¬ ∃ p : L.AttachedCosetVertex B,
        L.multiCosetInclude P hadm hgen hretL B hBP p = z :=
    (K.rootedLocalMultiCosetOffCoset_iff
      A hcard hret root P B hBP z).mpr hOffSource
  exact L.rank_two_off_selected_B_no_outgoing_edges
    hcard.le hgen hretL B hBP z hOffLocal e hsource

/-- The actual LOCAL Γ[A] old+new signed B-augmented graph
at a genuinely eligible original-source root. The B-coset root
is the REAL group coordinate of z, not a random representative. -/
noncomputable abbrev rootedLocalOffCosetAugmentedGraph
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z) :=
  IsolatedCosetGluing.gluedEGraph
    (K.rootedLocalMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    (trivialCompletionGenerator gen A) B
    ((K.intrinsicComponentLocalSlice A root).multiCosetAmbientValue
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le) z)
    z
    (by
      intro e he
      exact K.rootedLocalOffCoset_no_old_B_edge
        A hcard hret root B hBP z hOffSource e he)

/-- The identical TRUE original-source model, written
with its EXPLICIT rooted translated basepoint. The exact
equality with the ambient value of the glued root is #394. -/
noncomputable abbrev rootedTranslatedSourceOffCosetAugmentedGraph
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z) :=
  IsolatedCosetGluing.gluedEGraph
    (K.rootedAmbientMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    gen B
    (root.1 *
      (((K.intrinsicComponentLocalSlice A root).multiCosetAmbientValue
        (allProperCosetFamily A)
        ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
          hcard.le)
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le) z) : Γ))
    (K.rootedLocalMultiCosetVertexQuotientEquiv
      A hcard hret root (allProperCosetFamily A) z)
    (by
      intro e he
      exact K.rootedAmbientOffCoset_no_old_B_edge
        A hcard hret root B hBP z hOffSource e he)

/-- The COMPLETE old+new SOURCE B-augmentation is really
signed-graph-isomorphic to its local Γ[A] representative.

This is on all old tagged quotient vertices, all fresh B-coset
vertices, every old and new oriented signed edge token, and with
the exact old-root/new-coset basepoint identification. -/
noncomputable def rootedSourceOffCosetAugmentedGraphHom
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z) :
    LabelledGraphHom
      (K.rootedLocalOffCosetAugmentedGraph
        A hcard hret root B hBP z hOffSource).toLabelledGraph
      (K.rootedTranslatedSourceOffCosetAugmentedGraph
        A hcard hret root B hBP z hOffSource).toLabelledGraph :=
  rootedFullBAugmentationGraphHom
    (K.rootedLocalMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    (K.rootedAmbientMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    (K.rootedMultiCosetCompletedEGraphHom
      A hcard hret root (allProperCosetFamily A))
    (K.rootedMultiCosetCompletedEGraphHom_bijective
      A hcard hret root (allProperCosetFamily A)).1
    (K.rootedMultiCosetCompletedEGraphHom_bijective
      A hcard hret root (allProperCosetFamily A)).2
    gen A B ((allProperCosetFamily A).proper B hBP).subset
    root.1
    ((K.intrinsicComponentLocalSlice A root).multiCosetAmbientValue
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le) z)
    z
    (K.rootedLocalOffCoset_no_old_B_edge
      A hcard hret root B hBP z hOffSource)
    (K.rootedAmbientOffCoset_no_old_B_edge
      A hcard hret root B hBP z hOffSource)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
