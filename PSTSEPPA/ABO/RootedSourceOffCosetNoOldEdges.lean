import PSTSEPPA.ABO.RootedSourceAllProperCompletedStageIso
import PSTSEPPA.ABO.RootedSourceOffCosetIndexEquiv
import PSTSEPPA.ABO.RankTwoSingletonAugmentationInput

/-!
# No old signed B-edge at the TRUE source-rooted augmentation point

At rank two, corrected ABO Definition 5.3 type-(2) attaches a full
B-coset to a vertex z outside every existing component-tagged
B-coset constituent. The source H1-cover is an INCOMPLETE signed
Cayley graph, and ambient H1 is only 2-retractable.

The previously certified local Γ[A] rank-two singleton theorem
forbids EVERY outgoing B-signed old edge at z, even geometric
loops. Using the genuine signed edge-bijective source/local
multi-coset graph isomorphism, we transfer this exact predicate to
the ORIGINAL source-rooted multi-coset quotient.

The source/off-B hypothesis is the literal tagged quotient condition
from #389, not non-membership in an ambient Γ[B]-coset. This is the
precise no-collision premise needed to attach a NEW source B-coset
as a deterministic EGraph. The augmentation itself and its signed
edge naturality remain separate geometric obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The oriented signed edge-quotient carrier of the TRUE
source-rooted P_A multi-coset graph (before trivial completion).
It uses glued SOURCE and full SIGNED label, not Γ-coordinates. -/
noncomputable abbrev rootedAmbientAllProperRawEdgeQuotient
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex) :=
  Quotient (sourceLabelEdgeSetoid
    (K.rootedAmbientMultiCosetRawGraph A hcard hret root
      (allProperCosetFamily A)).source
    (K.rootedAmbientMultiCosetRawGraph A hcard hret root
      (allProperCosetFamily A)).label)

/-- A source-rooted old quotient vertex OUTSIDE its selected
full B-coset copy has NO genuine outgoing B-labelled edge,
including inverse edges and old loops. Ambient Γ need only be
2-retractable, and source Γ[A] may have distinct tagged vertices
with the same ambient group value.

This is the exact missing-edge condition of
`IsolatedCosetGluing.gluedEGraph` for type-(2) augmentation. -/
theorem rootedAmbientOffCoset_no_old_B_edge
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
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
    (e : K.rootedAmbientAllProperRawEdgeQuotient A hcard hret root)
    (hsource :
      (K.rootedAmbientMultiCosetCompletedEGraph
        A hcard hret root (allProperCosetFamily A)).source e =
      (K.rootedLocalMultiCosetVertexQuotientEquiv
        A hcard hret root (allProperCosetFamily A)) z) :
    signedBase
      ((K.rootedAmbientMultiCosetCompletedEGraph
        A hcard hret root (allProperCosetFamily A)).label e) ∉ B := by
  let P := allProperCosetFamily A
  let L := K.intrinsicComponentLocalSlice A root
  let hadm : L.AdmissibleForCosetExtension :=
    L.admissible_of_card_le_two hcard.le
  let hgen : IsGenerated (trivialCompletionGenerator gen A) :=
    isGenerated_trivialCompletionGenerator gen A
  let hretL : Retractable (trivialCompletionGenerator gen A) :=
    retractable_trivialCompletionGenerator_of_kRetractable
      gen 2 hret A hcard.le
  let GL := K.rootedLocalMultiCosetCompletedEGraph A hcard hret root P
  let GM := K.rootedAmbientMultiCosetCompletedEGraph A hcard hret root P
  let f := K.rootedMultiCosetCompletedEGraphHom A hcard hret root P
  have hbij := K.rootedMultiCosetCompletedEGraphHom_bijective
    A hcard hret root P
  have hOffLocal :
      ¬ ∃ p : L.AttachedCosetVertex B,
        L.multiCosetInclude P hadm hgen hretL B hBP p = z := by
    exact (K.rootedLocalMultiCosetOffCoset_iff
      A hcard hret root P B hBP z).mpr hOffSource
  obtain ⟨d, hd⟩ := hbij.2.2 e
  have hsourceL : GL.source d = z := by
    apply hbij.1.1
    calc
      f.onVertex (GL.source d) = GM.source (f.onEdge d) :=
        (f.map_source d).symm
      _ = GM.source e := by rw [hd]
      _ = f.onVertex z := hsource
  have hsourceCanonical :
      (L.multiCosetEGraph P hadm hgen hretL).source d = z := by
    exact hsourceL
  have hMissingLocal :
      signedBase (GL.label d) ∉ B := by
    exact L.rank_two_off_selected_B_no_outgoing_edges
      hcard.le hgen hretL B hBP z hOffLocal d hsourceCanonical
  intro hlabelB
  have hlabelLocal : signedBase (GL.label d) ∈ B := by
    have hmap : GM.label (f.onEdge d) = GL.label d :=
      f.map_label d
    rw [← hd, hmap] at hlabelB
    exact hlabelB
  exact hMissingLocal hlabelLocal

end CayleySubgraphSpec
end ABO
end PSTSEPPA
