import PSTSEPPA.ABO.ForwardInductionOriginalFullCosetTag
import PSTSEPPA.ABO.Lemma43FullBCosetSignedEdgeCompleteness
import PSTSEPPA.ABO.RootedSignedBComponentGraphIso

/-!
# ABO 4.5: ORIGINAL Γ-rooted full B-component has every real signed B-step

The full-B-coset alternative of the source theorem requires the
completed B-component to have the actual oriented positive AND
inverse B-edge token from each of its vertices. Ambient group
word-completeness is not enough: our original Γ skeleton can have
genuinely missing signed old edges.

Using the already certified local full component edge-existence
lemma and the bijective labelled original/local EGraph isomorphism,
we prove REAL signed edge completeness of the ORIGINAL Γ-rooted
B-component. No ambient Γ global retractability/generation, false
original edge, coordinate collapse, additional axiom or sorry.

Together with the previous genuinely ORIGINAL old D-component tag
invariance, this supplies the two essential original full-coset
clauses. Literal original D-summand edge presentation remains a
separate source-facing claim.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every source Γ-rooted B-component vertex of an original
selected D-coset, B⊆D, admits an actual directed signed edge
token with EACH signed B-letter, in the ORIGINAL completed
multi-coset quotient itself. Both the path condition and the
edge token are original Γ-rooted ones, not simulated paths
in the generated local subgroup. -/
theorem arbitraryRankRootedOriginal_fullBComponent_allSignedSteps
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι) (hDP : D ∈ P.alphabets)
    (B : Finset ι) (hBD : B ⊆ D)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D)
    (y : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret))
    (hy : y ∈ (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).BComponentVertexSet B
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret
        ((K.intrinsicComponentLocalSlice C root).multiCosetInclude
          P hadm hgen hret D hDP p)))
    (s : SignedLabel ι) (hs : signedBase s ∈ B) :
    ∃ a,
      a ∈ (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).BComponentEdgeSet B
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root P hadm hgen hret
            ((K.intrinsicComponentLocalSlice C root).multiCosetInclude
              P hadm hgen hret D hDP p)) ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).source a = y ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).label a = s := by
  let L := K.intrinsicComponentLocalSlice C root
  let G := K.arbitraryRankRootedLocalCompletedEGraph
    C root P hadm hgen hret
  let H := K.arbitraryRankRootedOriginalCompletedEGraph
    C root P hadm hgen hret
  let f := K.arbitraryRankRootedCompletedEGraphHom
    C root P hadm hgen hret
  have hbij := K.arbitraryRankRootedCompletedEGraphHom_bijective
    C root P hadm hgen hret
  obtain ⟨x, hx⟩ := hbij.1.2 y
  have hxB : x ∈ G.BComponentVertexSet B
      (L.multiCosetInclude P hadm hgen hret D hDP p) := by
    apply (G.BComponentVertex_mem_iff_bijective
      H f hbij.1 hbij.2 B
        (L.multiCosetInclude P hadm hgen hret D hDP p) x).mpr
    change y ∈ H.BComponentVertexSet B (f.onVertex
      (L.multiCosetInclude P hadm hgen hret D hDP p)) at hy
    rw [hx]
    exact hy
  obtain ⟨d, hdB, hdSrc, hdLab⟩ :=
    L.multiCoset_full_B_component_all_signed_steps_exist
      P hadm hgen hret D hDP B hBD p x hxB s hs
  refine ⟨f.onEdge d, ?_, ?_, ?_⟩
  · exact (G.BComponentEdge_mem_iff_bijective
      H f hbij.1 hbij.2 B
        (L.multiCosetInclude P hadm hgen hret D hDP p) d).mp hdB
  · calc
      H.source (f.onEdge d) = f.onVertex (G.source d) :=
        f.map_source d
      _ = f.onVertex x := by
        change f.onVertex
          ((L.multiCosetEGraph P hadm hgen hret).source d) =
            f.onVertex x
        exact congrArg f.onVertex hdSrc
      _ = y := hx
  · calc
      H.label (f.onEdge d) = G.label d := f.map_label d
      _ = s := hdLab

end CayleySubgraphSpec
end ABO
end PSTSEPPA
