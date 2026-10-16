import PSTSEPPA.ABO.SourceLiteralY1X2AllPrintedPlainTransitionQuotient
import PSTSEPPA.ABO.CosetConnectivity

/-!
# EXACT A-supported vertex and signed-edge ranges of genuine Cayley stage covers

The corrected ABO Theorem 4.7(ii) is local over the TRUE
A-generated subgroup G[A], but the finite first-rank source
constructs a complete Cayley(G) action on the genuine
printed component-tagged H=T(Y₁) plain P_A stage.

For ANY complete signed stage T and ANY labelled graph map
F:Cayley(G)→T, we show:

* the orbit of a chosen group root g under the actual
  subalphabet subgroup G[A] maps to precisely the vertices
  reachable from F(g) by chronological SIGNED A-words;
* the actual original A-labelled directed Cayley edge
  tokens with source in gG[A] map to EXACTLY all signed
  stage A-edge tokens whose source lies in that
  A-reachable orbit.

This is stronger than merely giving a full G-Cayley map
with unrestricted signed-word image. It is the exact
local subgroup range that the source rank-two
P_A full-coset cover needs.

The edge theorem uses full signed labels and DETERMINISM
of the completed EGraph; inverse tokens, geometric loops,
trivial/repeated generators and A=∅ are included.
It does not conflate B-component tags or assume the
entire stage is A-connected. A local labelled
Cayley(G[A])-to-stage morphism, with outside-A labels
legally stationary, requires an additional proof
of the source stage's outside-A loop property.

We instantiate both exact local ranges for each
ACTUAL literal original T(Y₁) rooted P_A complete stage
and its already certified finite T(X₂^all) based Cayley
morphism. This is a genuine source-facing local
action/cover API and not yet Theorem 4.7(ii)/(iii)
or unconditional PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)

/-- The image of a translated real generated LEFT A-coset
under a genuine signed Cayley-to-stage map is precisely
the stage's intrinsic A-word orbit of the chosen image
root; NO global stage connectedness is assumed. -/
theorem localAlphabetCayley_vertex_range
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (A : Finset ι) (g : Γ) :
    Set.range (fun x : generatedSubgroup gen A =>
      F.onVertex (g * (x : Γ))) =
    {v : V | ∃ w : LabelWord ι, LabelWord.Uses A w ∧
      T.followWord (F.onVertex g) w = v} := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨w, hw, hx⟩ :=
      exists_word_uses_eq_of_mem_generatedSubgroup gen A x.2
    refine ⟨w, hw, ?_⟩
    calc
      T.followWord (F.onVertex g) w =
          F.onVertex ((cayleyGraph gen).followWord g w) :=
        T.hom_followWord (cayleyGraph gen) F g w
      _ = F.onVertex (g * PSTS.SignedWord.evalGroup gen w) :=
        congrArg F.onVertex (cayleyGraph.followWord_eq_mul_evalGroup gen g w)
      _ = F.onVertex (g * (x : Γ)) := by rw [hx]
  · rintro ⟨w, hw, hv⟩
    let x : generatedSubgroup gen A :=
      ⟨PSTS.SignedWord.evalGroup gen w,
        evalGroup_mem_generatedSubgroup_of_uses gen A hw⟩
    refine ⟨x, ?_⟩
    change F.onVertex (g * PSTS.SignedWord.evalGroup gen w) = v
    rw [← cayleyGraph.followWord_eq_mul_evalGroup gen g w]
    exact (T.hom_followWord (cayleyGraph gen) F g w).symm.trans hv

/-- The image of ALL ACTUAL oriented SIGNED Cayley
A-edge tokens with source inside a fixed translated
G[A] coset equals exactly the set of stage A-labelled
directed signed edge tokens with source in its genuine
A-reachable orbit. Neither sign nor missing edge
support is discarded. -/
theorem localAlphabetCayley_edge_range
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (A : Finset ι) (g : Γ) :
    Set.range
      (fun xs : generatedSubgroup gen A ×
        {s : SignedLabel ι // signedBase s ∈ A} =>
        F.onEdge (g * (xs.1 : Γ), xs.2.1)) =
    {e : Edge |
      (∃ w : LabelWord ι, LabelWord.Uses A w ∧
        T.followWord (F.onVertex g) w = T.source e) ∧
      signedBase (T.label e) ∈ A} := by
  ext e
  constructor
  · rintro ⟨⟨x, s⟩, rfl⟩
    obtain ⟨w, hw, hx⟩ :=
      exists_word_uses_eq_of_mem_generatedSubgroup gen A x.2
    constructor
    · refine ⟨w, hw, ?_⟩
      calc
        T.followWord (F.onVertex g) w =
            F.onVertex ((cayleyGraph gen).followWord g w) :=
          T.hom_followWord (cayleyGraph gen) F g w
        _ = F.onVertex (g * PSTS.SignedWord.evalGroup gen w) :=
          congrArg F.onVertex (cayleyGraph.followWord_eq_mul_evalGroup gen g w)
        _ = F.onVertex (g * (x : Γ)) := by rw [hx]
        _ = T.source (F.onEdge (g * (x : Γ), s.1)) :=
          (F.map_source _).symm
    · have hs : T.label (F.onEdge (g * (x : Γ), s.1)) = s.1 :=
        F.map_label _
      simpa only [hs] using s.2
  · rintro ⟨⟨w, hw, heq⟩, hs⟩
    let x : generatedSubgroup gen A :=
      ⟨PSTS.SignedWord.evalGroup gen w,
        evalGroup_mem_generatedSubgroup_of_uses gen A hw⟩
    let s : {s : SignedLabel ι // signedBase s ∈ A} :=
      ⟨T.label e, hs⟩
    refine ⟨(x, s), ?_⟩
    change F.onEdge (g * PSTS.SignedWord.evalGroup gen w, T.label e) = e
    apply T.deterministic
    · calc
        T.source (F.onEdge
            (g * PSTS.SignedWord.evalGroup gen w, T.label e)) =
          F.onVertex (g * PSTS.SignedWord.evalGroup gen w) :=
          F.map_source _
        _ = F.onVertex ((cayleyGraph gen).followWord g w) :=
          congrArg F.onVertex (cayleyGraph.followWord_eq_mul_evalGroup gen g w).symm
        _ = T.followWord (F.onVertex g) w :=
          (T.hom_followWord (cayleyGraph gen) F g w).symm
        _ = T.source e := heq
    · exact F.map_label _

end CompleteEGraph

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Source instance: the exact image of the finite
literal G₂[A] under the ACTUAL based signed Cayley
cover of any selected T(Y₁)-rooted ordinary P_A stage
is its genuine signed A-word orbit. This is NOT an
ambient-value quotient of the tagged stage. -/
theorem sourceLiteralY1X2AllPrintedPlain_localA_vertex_range
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A))) :
    Set.range (fun x : generatedSubgroup
      (sourceLiteralY1X2AllGenerator src dst) A =>
      (sourceLiteralY1X2AllPrintedPlainCayleyHom
        src dst base A hcard root u).onVertex x.1) =
    {v | ∃ w : LabelWord ι, LabelWord.Uses A w ∧
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).followWord u w = v} := by
  simpa only [one_mul,
    sourceLiteralY1X2AllPrintedPlainCayleyHom_one] using
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).localAlphabetCayley_vertex_range
          (sourceLiteralY1X2AllGenerator src dst)
          (sourceLiteralY1X2AllPrintedPlainCayleyHom
            src dst base A hcard root u) A 1

/-- Source instance: the actual literal local G₂[A]
A-labelled signed Cayley edges cover EXACTLY the
formally oriented original completed-stage A-edges
whose sources are accessible from the chosen true
tagged H root by signed A-words. -/
theorem sourceLiteralY1X2AllPrintedPlain_localA_edge_range
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A))) :
    Set.range (fun xs : generatedSubgroup
        (sourceLiteralY1X2AllGenerator src dst) A ×
        {s : SignedLabel ι // signedBase s ∈ A} =>
      (sourceLiteralY1X2AllPrintedPlainCayleyHom
        src dst base A hcard root u).onEdge
          (xs.1.1, xs.2.1)) =
    {e |
      (∃ w : LabelWord ι, LabelWord.Uses A w ∧
        (sourceLiteralY1SelectedRootPlainCompleteStage
          src dst base A hcard root).followWord u w =
        (sourceLiteralY1SelectedRootPlainCompleteStage
          src dst base A hcard root).source e) ∧
      signedBase ((sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).label e) ∈ A} := by
  simpa only [one_mul,
    sourceLiteralY1X2AllPrintedPlainCayleyHom_one] using
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).localAlphabetCayley_edge_range
          (sourceLiteralY1X2AllGenerator src dst)
          (sourceLiteralY1X2AllPrintedPlainCayleyHom
            src dst base A hcard root u) A 1

end ABO
end PSTSEPPA
