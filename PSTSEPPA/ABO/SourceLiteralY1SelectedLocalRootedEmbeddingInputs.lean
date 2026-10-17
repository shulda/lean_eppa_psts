import PSTSEPPA.ABO.SourceLiteralY1OldGToTaggedHVertexEdgeAgreement
import PSTSEPPA.ABO.SelectedOldComponentMultiCosetAmbientEmbedding
import PSTSEPPA.ABO.RootedSourceAllProperCompletedStageIso
import PSTSEPPA.ABO.LocalGeneratedSubgroupIsGenerated
import PSTSEPPA.ABO.KStablePullbackAdmissibility
import PSTSEPPA.ABO.StandardCosetFamily

/-!
# The actual FIRST-RANK local G[A]→H[A] rooted embedding inputs

The accepted source tower is the genuine labelled quotient
  G = T(X₂^all) ↠ H = T(Y₁)
with only ONE-stability and TWO-retractability. Corrected ABO
Theorem 4.7(ii) must be applied to the actual *local*
G[A]→H[A] generated groups, not the generally nonretractable
global groups, and to the ACTUAL old signed A-component,
not an entire ambient coset (nor the artificially completed X₁
edge graph).

Given a TRUE printed original-input H-root and |A|=2, we
literally restrict the original incomplete H skeleton to A,
extract the intrinsic old A-component of the specified root,
and inverse-translate it into the real subgroup H[A].
This is the local old skeleton L_H. Its G[A] counterpart is
the genuine quotient pullback Q_A⁻¹(L_H), which may have
SEVERAL original signed A-components. We choose the one
containing the true identity group root.

ALL algebraic/geometric environmental hypotheses of the
component-scoped embedding theorem now hold UNCONDITIONALLY:
  - local groups are generated and fully retractable;
  - the actual H-local old skeleton and its G-local
    quotient pullback are admissible;
  - the all-proper coset family is genuinely weakly complete
    over the H-local incomplete skeleton;
  - Q_A remains one-stable, hence is stable on every
    proper B⊊A;
  - identity belongs to the true old G-pullback and selects
    one ORIGINAL intrinsic signed A-component.

The final theorem then applies the existing true ROOTED
mixed B/C-component-support gluing result to prove that one
specified OLD G A-component's FULL attached-coset region
embeds into its ambient G[A] Cayley group, conditional only
on a precisely normalized full signed Cayley(G[A]) cover
of the genuinely completed H-local P_A stage.

This last cover is *not* silently identified with the
independently certified literal printed T(Y₁) stage
cover. Transport along the real old-component signed
stage isomorphisms is the next explicit proof gate.
No global pullback connectedness, ambient H-coordinate
injectivity, arbitrary G[A]-stability or PSTS EPPA is
asserted by the present theorem.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The ACTUAL original-input intrinsic rooted H A-component,
translated into the genuinely generated H[A] subgroup.
All old missing edges remain missing, with both formal signs
and original component tags retained. -/
noncomputable abbrev sourceLiteralY1SelectedLocalHOldSkeleton
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :=
  ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A)
    .intrinsicComponentLocalSlice A
      (⟨root, by trivial⟩ :
        ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).Vertex)

/-- The exact LOCAL original G[A] skeleton lying above this
particular true old H[A] component, using the certified
literal printed finite Q_A. The pullback itself need NOT
be connected in its original signed A-edges. -/
noncomputable abbrev sourceLiteralY1SelectedLocalGOldPullback
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :=
  (sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root).pullbackQuotient
    (sourceLiteralY1X2AllLocalQuotient src dst A)

/-- At |A|=2, the true original H[A]-old component is
admissible. This is the genuine finite rank-two
admissibility base, not an ambient coset completion. -/
theorem sourceLiteralY1SelectedLocalHOld_admissible
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalHOldSkeleton
      src dst base A root).AdmissibleForCosetExtension :=
  (sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root)
    .admissible_of_card_le_two hcard.le

/-- All original and freshly completed signed H-local P_A
edges satisfy *weak* completeness, with exact proper-B
component tags. This is proved for the same literal
old skeleton, not merely for an unrelated catalogue. -/
theorem sourceLiteralY1SelectedLocalHOld_weakComplete
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root)
      .MultiCosetWeaklyComplete (allProperCosetFamily A)
      (sourceLiteralY1SelectedLocalHOld_admissible
        src dst base A hcard root)
      (sourceLiteralY1Local_isGenerated src dst A)
      (sourceLiteralY1Local_retractable src dst A hcard.le) := by
  exact allProperCosetFamily_weaklyComplete
    (sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root)
    (sourceLiteralY1SelectedLocalHOld_admissible
      src dst base A hcard root)
    (sourceLiteralY1Local_isGenerated src dst A)
    (sourceLiteralY1Local_retractable src dst A hcard.le)
    hcard.ge

/-- The true G[A]→H[A] labelled quotient is stable on EVERY
selected proper B⊊A (empty or singleton). It is NOT assumed
stable on all of A, where the rank-one hypothesis is insufficient. -/
theorem sourceLiteralY1SelectedLocalQuotient_properStable
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets) :
    (sourceLiteralY1X2AllLocalQuotient src dst A).StableAt B :=
  (sourceLiteralY1X2AllLocalQuotient_oneStable src dst A)
    B (rankTwoProper_card_le_one A B hcard
      ((allProperCosetFamily A).proper B hBP))

/-- The actual G[A] original-OLD pullback is admissible.
This is the corrected ABO Theorem 4.7(i) step with k=1:
ONLY proper-B stability is needed at a two-letter parent,
and the true old edge support is retained exactly. -/
theorem sourceLiteralY1SelectedLocalGOld_admissible
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).AdmissibleForCosetExtension := by
  exact
    (sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root)
      .pullbackQuotient_admissible_of_kStable
        (sourceLiteralY1X2AllLocalQuotient src dst A) 1
        (sourceLiteralY1X2AllLocalQuotient_oneStable src dst A)
        (by simp only [hcard]; omega)
        (sourceLiteralY1SelectedLocalHOld_admissible
          src dst base A hcard root)

/-- An explicitly selected TRUE OLD identity vertex in H[A].
It lies in the exact translated old root component, not
simply in the ambient group by fiat. -/
noncomputable def sourceLiteralY1SelectedLocalHOld_identity
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalHOldSkeleton
      src dst base A root).Vertex := by
  let K := (sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  obtain ⟨x, hx, _⟩ := K.intrinsicComponentLocal_identity_root A r
  exact ⟨1, by simpa only [← hx] using x.2⟩

@[simp] theorem sourceLiteralY1SelectedLocalHOld_identity_val
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalHOld_identity
      src dst base A root).1 = 1 :=
  rfl

/-- The G[A]-old PULLBACK contains its actual identity vertex
over the selected H[A] old root. This is the root of ONE
intrinsic signed old A-component; the total pullback may
contain many unrelated such components. -/
noncomputable def sourceLiteralY1SelectedLocalGOld_identity
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).Vertex := by
  have hmem : (1 : generatedSubgroup
      (sourceLiteralY1 src dst).transitionSubgroupGenerator A) ∈
      (sourceLiteralY1SelectedLocalHOldSkeleton
        src dst base A root).vertices :=
    (sourceLiteralY1SelectedLocalHOld_identity
      src dst base A root).2
  refine ⟨1, ?_⟩
  change (sourceLiteralY1X2AllLocalQuotient src dst A).hom
    (1 : generatedSubgroup (sourceLiteralY1X2AllGenerator src dst) A)
      ∈ (sourceLiteralY1SelectedLocalHOldSkeleton
          src dst base A root).vertices
  rw [map_one]
  exact hmem

@[simp] theorem sourceLiteralY1SelectedLocalGOld_identity_val
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalGOld_identity
      src dst base A root).1 = 1 :=
  rfl

/-- The EXACT weakly complete local H[A] stage for the
genuine printed root's old H-component. This is not
yet definitionally identified with the paper's
selected T(Y₁) tagged P_A stage. -/
noncomputable abbrev sourceLiteralY1SelectedLocalHCompleteStage
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :=
  (sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root)
    .weakMultiCosetCompletedStage
      (allProperCosetFamily A)
      (sourceLiteralY1SelectedLocalHOld_admissible
        src dst base A hcard root)
      (sourceLiteralY1Local_isGenerated src dst A)
      (sourceLiteralY1Local_retractable src dst A hcard.le)
      (sourceLiteralY1SelectedLocalHOld_weakComplete
        src dst base A hcard root)

/-- One precisely ROOT-NORMALIZED complete signed G[A]-Cayley
cover of the genuine old H[A] stage suffices to embed the
FULL attached fresh+old P_A region corresponding to ONE
intrinsic original G[A] old component.

ALL first-rank algebraic, admissibility and proper-support
stability hypotheses are discharged by the ACTUAL finite
printed source construction. The ONLY hypothesis left
here is F(1) being the exact tagged image of the chosen
true old identity G[A]-point in this same H-local stage.

Unlike the false global formulation, this concludes
Set.InjOn on the selected root's full multi-coset image,
NOT injectivity of the generally disconnected pullback's
whole multi-coset ambient coordinate map. -/
theorem sourceLiteralY1SelectedLocal_rootedMultiCoset_injOn_of_cover
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (F : LabelledGraphHom
      (cayleyGraph
        (trivialCompletionGenerator
          (sourceLiteralY1X2AllGenerator src dst) A)).toEGraph.toLabelledGraph
      (sourceLiteralY1SelectedLocalHCompleteStage
        src dst base A hcard root).toEGraph.toLabelledGraph)
    (hOne :
      F.onVertex (1 : generatedSubgroup
        (sourceLiteralY1X2AllGenerator src dst) A) =
      ((sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root)
        .pullbackOldToWeakMultiCosetStageHom
          (sourceLiteralY1X2AllLocalQuotient src dst A)
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalHOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1Local_isGenerated src dst A)
          (sourceLiteralY1Local_retractable src dst A hcard.le)
          (sourceLiteralY1SelectedLocalHOld_weakComplete
            src dst base A hcard root)
          ∅
          (empty_mem_allProperCosetFamily A
            (Finset.card_pos.mp (by rw [hcard]; decide))))
        .onVertex
          (sourceLiteralY1SelectedLocalGOld_identity
            src dst base A root)) :
    Set.InjOn
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetAmbientValue
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le))
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).rootedMultiCosetImage
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root)) := by
  let H := sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root
  let Q := sourceLiteralY1X2AllLocalQuotient src dst A
  let P := allProperCosetFamily A
  let hAdmH := sourceLiteralY1SelectedLocalHOld_admissible
    src dst base A hcard root
  let hGenH := sourceLiteralY1Local_isGenerated src dst A
  let hRetH := sourceLiteralY1Local_retractable src dst A hcard.le
  let hAdmG := sourceLiteralY1SelectedLocalGOld_admissible
    src dst base A hcard root
  let hGenG := sourceLiteralY1X2AllLocal_isGenerated src dst A
  let hRetG := sourceLiteralY1X2AllLocal_retractable src dst A hcard.le
  let hWeak := sourceLiteralY1SelectedLocalHOld_weakComplete
    src dst base A hcard root
  have hStable :
      ∀ B : Finset ι, B ∈ P.alphabets → Q.StableAt B := by
    intro B hBP
    exact sourceLiteralY1SelectedLocalQuotient_properStable
      src dst A hcard B hBP
  have hn : A.Nonempty := Finset.card_pos.mp (by rw [hcard]; decide)
  let hEmpty : (∅ : Finset ι) ∈ P.alphabets :=
    empty_mem_allProperCosetFamily A hn
  exact H.pullbackQuotient_rootedMultiCosetAmbient_injOn
    Q P hAdmH hGenH hRetH
    hAdmG hGenG hRetG hStable hWeak
    ∅ hEmpty F
    (sourceLiteralY1SelectedLocalGOld_identity
      src dst base A root)
    hOne

end ABO
end PSTSEPPA
