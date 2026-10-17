import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalGlobalCayleySignedEmbedding
import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalSignedOffBReflection
import PSTSEPPA.ABO.SourceLiteralY1LocalHOffBPrintedType2Index
import PSTSEPPA.ABO.SourceLiteralY1X2AllType2DirectTransitionQuotient

/-!
# TRUE first-rank off-B point determines a based finite ORIGINAL type-(2) cover

The corrected ABO rank-one source is the actual finite
labelled group G=T(X₂^all) surjecting onto H=T(Y₁).
We have separately certified all of the following:
* the original SIGNED old+fresh G[A] P_A multiCE
  is embedded on ONE rooted A-component in the finite
  global G Cayley graph, without fictitious outside-A
  original edges;
* for each REAL old+fresh G[A] vertex z OFF the complete
  B-constituent, its genuine H[A] SIGNED quotient image
  remains off the H[A] B-constituent, using only 1-stability;
* normalization into the ORIGINAL printed T(Y₁) old
  root P_A quotient gives a literal component-tagged
  type-(2) augmented index (base,A,root,B,z_H);
* the whole ORIGINAL finite G=T(X₂^all) acts on EACH
  literal printed selected type-(2) augmented stage,
  with a labelled Cayley(G) cover BASED AT ANY global
  G group coordinate.

These ingredients now yield a CONCRETE TYPE-(2) STAGE
INDEX and a CONCRETE GLOBALLY SIGNED COVER based at
the actual group coordinate of ANY genuine selected
G[A] off-B vertex z. Its basepoint maps to EXACTLY
the OLD component-tagged printed H augmentation root,
not to a point identified only by its H group value.

This is the genuine source-based cover F needed by
the checked one-real-path type-(2) B-orbit detector.

The only remaining compatibility in that detector is
to compare the OLD printed augmentation root with the
source SIGNED original G[A]→printed-H old graph morphism
on that chosen G[A] vertex, then apply the 1-stable
global Q:G↠H using genuine signed rooted A-connectivity.

Neither entire old G pullback connectivity nor ambient
H quotient injectivity is assumed. No 4.7(iii), R8,
Condition 5.2, higher rank or PSTS EPPA conclusion yet.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Every genuine old/fresh G[A] off-B vertex has a
LITERAL indexed selected printed first-rank type-(2)
augmentation in the true finite X₂^all catalogue.
It retains the actual original input base, A, old H
root, proper B, and exact component-tagged off-B point. -/
noncomputable def sourceLiteralY1SelectedLocalGOffB_type2Index
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).MultiCosetVertex
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable
          src dst A hcard.le))
    (hOff : ¬ ∃ p : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetInclude
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le) B hBP p = z) :
    sourceLiteralY1Type2Index src dst :=
  ⟨base, ⟨⟨A, hcard⟩, ⟨root, ⟨⟨B, hBP⟩,
    sourceLiteralY1SelectedLocalGOffB_toPrintedType2
      src dst base A hcard root B hBP z hOff⟩⟩⟩⟩

/-- The REAL global finite G Cayley→literal PRINTED type-(2)
completed action based cover associated to any selected
G[A] off-B point, with its group-coordinate root taken from
the true original signed local→global Cayley morphism.

The initial OLD H augmentation vertex is the exact
component-tagged old indexed value of that same z. -/
noncomputable def sourceLiteralY1SelectedLocalGOffB_globalType2BasedHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).MultiCosetVertex
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable
          src dst A hcard.le))
    (hOff : ¬ ∃ p : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetInclude
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le) B hBP p = z) :
    LabelledGraphHom
      (cayleyGraph (sourceLiteralY1X2AllGenerator src dst)).toEGraph.toLabelledGraph
      ((sourceLiteralY1Type2ActionDatum src dst
        (sourceLiteralY1SelectedLocalGOffB_type2Index
          src dst base A hcard root B hBP z hOff)).stage).toEGraph.toLabelledGraph := by
  let j := sourceLiteralY1SelectedLocalGOffB_type2Index
    src dst base A hcard root B hBP z hOff
  let off := sourceLiteralY1SelectedLocalGOffB_toPrintedType2
    src dst base A hcard root B hBP z hOff
  let u : (sourceLiteralY1Type2ActionDatum src dst j).Carrier :=
    Sum.inl off.vertex
  exact sourceLiteralY1X2AllType2BasedAtHom
    src dst j u
    ((sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom
      src dst base A hcard root).onVertex z)

/-- The actual G-global group coordinate of EVERY selected
G[A] OFF-B vertex is mapped to exactly the genuine
ORIGINAL PRINTED OLD component-tagged H augmentation root
of its selected type-(2) stage.

This is a complete signed Cayley cover BASEPOINT identity,
not a hypothesis on all G group vertices or a collapse
of the original old H component labels. -/
theorem sourceLiteralY1SelectedLocalGOffB_globalType2BasedHom_oldRoot
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).MultiCosetVertex
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable
          src dst A hcard.le))
    (hOff : ¬ ∃ p : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetInclude
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le) B hBP p = z) :
    (sourceLiteralY1SelectedLocalGOffB_globalType2BasedHom
      src dst base A hcard root B hBP z hOff).onVertex
        ((sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom
          src dst base A hcard root).onVertex z) =
      Sum.inl
        (sourceLiteralY1SelectedLocalGOffB_toPrintedType2
          src dst base A hcard root B hBP z hOff).vertex := by
  change
    (sourceLiteralY1X2AllType2BasedAtHom
      src dst
      (sourceLiteralY1SelectedLocalGOffB_type2Index
        src dst base A hcard root B hBP z hOff)
      (Sum.inl
        (sourceLiteralY1SelectedLocalGOffB_toPrintedType2
          src dst base A hcard root B hBP z hOff).vertex)
      ((sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom
        src dst base A hcard root).onVertex z)).onVertex
      ((sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom
        src dst base A hcard root).onVertex z) = _
  exact sourceLiteralY1X2AllType2BasedAtHom_base
    src dst
    (sourceLiteralY1SelectedLocalGOffB_type2Index
      src dst base A hcard root B hBP z hOff)
    (Sum.inl
      (sourceLiteralY1SelectedLocalGOffB_toPrintedType2
        src dst base A hcard root B hBP z hOff).vertex)
    ((sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom
      src dst base A hcard root).onVertex z)

end ABO
end PSTSEPPA
