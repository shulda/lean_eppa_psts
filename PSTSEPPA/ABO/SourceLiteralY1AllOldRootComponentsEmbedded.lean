import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalRootedAmbientEmbedding
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootNormalizedLocalHFullCayleyCover
import PSTSEPPA.ABO.SelectedOldComponentMultiCosetAmbientEmbedding
import PSTSEPPA.ABO.CayleyLeftTranslations

/-!
# Genuine first-rank ORIGINAL rooted ambient embedding for EVERY old A-component

The existing checked first-rank source-local result embeds the
complete old+fresh attached P_A region based at the original
G[A]-pullback IDENTITY. The true old G[A] pullback of a single
original incomplete H[A] A-component may have SEVERAL
distinct signed A-components, hence identity-rooted
embeddedness does not automatically cover all of them.

However the actual first-rank source has more than an
identity-rooted signed stage cover: it has a SURJECTIVE
full labelled Cayley(G[A])→the EXACT normalized completed
old H[A] P_A stage morphism, on ALL genuine vertices
and oriented signed edges.

For ANY original old pullback vertex r, its exact H-old
tagged point in the completed stage therefore has a
genuine Cayley preimage g. Left translating the Cayley
cover by g gives a signed morphism based at r's EXACT
old H point. The independently certified general
component-scoped collision theorem applies with THIS
root r, without supposing that r is G[A]'s identity.

The result: for EVERY original old G[A] A-component,
the whole selected old+fresh properly tagged attached
P_A region is individually ambient-coordinate embedded.

This is a strict mathematical strengthening of the
first-rank corrected 4.7(ii) source result, but NOT
a claim of simultaneous injectivity of the whole
DISCONNECTED original G[A] pullback: different A-
components might still have colliding ambient G[A]
coordinates with genuinely different original tags.

The argument is entirely in the real source G=T(X₂^all)
and H=T(Y₁), with the proper-B one-stable quotient,
original incomplete signed old edges, TRUE locally
retractable G[A], H[A], and legal original source stage
completion. No new axioms, fictitious old edges,
arbitrary A-stability, R8, full 4.7(iii), higher rank
or final finite PSTS EPPA are involved.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- An actual vertex-SURJECTIVE Cayley(G) cover of the
LEGALLY completed H multiCE is enough to embed the entire
old+fresh G attached region above EVERY one selected
ORIGINAL old G A-component, based at ANY old pullback
vertex r. The cover need not come with a predefined
old root, because vertex surjectivity supplies exactly
the one needed for r and true Cayley left translation
preserves all formal signed edges and labels.

No total G multiCE ambient injectivity is concluded. -/
theorem pullbackQuotient_allRoots_rootedMultiCosetAmbient_injOn
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hStable : ∀ B : Finset ι, B ∈ P.alphabets → Q.StableAt B)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage
        P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (hSurj : Function.Surjective F.onVertex)
    (root : (K.pullbackQuotient Q).Vertex) :
    Set.InjOn
      ((K.pullbackQuotient Q).multiCosetAmbientValue
        P hAdmG hGenG hRetG)
      ((K.pullbackQuotient Q).rootedMultiCosetImage
        P hAdmG hGenG hRetG root) := by
  obtain ⟨g, hg⟩ := hSurj
    ((K.pullbackOldToWeakMultiCosetStageHom
      Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex root)
  let Fg := F.comp (cayleyLeftTranslateHom genΓ g)
  have hOne :
      Fg.onVertex (1 : Γ) =
        (K.pullbackOldToWeakMultiCosetStageHom
          Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex root := by
    change F.onVertex (g * 1) = _
    simpa using hg
  exact K.pullbackQuotient_rootedMultiCosetAmbient_injOn
    Q P hAdmH hGenH hRetH hAdmG hGenG hRetG
    hStable hweak B₀ hB₀ Fg root hOne

end CayleySubgraphSpec

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the EXACT finite first-rank original T(X₂^all)
to T(Y₁) signed old-input construction, the entire
original multiCE region selected from ANY genuinely
existing G[A] old vertex is embedded in local G[A].

The earlier identity-root theorem is one special case.
The genuine original G[A] Q_A old pullback itself
may be disconnected and no cross-component collision
claim is made. -/
theorem sourceLiteralY1SelectedLocal_everyOldRoot_rootedMultiCoset_injOn
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (r : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).Vertex) :
    Set.InjOn
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetAmbientValue
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable
          src dst A hcard.le))
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).rootedMultiCosetImage
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable
          src dst A hcard.le) r) := by
  let H := sourceLiteralY1SelectedLocalHOldSkeleton
    src dst base A root
  let Q := sourceLiteralY1X2AllLocalQuotient src dst A
  let P := allProperCosetFamily A
  let hAdmH := sourceLiteralY1SelectedLocalHOld_admissible
    src dst base A hcard root
  let hGenH := sourceLiteralY1Local_isGenerated src dst A
  let hRetH := sourceLiteralY1Local_retractable src dst A hcard.le
  let hAdmG := sourceLiteralY1SelectedLocalGOld_admissible
    src dst base A hcard root
  let hGenG := sourceLiteralY1X2AllLocal_isGenerated src dst A
  let hRetG := sourceLiteralY1X2AllLocal_retractable
    src dst A hcard.le
  let hweak := sourceLiteralY1SelectedLocalHOld_weakComplete
    src dst base A hcard root
  have hStable : ∀ B : Finset ι, B ∈ P.alphabets → Q.StableAt B := by
    intro B hBP
    exact sourceLiteralY1SelectedLocalQuotient_properStable
      src dst A hcard B hBP
  have hApos : A.Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; decide)
  let hEmpty : (∅ : Finset ι) ∈ P.alphabets :=
    empty_mem_allProperCosetFamily A hApos
  let F := sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom
    src dst base A hcard root
  have hSurj : Function.Surjective F.onVertex :=
    sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom_vertex_surjective
      src dst base A hcard root
  exact H.pullbackQuotient_allRoots_rootedMultiCosetAmbient_injOn
    Q P hAdmH hGenH hRetH hAdmG hGenG hRetG
    hStable hweak ∅ hEmpty F hSurj r

end ABO
end PSTSEPPA
