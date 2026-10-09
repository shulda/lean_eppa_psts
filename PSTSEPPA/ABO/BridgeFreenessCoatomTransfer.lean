import PSTSEPPA.ABO.BridgeFreenessInterface
import PSTSEPPA.ABO.CoatomFamilyPathEquivalence

/-!
# Bridge freeness is invariant under replacement by maximal cosets

The full proper-alphabet coset extension and the coatom-only extension
are canonically isomorphic as *tagged labelled graphs* for |A|>=2.
Both copies retain the same canonical morphism into the ambient Cayley
group, not merely an abstract graph isomorphism.

Consequently the two conditions of ABO Definition 4.1 are invariant:
(1) injectivity of the canonical ambient projection on vertices (and
hence, by determinism, on signed oriented edges);
(2) reflection inside the extension of every B-connection in the
ambient Cayley graph for B⊊A.

The second implication uses the certified reflection of ACTUAL
signed word paths through the coatom/full isomorphism. No global
ambient injectivity is assumed; it is exactly the bridge-freeness
hypothesis being transferred.

This lemma isolates a crucial interface of the forward/upward
inductive proof. It does not establish bridge freeness or the cluster
property for any particular skeleton.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The canonical inclusion of a selected family into a larger one
commutes with the ambient group projection on all quotient vertices,
including overlapping distinct intrinsic component tags. -/
theorem multiCosetFamilyVertexMap_ambient_value
    (P Q : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hPQ : P.alphabets ⊆ Q.alphabets)
    (u : K.MultiCosetVertex P hadm hgen hret) :
    K.multiCosetAmbientValue Q hadm hgen hret
      (K.multiCosetFamilyVertexMap P Q hadm hgen hret hPQ u) =
    K.multiCosetAmbientValue P hadm hgen hret u := by
  induction u using Quotient.inductionOn with
  | h raw =>
      rfl

/-- In particular the two isomorphic coatom/full presentations
give *identical* Cayley coordinates to corresponding vertices. -/
theorem coatomToFullCosetHom_ambient_value
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (u : K.MultiCosetVertex (coatomCosetFamily A)
      hadm hgen hret) :
    K.multiCosetAmbientValue (allProperCosetFamily A)
      hadm hgen hret
      ((K.coatomToFullCosetHom hadm hgen hret).onVertex u) =
    K.multiCosetAmbientValue (coatomCosetFamily A)
      hadm hgen hret u := by
  exact K.multiCosetFamilyVertexMap_ambient_value
    (coatomCosetFamily A) (allProperCosetFamily A)
    hadm hgen hret (coatomCosetFamily_subset_allProper A) u

/-- The source's exact bridge-freeness property holds for the
full proper-family extension iff it holds for the coatom-only
extension, for |A|≥2. The *same* ambient B-coset relation and
the same genuine signed-word path geometry are used on both sides.
This is an equivalence of independent INDuction hypotheses, not
a proof that either extension is automatically bridge-free. -/
theorem coatomCoset_bridgeFree_iff_allProper
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 2 ≤ A.card) :
    K.MultiCosetBridgeFree (coatomCosetFamily A)
      hadm hgen hret ↔
    K.MultiCosetBridgeFree (allProperCosetFamily A)
      hadm hgen hret := by
  let F := K.coatomToFullCosetHom hadm hgen hret
  have hamb :
      ∀ u : K.MultiCosetVertex (coatomCosetFamily A)
        hadm hgen hret,
        K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret (F.onVertex u) =
        K.multiCosetAmbientValue (coatomCosetFamily A)
          hadm hgen hret u := by
    intro u
    exact K.coatomToFullCosetHom_ambient_value hadm hgen hret u
  obtain ⟨⟨hvinj, hvsurj⟩, ⟨_, hesurj⟩⟩ :=
    K.coatomToFullCosetHom_bijective hadm hgen hret hAcard
  constructor
  · intro hBridgeCo
    constructor
    · intro x y hxy
      obtain ⟨u, rfl⟩ := hvsurj x
      obtain ⟨v, rfl⟩ := hvsurj y
      have hxyCo :
          K.multiCosetAmbientValue (coatomCosetFamily A)
            hadm hgen hret u =
          K.multiCosetAmbientValue (coatomCosetFamily A)
            hadm hgen hret v := by
        rw [← hamb u, ← hamb v]
        exact hxy
      exact congrArg F.onVertex (hBridgeCo.1 hxyCo)
    · intro B hBA x y hAmbient
      obtain ⟨u, rfl⟩ := hvsurj x
      obtain ⟨v, rfl⟩ := hvsurj y
      have hAmbientCo :
          K.multiCosetAmbientValue (coatomCosetFamily A)
            hadm hgen hret v ∈
          generatedLeftCoset gen B
            (K.multiCosetAmbientValue (coatomCosetFamily A)
              hadm hgen hret u) := by
        rw [← hamb u, ← hamb v]
        exact hAmbient
      obtain ⟨w, hw, hpath⟩ :=
        hBridgeCo.2 B hBA u v hAmbientCo
      exact ⟨w, hw, hpath.map F⟩
  · intro hBridgeFull
    constructor
    · intro u v huv
      apply hvinj
      apply hBridgeFull.1
      change
        K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret (F.onVertex u) =
        K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret (F.onVertex v)
      rw [hamb u, hamb v]
      exact huv
    · intro B hBA u v hAmbient
      have hAmbientFull :
          K.multiCosetAmbientValue (allProperCosetFamily A)
            hadm hgen hret (F.onVertex v) ∈
          generatedLeftCoset gen B
            (K.multiCosetAmbientValue (allProperCosetFamily A)
              hadm hgen hret (F.onVertex u)) := by
        rw [hamb u, hamb v]
        exact hAmbient
      obtain ⟨w, hw, hpath⟩ :=
        hBridgeFull.2 B hBA (F.onVertex u) (F.onVertex v)
          hAmbientFull
      exact ⟨w, hw,
        (K.coatomToFullCosetHom_follows_iff
          hadm hgen hret hAcard u v w).mpr hpath⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
