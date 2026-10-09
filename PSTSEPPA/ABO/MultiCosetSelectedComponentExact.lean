import PSTSEPPA.ABO.MultiCosetParentComponentExact
import PSTSEPPA.ABO.MultiCosetEGraph

/-!
# Exact intrinsic B-components at a selected full B-coset constituent

Unlike the earlier lower-family component theorem, here the full
multi-coset extension may contain constituents with alphabets D
that are not contained in B. The selected family P merely
has to contain B itself.

The key invariant is simple but important: the constituent
single-B extension is complete *on B-letters*. Whenever a B-labelled
edge leaves a point of its image inside the deterministic global
multi-coset EGraph, it must equal the image of the unique local
B-labelled edge. Therefore neither the intrinsic B-component
index nor membership in the selected full B-coset can change
along a realised B-word path.

Conversely every two points of the same tagged B-coset are
connected by genuine B-paths in that constituent, which map
to paths in the full multi-coset EGraph.

This proves the source-facing skeleton-meeting/full-B-coset
case of the component structure used in ABO Proposition 3.23,
even when other selected alphabets are *not* below B.
No global Cayley-map injectivity is used.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A B-labelled global edge leaving a selected tagged B-coset
point has its target in the *same* tagged B-coset. The proof
uses deterministic signed edges and the canonical inclusion
of the single-B EGraph into the multi-CE. -/
theorem multiCoset_selected_B_step_stays_in_coset
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : K.AttachedCosetVertex B)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret)
    (hsource :
      (K.multiCosetEGraph P hadm hgen hret).source e =
        K.multiCosetInclude P hadm hgen hret B hBP p)
    (hB :
      signedBase ((K.multiCosetEGraph P hadm hgen hret).label e) ∈ B) :
    ∃ q : K.AttachedCosetVertex B,
      q.1 = p.1 ∧
      (K.multiCosetEGraph P hadm hgen hret).target e =
        K.multiCosetInclude P hadm hgen hret B hBP q := by
  let G := K.multiCosetEGraph P hadm hgen hret
  let f := K.singleCosetToMultiHom P hadm hgen hret B hBP
  let s : {s : SignedLabel ι // signedBase s ∈ B} :=
    ⟨G.label e, hB⟩
  let eB : K.SingleCosetEdge B := Sum.inr (p, s)
  have hsrc :
      G.source (f.onEdge eB) =
        K.multiCosetInclude P hadm hgen hret B hBP p := by
    exact f.map_source eB
  have hlab : G.label (f.onEdge eB) = G.label e := by
    exact f.map_label eB
  have heq : e = f.onEdge eB :=
    G.deterministic (hsource.trans hsrc.symm) hlab.symm
  let q := (K.singleCosetEGraph B).target eB
  refine ⟨q, rfl, ?_⟩
  rw [heq]
  exact f.map_target eB

/-- Every actual B-path starting at a selected B-coset point
stays in that same component-tagged B-coset, even when the
global family also attaches incomparable alphabets. -/
theorem multiCoset_selected_B_path_stays_in_coset
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (w : LabelWord ι) :
    LabelWord.Uses B w →
    ∀ (p : K.AttachedCosetVertex B)
      (z : K.MultiCosetVertex P hadm hgen hret),
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret B hBP p)
        w z →
      ∃ q : K.AttachedCosetVertex B,
        q.1 = p.1 ∧
        z = K.multiCosetInclude P hadm hgen hret B hBP q := by
  let G := K.multiCosetEGraph P hadm hgen hret
  induction w with
  | nil =>
      intro _ p z hz
      have heq := G.follows_nil_iff.mp hz
      exact ⟨p, rfl, heq.symm⟩
  | cons s w ih =>
      intro hw p z hz
      cases hz with
      | cons e hsrc hl hrest =>
          have hlabel :
              signedBase ((K.multiCosetEGraph P hadm hgen hret).label e) ∈ B := by
            rw [hl]
            exact hw.1
          obtain ⟨q, hqidx, hqtarget⟩ :=
            K.multiCoset_selected_B_step_stays_in_coset
              P hadm hgen hret B hBP p e hsrc hlabel
          have hrest' : G.Follows
              (K.multiCosetInclude P hadm hgen hret B hBP q) w z := by
            rw [← hqtarget]
            exact hrest
          obtain ⟨r, hridx, hrz⟩ :=
            ih hw.2 q z hrest'
          exact ⟨r, hridx.trans hqidx, hrz⟩

/-- Intrinsic B-path reachability from a tagged B-coset point
in the *full* multi-CE is equivalent to membership in exactly
that same tagged B-coset. This does not assume every selected
alphabet is contained in B. -/
theorem multiCoset_selected_B_component_exact
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : K.AttachedCosetVertex B)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret B hBP p) w z) ↔
    ∃ q : K.AttachedCosetVertex B,
      q.1 = p.1 ∧
      z = K.multiCosetInclude P hadm hgen hret B hBP q := by
  constructor
  · rintro ⟨w, hw, hpz⟩
    exact K.multiCoset_selected_B_path_stays_in_coset
      P hadm hgen hret B hBP w hw p z hpz
  · rintro ⟨q, hidx, hq⟩
    obtain ⟨w, hw, hpath⟩ :=
      K.singleCosetEGraph_connected_on_index B p q hidx.symm
    have hmapped := hpath.map
      (K.singleCosetToMultiHom P hadm hgen hret B hBP)
    change (K.multiCosetEGraph P hadm hgen hret).Follows
      (K.multiCosetInclude P hadm hgen hret B hBP p) w
      (K.multiCosetInclude P hadm hgen hret B hBP q) at hmapped
    rw [hq]
    exact ⟨w, hw, hmapped⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
