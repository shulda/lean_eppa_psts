import PSTSEPPA.ABO.MultiCosetMaximalConstituentExit
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact

/-!
# Rank drop witnessed *inside* a maximal constituent when a B-path exits

This is the full path-level boundary statement needed at the start of
the source ABO Lemma 4.3. The previous module isolates the exact
strictly smaller tagged support at one crossing edge. Here we
locate the FIRST exit along a genuine signed B-word path.

Fix a particular tagged full C-coset (not merely the union
of all C-constituents). If a realised B-path begins in
that copy and ends outside it, a vertex x on a B-prefix
of the path is:
  * still in the SAME tagged C-copy;
  * supported by a proper D⊊C; and
  * reached by an actual B-path from the initial point.

The copy-tag condition is essential: different C-component
tags can have the same ambient Cayley coordinates, and a path
could move between different C-copies without ever leaving
the union of all C-supported vertices.

This is an unconditional rank-decreasing *boundary witness*.
It does not construct a common core for the whole B-component,
and makes no assumption of bridge-freeness or the cluster property.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If an actual B-word path from a selected maximal C-copy
leaves that exact tagged copy, a point of its boundary still
inside the copy has tagged support over some strict D⊊C.

This is valid at arbitrary |A|, subject only to the explicit
maximality/nonemptiness hypothesis on C. -/
theorem allProperCoset_maximal_constituent_path_exit_lower
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCnonempty : C.Nonempty)
    (hMax :
      ∀ (E : Finset ι)
        (hEP : E ∈ (allProperCosetFamily A).alphabets),
        C ⊆ E → E = C)
    (p : K.AttachedCosetVertex C)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hOutsideCopy :
      ¬ ∃ q : K.AttachedCosetVertex C,
        q.1 = p.1 ∧
        y = K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP q)
    (hPath :
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          (K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP p) w y) :
    ∃ x : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret,
      (∃ q : K.AttachedCosetVertex C,
        q.1 = p.1 ∧
        x = K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP q) ∧
      (∃ u : LabelWord ι, LabelWord.Uses B u ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          (K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP p) u x) ∧
      ∃ D : Finset ι,
        D ⊂ C ∧
        K.MultiCosetVertexSupported (allProperCosetFamily A)
          hadm hgen hret D x := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let S : K.MultiCosetVertex P hadm hgen hret → Prop :=
    fun x => ∃ q : K.AttachedCosetVertex C,
      q.1 = p.1 ∧
      x = K.multiCosetInclude P hadm hgen hret C hCP q

  have hExitStep :
      ∀ (e : K.MultiCosetEdgeVertexIncidenceQuotient
        P hadm hgen hret),
        S (G.source e) → ¬ S (G.target e) →
        ∃ D : Finset ι,
          D ⊂ C ∧
          K.MultiCosetVertexSupported
            P hadm hgen hret D (G.source e) := by
    intro e hs ht
    have hOutside : signedBase (G.label e) ∉ C := by
      intro hl
      obtain ⟨q, hqidx, hq⟩ := hs
      obtain ⟨r, hridx, hr⟩ :=
        K.multiCoset_selected_B_step_stays_in_coset
          P hadm hgen hret C hCP q e hq hl
      exact ht ⟨r, hridx.trans hqidx, hr⟩
    have hSourceC :
        K.MultiCosetVertexSupported P hadm hgen hret
          C (G.source e) := by
      obtain ⟨q, _, hq⟩ := hs
      exact ⟨hCP, q, hq.symm⟩
    exact K.allProperCoset_maximal_support_exit_label_lower
      hadm hgen hret C hCP hCnonempty hMax
      e hSourceC hOutside

  have hAux :
      ∀ (w : LabelWord ι)
        (u v : K.MultiCosetVertex P hadm hgen hret),
        LabelWord.Uses B w →
        G.Follows u w v →
        S u → ¬ S v →
        ∃ x : K.MultiCosetVertex P hadm hgen hret,
          S x ∧
          (∃ prefix : LabelWord ι,
            LabelWord.Uses B prefix ∧ G.Follows u prefix x) ∧
          ∃ D : Finset ι,
            D ⊂ C ∧
            K.MultiCosetVertexSupported
              P hadm hgen hret D x := by
    intro w
    induction w with
    | nil =>
        intro u v _ hp hu hv
        have huv : u = v := G.follows_nil_iff.mp hp
        subst v
        exact False.elim (hv hu)
    | cons s rest ih =>
        intro u v hw hp hu hv
        cases hp with
        | cons e hsrc hl hrest =>
            by_cases hTarget : S (G.target e)
            · obtain ⟨x, hx, ⟨prefix, hPrefix, hPrefixPath⟩,
                  D, hD, hSupp⟩ :=
                ih (G.target e) v hw.2 hrest hTarget hv
              refine ⟨x, hx, ⟨s :: prefix, ?_, ?_⟩,
                D, hD, hSupp⟩
              · exact ⟨hw.1, hPrefix⟩
              · exact EGraph.Follows.cons e hsrc hl hPrefixPath
            · have hSource : S (G.source e) := by
                rw [hsrc]
                exact hu
              obtain ⟨D, hD, hSupp⟩ := hExitStep e hSource hTarget
              refine ⟨u, hu,
                ⟨[], LabelWord.uses_nil B,
                  G.follows_nil_iff.mpr rfl⟩,
                D, hD, ?_⟩
              rw [hsrc] at hSupp
              exact hSupp

  obtain ⟨w, hw, hp⟩ := hPath
  have hStart :
      S (K.multiCosetInclude P hadm hgen hret C hCP p) :=
    ⟨p, rfl, rfl⟩
  exact hAux w
    (K.multiCosetInclude P hadm hgen hret C hCP p)
    y hw hp hStart hOutsideCopy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
