import PSTSEPPA.ABO.IsolatedCosetGluing
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Old B-components cannot enter an isolated full B-coset attachment

The rank-two type-(2) singleton augmentation attaches a fresh full B-coset
to an old EGraph at a root with no pre-existing signed B-edges.

The missing-edge condition has two distinct consequences. By formal edge
inversion, NO old B-edge can even ENTER the root. Thus a genuine old B-path
starting away from the root remains away from it. Furthermore every new
B-edge of the attached coset has its source either at the root or at a
fresh tagged coset vertex. A B-path from another old vertex therefore
cannot use a new edge. We certify these exact path statements without
assuming any completeness of the original graph or group faithfulness.

Together with the already-certified attached-coset word kernel, this
separates the last old-vertex obligation in the rank-one R2 proof.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- An old B-labelled edge cannot ENTER the attachment root:
otherwise its formal inverse is an old B-edge leaving the root,
contradicting the exact signed missing-edge hypothesis. -/
theorem old_B_edge_target_ne_root
    (G : EGraph V OldEdge ι)
    (B : Finset ι) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (e : OldEdge)
    (hB : signedBase (G.label e) ∈ B) :
    G.target e ≠ root := by
  intro he
  have hsource_inv : G.source (G.inv e) = root := he
  have hlabel_inv : signedBase (G.label (G.inv e)) ∈ B := by
    rw [G.toLabelledGraph.label_inv_eq]
    simpa only [signedBase_inv] using hB
  exact hMissing (G.inv e) hsource_inv hlabel_inv

/-- A genuine old B-path starting at an old point other than the
attachment root cannot reach the root (or visit it midway). -/
theorem old_B_path_avoids_root
    (G : EGraph V OldEdge ι)
    (B : Finset ι) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (x y : V) (w : LabelWord ι)
    (hw : LabelWord.Uses B w)
    (hne : x ≠ root)
    (hpath : G.Follows x w y) :
    y ≠ root := by
  induction w generalizing x with
  | nil =>
      have hxy : x = y := G.follows_nil_iff.mp hpath
      exact fun hy => hne (hxy.trans hy)
  | cons s w ih =>
      cases hpath with
      | cons e hsrc hlab htail =>
          have hB : signedBase (G.label e) ∈ B := by
            rw [hlab]
            exact hw.1
          exact ih hw.2 (G.old_B_edge_target_ne_root B root
            hMissing e hB) htail

/-- A glued B-edge whose source is an old vertex away from
the root must literally be an original B-edge. Its target
also remains an old vertex away from the root. -/
theorem glued_B_edge_from_old_ne_root
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root x : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hne : x ≠ root)
    (e : Edge OldEdge gen B g)
    (hsource :
      (gluedEGraph G gen B g root hMissing).source e =
        (Sum.inl x : Vertex V gen B g))
    (hB :
      signedBase ((gluedEGraph G gen B g root hMissing).label e) ∈ B) :
    ∃ f : OldEdge, e = Sum.inl f ∧
      G.source f = x ∧ G.target f ≠ root := by
  cases e with
  | inl f =>
      have hsrc : G.source f = x := Sum.inl.inj hsource
      have hlabel : signedBase (G.label f) ∈ B := hB
      exact ⟨f, rfl, hsrc,
        G.old_B_edge_target_ne_root B root hMissing f hlabel⟩
  | inr f =>
      have hr : x = root :=
        gluePoint_inl_eq_root gen B g root x
          ⟨(cayleyGraph gen).source f.1, f.2.1⟩ hsource
      exact False.elim (hne hr)

/-- Every B-path in the glued graph starting at an old
vertex away from the root uses ONLY old edges, stays
away from the root, and ends at an old vertex. -/
theorem glued_B_path_from_old_ne_root_reflect
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (x : V) (hne : x ≠ root)
    (z : Vertex V gen B g)
    (w : LabelWord ι)
    (hw : LabelWord.Uses B w)
    (hpath :
      (gluedEGraph G gen B g root hMissing).Follows
        (Sum.inl x) w z) :
    ∃ y : V, y ≠ root ∧ z = Sum.inl y ∧ G.Follows x w y := by
  let H := gluedEGraph G gen B g root hMissing
  induction w generalizing x z with
  | nil =>
      have hz : (Sum.inl x : Vertex V gen B g) = z :=
        H.follows_nil_iff.mp hpath
      subst z
      exact ⟨x, hne, rfl, EGraph.Follows.nil x⟩
  | cons s w ih =>
      cases hpath with
      | cons e hsrc hlab hrest =>
          have heB : signedBase (H.label e) ∈ B := by
            rw [hlab]
            exact hw.1
          obtain ⟨f, hEq, hSource, hTarget⟩ :=
            glued_B_edge_from_old_ne_root G gen B g root x
              hMissing hne e hsrc heB
          subst e
          have htail :
              H.Follows (Sum.inl (G.target f)) w z := hrest
          obtain ⟨y, hyroot, hz, hp⟩ :=
            ih hw.2 hTarget htail
          refine ⟨y, hyroot, hz, ?_⟩
          exact EGraph.Follows.cons f hSource hlab hp

/-- Old-vertex B-reachability away from the attachment root
is exactly the original B-reachability. The augmented
full B-coset adds no shortcuts among these old vertices. -/
theorem glued_B_reachable_old_ne_root_iff
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (x y : V) (hne : x ≠ root) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (gluedEGraph G gen B g root hMissing).Follows
        (Sum.inl x) w (Sum.inl y)) ↔
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      G.Follows x w y) := by
  constructor
  · rintro ⟨w, hw, hp⟩
    obtain ⟨z, _, hz, hOld⟩ :=
      glued_B_path_from_old_ne_root_reflect
        G gen B g root hMissing x hne (Sum.inl y) w hw hp
    have hyz : y = z := Sum.inl.inj hz
    subst z
    exact ⟨w, hw, hOld⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw, hp.map (oldHom G gen B g root hMissing)⟩

end IsolatedCosetGluing
end ABO
end PSTSEPPA
