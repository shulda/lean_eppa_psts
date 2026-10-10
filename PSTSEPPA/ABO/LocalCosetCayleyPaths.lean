import PSTSEPPA.ABO.LocalCosetCayleySlice
import PSTSEPPA.ABO.ComponentSubgraphPaths

/-!
# Exact signed-path reflection for genuine local Cayley coset slices

The previous module constructs a full literal A-coset slice of a
possibly incomplete Γ-Cayley skeleton K as a skeleton over the actual
local group Γ[A], embedded back into K by left translation.

An injective labelled morphism alone only PRESERVES paths. To use
this construction in corrected ABO's component/cluster induction,
we must also REFLECT every actually realised signed path.

We prove:
* every K-edge starting in the translated A-coset has a genuine
  unique corresponding local directed signed edge (not an imagined
  completion edge);
* every K-path starting inside the translated A-coset lifts to an
  actual local path with EXACTLY the same sequence of signed labels;
* hence between the image of any two local vertices, Follows is
  equivalent in the local slice and the original incomplete K;
* the equivalence also holds for intrinsic reachability restricted
  to ANY alphabet C, including C not contained in A.

The proof uses only the original K's A-edge restriction; no global
retractability, closure of missing edges or ambient path completion
is smuggled in. This is the path-exact strengthening of #315
needed for source-faithful local component geometry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every actual signed original edge whose source lies in
g·Γ[A] has an actual LOCAL edge lifting to the same oriented
edge token; conversely any local edge stays in that coset. -/
theorem leftCosetSliceHom_edge_range_iff (g : Γ) (e : K.Edge) :
    (∃ f : (K.leftCosetSlice g).Edge,
      (K.leftCosetSliceHom g).onEdge f = e) ↔
    ((K.toEGraph).source e).1 ∈ generatedLeftCoset gen A g := by
  constructor
  · rintro ⟨f, hf⟩
    have hs := (K.leftCosetSliceHom g).map_source f
    rw [hf] at hs
    apply (K.leftCosetSliceHom_vertex_range_iff g
      ((K.toEGraph).source e)).mp
    exact ⟨((K.leftCosetSlice g).toEGraph).source f, hs.symm⟩
  · intro he
    change g⁻¹ * e.1.1 ∈ generatedSubgroup gen A at he
    let t : generatedSubgroup gen A := ⟨g⁻¹ * e.1.1, he⟩
    have htEq : g * (t : Γ) = e.1.1 := by
      simp [t]
    have htEdge : (t, e.1.2) ∈ (K.leftCosetSlice g).edges := by
      change (g * (t : Γ), e.1.2) ∈ K.edges
      rw [htEq]
      exact e.2
    refine ⟨⟨(t, e.1.2), htEdge⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact htEq
    · rfl

/-- Choose the literal local representative of a vertex of K
known to lie in g·Γ[A]. Injectivity makes its value unique;
the noncomputable choice is only for its proof witness. -/
noncomputable def leftCosetSliceLiftVertex
    (g : Γ) (x : K.Vertex)
    (hx : x.1 ∈ generatedLeftCoset gen A g) :
    (K.leftCosetSlice g).Vertex :=
  Classical.choose ((K.leftCosetSliceHom_vertex_range_iff g x).mpr hx)

/-- A lifted local vertex maps to the EXACT old vertex. -/
@[simp]
theorem leftCosetSliceHom_liftVertex
    (g : Γ) (x : K.Vertex)
    (hx : x.1 ∈ generatedLeftCoset gen A g) :
    (K.leftCosetSliceHom g).onVertex
      (K.leftCosetSliceLiftVertex g x hx) = x :=
  Classical.choose_spec ((K.leftCosetSliceHom_vertex_range_iff g x).mpr hx)

/-- Every real original signed path starting at a vertex of
g·Γ[A] lifts to a REAL path in the full local slice.
The word w is not modified, even for inverse letters or loops.
In particular its endpoint automatically remains in g·Γ[A]. -/
theorem leftCosetSlice_follows_lift
    (g : Γ)
    {u v : K.Vertex} {w : LabelWord ι}
    (hp : (K.toEGraph).Follows u w v)
    (hu : u.1 ∈ generatedLeftCoset gen A g) :
    ∃ hv : v.1 ∈ generatedLeftCoset gen A g,
      ((K.leftCosetSlice g).toEGraph).Follows
        (K.leftCosetSliceLiftVertex g u hu) w
        (K.leftCosetSliceLiftVertex g v hv) := by
  induction hp with
  | nil u =>
      exact ⟨hu, EGraph.Follows.nil _⟩
  | @cons u v s w e hs hl hrest ih =>
      have hsrc :
          ((K.toEGraph).source e).1 ∈ generatedLeftCoset gen A g := by
        rw [hs]
        exact hu
      obtain ⟨f, hf⟩ :=
        (K.leftCosetSliceHom_edge_range_iff g e).mpr hsrc
      have htargetMap :
          (K.leftCosetSliceHom g).onVertex
            (((K.leftCosetSlice g).toEGraph).target f) =
              (K.toEGraph).target e := by
        calc
          (K.leftCosetSliceHom g).onVertex
              (((K.leftCosetSlice g).toEGraph).target f) =
              (K.toEGraph).target ((K.leftCosetSliceHom g).onEdge f) :=
            ((K.leftCosetSliceHom g).map_target f).symm
          _ = (K.toEGraph).target e := by rw [hf]
      have htgt :
          ((K.toEGraph).target e).1 ∈ generatedLeftCoset gen A g :=
        (K.leftCosetSliceHom_vertex_range_iff g
          ((K.toEGraph).target e)).mp
          ⟨((K.leftCosetSlice g).toEGraph).target f, htargetMap⟩
      obtain ⟨hv, hrestLift⟩ := ih htgt
      have hsource :
          ((K.leftCosetSlice g).toEGraph).source f =
            K.leftCosetSliceLiftVertex g u hu := by
        apply K.leftCosetSliceHom_vertex_injective g
        calc
          (K.leftCosetSliceHom g).onVertex
              (((K.leftCosetSlice g).toEGraph).source f) =
              (K.toEGraph).source ((K.leftCosetSliceHom g).onEdge f) :=
            ((K.leftCosetSliceHom g).map_source f).symm
          _ = (K.toEGraph).source e := by rw [hf]
          _ = u := hs
          _ = (K.leftCosetSliceHom g).onVertex
              (K.leftCosetSliceLiftVertex g u hu) :=
            (K.leftCosetSliceHom_liftVertex g u hu).symm
      have htarget :
          ((K.leftCosetSlice g).toEGraph).target f =
            K.leftCosetSliceLiftVertex g ((K.toEGraph).target e) htgt := by
        apply K.leftCosetSliceHom_vertex_injective g
        calc
          (K.leftCosetSliceHom g).onVertex
              (((K.leftCosetSlice g).toEGraph).target f) =
              (K.toEGraph).target e := htargetMap
          _ = (K.leftCosetSliceHom g).onVertex
              (K.leftCosetSliceLiftVertex g ((K.toEGraph).target e) htgt) :=
            (K.leftCosetSliceHom_liftVertex g _ htgt).symm
      have hlabel :
          ((K.leftCosetSlice g).toEGraph).label f = s := by
        calc
          ((K.leftCosetSlice g).toEGraph).label f =
              (K.toEGraph).label ((K.leftCosetSliceHom g).onEdge f) :=
            ((K.leftCosetSliceHom g).map_label f).symm
          _ = (K.toEGraph).label e := by rw [hf]
          _ = s := hl
      refine ⟨hv, EGraph.Follows.cons f hsource hlabel ?_⟩
      rw [htarget]
      exact hrestLift

/-- EXACT correspondence of all labelled paths between any two
vertices of one true local slice, not only ambient-coset containment.
The forward implication is morphism naturality; the reverse is
proved by lifting each actual original signed edge. -/
theorem leftCosetSlice_follows_iff
    (g : Γ) (x y : (K.leftCosetSlice g).Vertex)
    (w : LabelWord ι) :
    ((K.leftCosetSlice g).toEGraph).Follows x w y ↔
      (K.toEGraph).Follows
        ((K.leftCosetSliceHom g).onVertex x)
        w
        ((K.leftCosetSliceHom g).onVertex y) := by
  constructor
  · intro hp
    exact hp.map (K.leftCosetSliceHom g)
  · intro hp
    have hx :
        ((K.leftCosetSliceHom g).onVertex x).1 ∈
          generatedLeftCoset gen A g :=
      (K.leftCosetSliceHom_vertex_range_iff g _).mp ⟨x, rfl⟩
    obtain ⟨hy, hLift⟩ := K.leftCosetSlice_follows_lift g hp hx
    have hxEq :
        K.leftCosetSliceLiftVertex g
          ((K.leftCosetSliceHom g).onVertex x) hx = x := by
      apply K.leftCosetSliceHom_vertex_injective g
      rw [K.leftCosetSliceHom_liftVertex]
    have hyEq :
        K.leftCosetSliceLiftVertex g
          ((K.leftCosetSliceHom g).onVertex y) hy = y := by
      apply K.leftCosetSliceHom_vertex_injective g
      rw [K.leftCosetSliceHom_liftVertex]
    simpa only [hxEq, hyEq] using hLift

/-- In particular the local and original INTRINSIC C-components
agree exactly under the slice embedding, for arbitrary C.
No subalphabet-coset surrogate is substituted for real paths. -/
theorem leftCosetSlice_subalphabetReachable_iff
    (g : Γ) (C : Finset ι)
    (x y : (K.leftCosetSlice g).Vertex) :
    (K.leftCosetSlice g).SubalphabetReachable C x y ↔
      K.SubalphabetReachable C
        ((K.leftCosetSliceHom g).onVertex x)
        ((K.leftCosetSliceHom g).onVertex y) := by
  constructor
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw, (K.leftCosetSlice_follows_iff g x y w).mp hp⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw, (K.leftCosetSlice_follows_iff g x y w).mpr hp⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
