/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz.
Portions Copyright (c) 2026 Daniel Lyng.
The finite reindexing and padding arguments adapt Daniel Lyng's
Econlib Math/Analysis/ConvexReduction.lean and Persuasion/Finite/Caratheodory.lean
at 003655ccf010cdf44c4f67d6675167b54ce0e9df (Apache-2.0).
Released under Apache 2.0.
-/
module

public import BayesianPersuasion.Primitives
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic

@[expose] public section

open Set Finset
namespace BayesianPersuasion.Proof

instance belief_compact (ι : Type*) [Fintype ι] : CompactSpace (Belief ι) :=
  isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ ι)

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem convexHull_finite_support {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) :
    ∃ (k : ℕ) (_ : k ≤ Module.finrank ℝ E + 1) (z : Fin k → E) (w : Belief (Fin k)),
      (∀ j, z j ∈ s) ∧ ∑ j, w.val j • z j = x := by
  obtain ⟨ι, hι, z, w, hz, hi, hw, hsum, hbar⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    hi.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, hcard, z ∘ e,
    ⟨w ∘ e, fun j => (hw (e j)).le, ?_⟩, fun j => hz ⟨e j, rfl⟩, ?_⟩
  · exact (e.sum_comp w).trans hsum
  · exact (e.sum_comp (fun j => w j • z j)).trans hbar

/-- Summation is unaffected by padding with zero coefficients. -/
theorem sum_pad {k N : ℕ} (hk : k ≤ N) {G : Type*} [AddCommMonoid G]
    (f : Fin k → G) :
    (∑ j : Fin N, if h : j.val < k then f ⟨j.val, h⟩ else 0) = ∑ j, f j := by
  classical
  symm
  refine @Finset.sum_of_injOn (Fin k) (Fin N) G _ univ univ f
    (fun j => if h : j.val < k then f ⟨j.val, h⟩ else 0)
    (fun j : Fin k => (⟨j.val, lt_of_lt_of_le j.isLt hk⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro j₁ _ j₂ _ h; exact Fin.ext (Fin.mk.inj h)
  · intro _ _; simp
  · intro j _ hj
    have h : ¬ (j.val < k) := by
      intro hlt; apply hj; exact ⟨⟨j.val, hlt⟩, by simp, Fin.ext rfl⟩
    exact dite_eq_right h
  · intro j _; simp only [dite_eq_left j.isLt]

theorem convexHull_fixed_support {s : Set E} (hs : s.Nonempty) {x : E}
    (hx : x ∈ convexHull ℝ s) :
    ∃ (w : Belief (Fin (Module.finrank ℝ E + 1)))
      (z : Fin (Module.finrank ℝ E + 1) → s), ∑ j, w.val j • (z j).val = x := by
  classical
  obtain ⟨z₀, hz₀⟩ := hs
  obtain ⟨k, hk, z, w, hz, hbar⟩ := convexHull_finite_support hx
  let wp : Fin (Module.finrank ℝ E + 1) → ℝ :=
    fun j => if h : j.val < k then w.val ⟨j.val, h⟩ else 0
  let zp : Fin (Module.finrank ℝ E + 1) → s :=
    fun j => if h : j.val < k then ⟨z ⟨j.val, h⟩, hz _⟩ else ⟨z₀, hz₀⟩
  have hw : (∀ j, 0 ≤ wp j) ∧ ∑ j, wp j = 1 := by
    constructor
    · intro j; dsimp [wp]; split_ifs <;> simp_all [w.property.1]
    · exact (sum_pad hk w.val).trans w.property.2
  refine ⟨⟨wp, hw⟩, zp, ?_⟩
  have hterm : ∀ j, wp j • (zp j).val =
      if h : j.val < k then w.val ⟨j.val, h⟩ • z ⟨j.val, h⟩ else 0 := by
    intro j; dsimp [wp, zp]; split_ifs <;> simp
  simp_rw [hterm]
  exact (sum_pad hk (fun j => w.val j • z j)).trans hbar

variable [TopologicalSpace E] [T2Space E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- Compact subsets of a finite dimensional real space have compact convex hull. -/
theorem compact_convexHull {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  by_cases hne : s.Nonempty
  · letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
    let F : Belief (Fin (Module.finrank ℝ E + 1)) ×
        (Fin (Module.finrank ℝ E + 1) → s) → E := fun t => ∑ j, t.1.val j • (t.2 j).val
    have hF : Continuous F := by
      unfold F
      exact continuous_finsetSum _ fun j _ =>
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd))
    have heq : convexHull ℝ s = Set.range F := by
      ext x
      constructor
      · intro hx
        obtain ⟨w, z, hz⟩ := convexHull_fixed_support hne hx
        exact ⟨(w, z), hz⟩
      · rintro ⟨⟨w, z⟩, rfl⟩
        exact mem_convexHull_of_exists_fintype w.val (fun j => (z j).val)
          w.property.1 w.property.2 (fun j => (z j).property) rfl
    rw [heq]
    exact isCompact_range hF
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, convexHull_empty]
    exact isCompact_empty

end BayesianPersuasion.Proof
