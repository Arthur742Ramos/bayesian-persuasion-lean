module

public import BayesianPersuasion.Signals
public import BayesianPersuasion.CompactHull
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

universe uΩ uA

open Set Finset
namespace BayesianPersuasion

variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]

def probabilitySimplex (Ω : Type uΩ) [Fintype Ω] : Set (Ω → ℝ) :=
  {p | (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1}

/-- Belief and sender-payoff pairs from receiver-optimal actions. -/
def bestReplyPayoffs (u v : A → Ω → ℝ) : Set ((Ω → ℝ) × ℝ) :=
  (fun x : Belief Ω × A => (x.1.val, expected v x.1 x.2)) ''
    {x | BestReply u x.1 x.2}

/-- Upper boundary of the convex hull of receiver-optimal economic outcomes. -/
noncomputable def concavification (u v : A → Ω → ℝ) (q : Ω → ℝ) : ℝ :=
  sSup {z | (q, z) ∈ convexHull ℝ (bestReplyPayoffs u v)}

noncomputable def splitValue (u v : A → Ω → ℝ) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) : ℝ := ∑ s, w.val s * senderPayoff u v (b s)

noncomputable def signalValue (u v : A → Ω → ℝ) (p : Belief Ω) {n : ℕ}
    (π : Signal Ω n) : ℝ :=
  ∑ s, signalMass p π s * senderPayoff u v (signalPosterior p π s)

namespace Proof

/-- The posterior payoff formula is the state/message expectation of the
sender's primitive utility under any sender-preferred receiver actions. -/
theorem signalValue_primitive [TopologicalSpace A] [CompactSpace A] [Nonempty A]
    (u v : A → Ω → ℝ) (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) {n : ℕ}
    (π : Signal Ω n) (a : Fin n → A)
    (ha : ∀ s, SenderPreferred u v (signalPosterior p π s) (a s)) :
    signalValue u v p π = ∑ ω, p.val ω * ∑ s, (π ω).val s * v (a s) ω := by
  have hf : ∀ s, senderPayoff u v (signalPosterior p π s) =
      expected v (signalPosterior p π s) (a s) := fun s => senderPayoff_eq u v hu hv _ (ha s)
  unfold signalValue
  simp_rw [hf, expected, Finset.mul_sum]
  calc
    (∑ s, ∑ ω, signalMass p π s * ((signalPosterior p π s).val ω * v (a s) ω)) =
        ∑ s, ∑ ω, p.val ω * ((π ω).val s * v (a s) ω) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro ω _
      rw [← mul_assoc, mass_mul_posterior, mul_assoc]
    _ = _ := by rw [Finset.sum_comm]

theorem noInformation_value (u v : A → Ω → ℝ) (p : Belief Ω) :
    signalValue u v p noInformationSignal = senderPayoff u v p := by
  have hm : ∀ s : Fin 1, signalMass p noInformationSignal s = 1 := by
    intro s
    simpa [signalMass, noInformationSignal] using p.property.2
  have hb : ∀ s : Fin 1, signalPosterior p noInformationSignal s = p := by
    intro s
    apply Subtype.ext
    funext ω
    simp [signalPosterior, posteriorVector, hm, noInformationSignal]
  simp [signalValue, hm, hb]

variable [TopologicalSpace A] [CompactSpace A] [Nonempty A] [T2Space A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))

include hu hv

theorem bestReplyPayoffs_compact : IsCompact (bestReplyPayoffs u v) := by
  apply (bestReply_graph_isClosed u hu).isCompact.image
  exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_expected v hv)

theorem sender_pair_mem (p : Belief Ω) :
    (p.val, senderPayoff u v p) ∈ bestReplyPayoffs u v := by
  obtain ⟨a, ha⟩ := senderPreferred_exists u v hu hv p
  exact ⟨(p, a), ha.1, Prod.ext rfl (senderPayoff_eq u v hu hv p ha).symm⟩

theorem hull_compact : IsCompact (convexHull ℝ (bestReplyPayoffs u v)) :=
  compact_convexHull (bestReplyPayoffs_compact u v hu hv)

theorem fiber_bddAbove (p : Belief Ω) :
    BddAbove {z | (p.val, z) ∈ convexHull ℝ (bestReplyPayoffs u v)} := by
  apply (hull_compact u v hu hv).bddAbove_image continuous_snd.continuousOn |>.mono
  intro z hz
  exact ⟨(p.val, z), hz, rfl⟩

theorem hull_le (p : Belief Ω) {z : ℝ}
    (hz : (p.val, z) ∈ convexHull ℝ (bestReplyPayoffs u v)) :
    z ≤ concavification u v p.val :=
  le_csSup (fiber_bddAbove u v hu hv p) hz

theorem concavification_max_point (p : Belief Ω) :
    (p.val, concavification u v p.val) ∈ convexHull ℝ (bestReplyPayoffs u v) := by
  let K := convexHull ℝ (bestReplyPayoffs u v) ∩ {x | x.1 = p.val}
  have hk : IsCompact K := (hull_compact u v hu hv).inter_right
    (isClosed_eq continuous_fst continuous_const)
  have hne : K.Nonempty :=
    ⟨(p.val, senderPayoff u v p), subset_convexHull ℝ _ (sender_pair_mem u v hu hv p), rfl⟩
  obtain ⟨x, hx, hm⟩ := hk.exists_isMaxOn hne continuous_snd.continuousOn
  have hxp : x = (p.val, x.2) := Prod.ext hx.2 rfl
  have hf : concavification u v p.val = x.2 := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ⟨x.2, hxp ▸ hx.1⟩
    · intro z hz
      exact hm ⟨hz, rfl⟩
    · intro z hz
      exact ⟨x.2, hxp ▸ hx.1, hz⟩
  rw [hf, ← hx.2]
  exact hx.1

theorem split_pair_mem (p : Belief Ω) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) (hb : BayesPlausible p w b) :
    (p.val, splitValue u v w b) ∈ convexHull ℝ (bestReplyPayoffs u v) := by
  apply mem_convexHull_of_exists_fintype w.val
    (fun s => ((b s).val, senderPayoff u v (b s))) w.property.1 w.property.2
    (fun j => sender_pair_mem u v hu hv (b j))
  apply Prod.ext
  · ext ω
    simpa only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hb ω
  · simp [splitValue, Prod.snd_sum, Prod.smul_snd]

theorem split_le_concavification (p : Belief Ω) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) (hb : BayesPlausible p w b) :
    splitValue u v w b ≤ concavification u v p.val :=
  hull_le u v hu hv p (split_pair_mem u v hu hv p w b hb)

/-- A finite optimal splitting, with an explicit conservative ambient-dimension bound. -/
theorem optimal_split (p : Belief Ω) :
    ∃ (k : ℕ) (_ : k ≤ Fintype.card Ω + 2) (w : Belief (Fin k))
      (b : Fin k → Belief Ω), BayesPlausible p w b ∧
        splitValue u v w b = concavification u v p.val := by
  obtain ⟨k, hk, z, w, hz, hbar⟩ := convexHull_finite_support
    (concavification_max_point u v hu hv p)
  have hreps : ∀ j, ∃ x : Belief Ω × A,
      BestReply u x.1 x.2 ∧ (x.1.val, expected v x.1 x.2) = z j := hz
  choose x hx heq using hreps
  let b := fun j => (x j).1
  have hfst : ∑ j, w.val j • (b j).val = p.val := by
    have h := congrArg Prod.fst hbar
    simpa only [Prod.fst_sum, Prod.smul_fst, ← heq, b] using h
  have hb : BayesPlausible p w b := by
    intro ω
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hfst ω
  have hsnd : ∑ j, w.val j * expected v (b j) (x j).2 = concavification u v p.val := by
    have h := congrArg Prod.snd hbar
    simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul, ← heq, b] using h
  refine ⟨k, by simpa [Module.finrank_prod, Module.finrank_pi] using hk, w, b, hb,
    le_antisymm (split_le_concavification u v hu hv p w b hb) ?_⟩
  rw [← hsnd]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (bestReply_le_senderPayoff u v hu hv (b j) (hx j)) (w.property.1 j)

theorem optimal_signal (p : Belief Ω) (hp : FullSupport p) :
    ∃ (k : ℕ) (_ : k ≤ Fintype.card Ω + 2) (π : Signal Ω k),
      signalValue u v p π = concavification u v p.val ∧
      ∀ (m : ℕ) (σ : Signal Ω m), signalValue u v p σ ≤ signalValue u v p π := by
  obtain ⟨k, hk, w, b, hb, hval⟩ := optimal_split u v hu hv p
  refine ⟨k, hk, splittingSignal p hp w b hb, ?_, ?_⟩
  · exact (splitting_payoff p hp w b hb (senderPayoff u v)).trans hval
  · intro m σ
    rw [show signalValue u v p (splittingSignal p hp w b hb) = concavification u v p.val from
      (splitting_payoff p hp w b hb (senderPayoff u v)).trans hval]
    exact split_le_concavification u v hu hv p (signalWeights p σ) (signalPosterior p σ)
      (signal_bayesPlausible p σ)

omit hu hv in
theorem probabilitySimplex_convex : Convex ℝ (probabilitySimplex Ω) := by
  intro p hp q hq a b ha hb hab
  constructor
  · intro ω
    exact add_nonneg (mul_nonneg ha (hp.1 ω)) (mul_nonneg hb (hq.1 ω))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hq.2]
    simpa using hab

theorem concavification_majorizes (p : Belief Ω) :
    senderPayoff u v p ≤ concavification u v p.val :=
  hull_le u v hu hv p (subset_convexHull ℝ _ (sender_pair_mem u v hu hv p))

theorem concavification_concave :
    ConcaveOn ℝ (probabilitySimplex Ω) (concavification u v) := by
  refine ⟨probabilitySimplex_convex, ?_⟩
  intro p hp q hq a b ha hb hab
  let P : Belief Ω := ⟨p, hp⟩
  let Q : Belief Ω := ⟨q, hq⟩
  let R : Belief Ω := ⟨a • p + b • q, probabilitySimplex_convex hp hq ha hb hab⟩
  have h := convex_convexHull ℝ (bestReplyPayoffs u v)
    (concavification_max_point u v hu hv P)
    (concavification_max_point u v hu hv Q) ha hb hab
  exact hull_le u v hu hv R h

theorem concavification_le_majorant (g : (Ω → ℝ) → ℝ)
    (hg : ConcaveOn ℝ (probabilitySimplex Ω) g)
    (hmajor : ∀ p : Belief Ω, senderPayoff u v p ≤ g p.val) (p : Belief Ω) :
    concavification u v p.val ≤ g p.val := by
  obtain ⟨k, _, w, b, hb, hval⟩ := optimal_split u v hu hv p
  have hbar : ∑ s, w.val s • (b s).val = p.val := by
    ext ω
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hb ω
  have hj := hg.le_map_sum (t := Finset.univ) (w := w.val) (p := fun s => (b s).val)
    (fun s _ => w.property.1 s) w.property.2 (fun s _ => (b s).property)
  rw [hbar] at hj
  rw [← hval]
  exact (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
    (hmajor (b s)) (w.property.1 s)).trans hj

theorem senderPayoff_bounded :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : Belief Ω, |senderPayoff u v p| ≤ M := by
  have hcont : Continuous (fun x : Belief Ω × A => |expected v x.1 x.2|) :=
    (continuous_expected v hv).abs
  obtain ⟨M, hM⟩ := (isCompact_range hcont).bddAbove
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro p
  obtain ⟨a, ha⟩ := senderPreferred_exists u v hu hv p
  rw [senderPayoff_eq u v hu hv p ha]
  exact (hM ⟨(p, a), rfl⟩).trans (le_max_left _ _)

theorem persuasion_gain_iff (p : Belief Ω) (hp : FullSupport p) :
    (∃ (n : ℕ) (π : Signal Ω n), senderPayoff u v p < signalValue u v p π) ↔
      senderPayoff u v p < concavification u v p.val := by
  constructor
  · rintro ⟨n, π, hπ⟩
    exact hπ.trans_le (split_le_concavification u v hu hv p
      (signalWeights p π) (signalPosterior p π) (signal_bayesPlausible p π))
  · intro h
    obtain ⟨n, _, π, hπ, _⟩ := optimal_signal u v hu hv p hp
    exact ⟨n, π, by simpa only [hπ] using h⟩

end Proof
end BayesianPersuasion
