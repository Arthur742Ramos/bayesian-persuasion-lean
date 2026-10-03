/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0.
-/
module

public import BayesianPersuasion.Attainment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Optimal Information and Concavification in Bayesian Persuasion

Finite states, compact metric actions, continuous utility primitives, and
a full-support common prior, and sender-preferred receiver ties yield an attained finite optimal experiment.
Its value is the least concave majorant of the induced sender payoff.
-/

@[expose] public section

universe uΩ uA
open Set Finset
namespace BayesianPersuasion

variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω] [Nonempty Ω]
variable [MetricSpace A] [CompactSpace A] [Nonempty A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))

include hu hv in
/-- The receiver optimization and sender tie rule produce a bounded USC payoff. -/
theorem economic_payoff_regular :
    (∀ p : Belief Ω, ∃ a, SenderPreferred u v p a ∧ senderPayoff u v p = expected v p a) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ p : Belief Ω, |senderPayoff u v p| ≤ M) ∧
    UpperSemicontinuous (senderPayoff u v) := by
  refine ⟨?_, Proof.senderPayoff_bounded u v hu hv,
    Proof.senderPayoff_upperSemicontinuous u v hu hv⟩
  intro p
  obtain ⟨a, ha⟩ := Proof.senderPreferred_exists u v hu hv p
  exact ⟨a, ha, Proof.senderPayoff_eq u v hu hv p ha⟩

/-- Finite Bayes-plausible splittings are exactly finite state-conditional
experiments at a full-support prior, with honest posterior recovery restricted to nonnull messages. -/
theorem finite_signal_splitting (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) :
    BayesPlausible p w b ↔ ∃ π : Signal Ω n,
      (∀ s ω, p.val ω * (π ω).val s = w.val s * (b s).val ω) ∧
      (∀ s, w.val s ≠ 0 → signalPosterior p π s = b s) ∧
      signalValue u v p π = splitValue u v w b := by
  constructor
  · intro hb
    exact ⟨splittingSignal p hp w b hb,
      fun s ω => Proof.splitting_joint p hp w b hb ω s,
      Proof.splitting_posterior p hp w b hb,
      Proof.splitting_payoff p hp w b hb (senderPayoff u v)⟩
  · rintro ⟨π, hj, _, _⟩ ω
    calc
      ∑ s, w.val s * (b s).val ω = ∑ s, p.val ω * (π ω).val s :=
        Finset.sum_congr rfl fun s _ => (hj s ω).symm
      _ = p.val ω := by rw [← Finset.mul_sum, (π ω).property.2, mul_one]

include hu hv in
/-- An optimal finite signal exists and its value is the least concave
majorant of the economically derived sender payoff on the entire simplex. -/
theorem optimal_information_and_concavification (p : Belief Ω) (hp : FullSupport p) :
    (∃ (k : ℕ) (_ : k ≤ Fintype.card Ω + 2) (π : Signal Ω k),
      signalValue u v p π = concavification u v p.val ∧
      ∀ (m : ℕ) (σ : Signal Ω m), signalValue u v p σ ≤ signalValue u v p π) ∧
    ConcaveOn ℝ (probabilitySimplex Ω) (concavification u v) ∧
    (∀ q : Belief Ω, senderPayoff u v q ≤ concavification u v q.val) ∧
    (∀ g : (Ω → ℝ) → ℝ, ConcaveOn ℝ (probabilitySimplex Ω) g →
      (∀ q : Belief Ω, senderPayoff u v q ≤ g q.val) →
      ∀ q : Belief Ω, concavification u v q.val ≤ g q.val) :=
  ⟨Proof.optimal_signal u v hu hv p hp, Proof.concavification_concave u v hu hv,
    Proof.concavification_majorizes u v hu hv, Proof.concavification_le_majorant u v hu hv⟩

include hu hv in
/-- Strict persuasion gain is exactly the concavification gap above the
sender's payoff at the uninformed common prior. -/
theorem persuasion_gain_iff (p : Belief Ω) (hp : FullSupport p) :
    (∃ (n : ℕ) (π : Signal Ω n), senderPayoff u v p < signalValue u v p π) ↔
      senderPayoff u v p < concavification u v p.val :=
  Proof.persuasion_gain_iff u v hu hv p hp

namespace Proof
include hu hv in
theorem senderPayoff_measurable [MeasurableSpace (Belief Ω)] [BorelSpace (Belief Ω)] :
    Measurable (senderPayoff u v) :=
  (senderPayoff_upperSemicontinuous u v hu hv).measurable
end Proof
end BayesianPersuasion
