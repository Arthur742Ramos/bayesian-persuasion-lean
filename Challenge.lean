/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0.
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

/-!
# Optimal Information and Concavification in Bayesian Persuasion

Finite states, nonempty compact metric actions, continuous utilities, and a
full-support common prior. Receiver indifference is resolved in the sender's
favor. Finite signals realize exactly finite Bayes-plausible splittings;
an optimal finite signal exists and its value is the least concave majorant.
Only nonnull messages must recover a prescribed posterior.

The statement covers the signal/splitting part of Proposition 1, the existence
argument, and Corollary 2 in Kamenica and Gentzkow (2011). It does not include
the straightforward recommendation branch or compact-state extension.
The support bound proved here is the conservative |Ω| + 2 bound.
-/

@[expose] public section
universe uΩ uA
open Set Finset
namespace BayesianPersuasion

variable (Ω : Type uΩ) [Fintype Ω]

/-- Probability vectors on the finite state space, with their usual topology. -/
abbrev Belief := {p : Ω → ℝ // (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1}

variable {Ω} {A : Type uA}

/-- Expected utility at a belief. -/
def expected (u : A → Ω → ℝ) (p : Belief Ω) (a : A) : ℝ :=
  ∑ ω, p.val ω * u a ω

/-- The receiver maximizes expected utility over all available actions. -/
def BestReply (u : A → Ω → ℝ) (p : Belief Ω) (a : A) : Prop :=
  ∀ b, expected u p b ≤ expected u p a

/-- Among receiver best replies, the action maximizes the sender's utility. -/
def SenderPreferred (u v : A → Ω → ℝ) (p : Belief Ω) (a : A) : Prop :=
  BestReply u p a ∧ ∀ b, BestReply u p b → expected v p b ≤ expected v p a

/-- The sender's value under receiver best response and sender-preferred ties. -/
noncomputable def senderPayoff (u v : A → Ω → ℝ) (p : Belief Ω) : ℝ :=
  sSup (expected v p '' {a | BestReply u p a})


/-- Finite state-conditional signal probabilities, normalized at every state. -/
abbrev Signal (Ω : Type uΩ) [Fintype Ω] (n : ℕ) := Ω → Belief (Fin n)

/-- One constant message conveys no information about the state. -/
def noInformationSignal : Signal Ω 1 := fun _ => ⟨fun _ => 1, by simp⟩

def FullSupport (p : Belief Ω) : Prop := ∀ ω, 0 < p.val ω

/-- A finite distribution of posterior beliefs with barycenter equal to the prior. -/
def BayesPlausible (p : Belief Ω) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) : Prop := ∀ ω, ∑ s, w.val s * (b s).val ω = p.val ω

def signalMass (p : Belief Ω) {n : ℕ} (π : Signal Ω n) (s : Fin n) : ℝ :=
  ∑ ω, p.val ω * (π ω).val s

/-- At null messages the posterior is defined to be the prior. -/
noncomputable def posteriorVector (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) : Ω → ℝ :=
  if signalMass p π s = 0 then p.val else fun ω => p.val ω * (π ω).val s / signalMass p π s

namespace Proof

theorem signalMass_nonneg (p : Belief Ω) {n : ℕ} (π : Signal Ω n) (s : Fin n) :
    0 ≤ signalMass p π s :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (p.property.1 ω) ((π ω).property.1 s)

theorem posteriorVector_isBelief (p : Belief Ω) {n : ℕ} (π : Signal Ω n) (s : Fin n) :
    (∀ ω, 0 ≤ posteriorVector p π s ω) ∧ ∑ ω, posteriorVector p π s ω = 1 := by
  classical
  unfold posteriorVector
  split_ifs with h
  · exact p.property
  · constructor
    · intro ω
      exact div_nonneg (mul_nonneg (p.property.1 ω) ((π ω).property.1 s))
        (signalMass_nonneg p π s)
    · rw [← Finset.sum_div]
      exact div_self h

end Proof

noncomputable def signalPosterior (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) : Belief Ω := ⟨posteriorVector p π s, Proof.posteriorVector_isBelief p π s⟩
section ValueDefinitions
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

end ValueDefinitions
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
  sorry

/-- Finite Bayes-plausible splittings are exactly finite state-conditional
experiments at a full-support prior, with honest posterior recovery restricted to nonnull messages. -/
theorem finite_signal_splitting (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) :
    BayesPlausible p w b ↔ ∃ π : Signal Ω n,
      (∀ s ω, p.val ω * (π ω).val s = w.val s * (b s).val ω) ∧
      (∀ s, w.val s ≠ 0 → signalPosterior p π s = b s) ∧
      signalValue u v p π = splitValue u v w b := by
  sorry

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
      ∀ q : Belief Ω, concavification u v q.val ≤ g q.val) := by
  sorry

include hu hv in
/-- Strict persuasion gain is exactly the concavification gap above the
sender's payoff at the uninformed common prior. -/
theorem persuasion_gain_iff (p : Belief Ω) (hp : FullSupport p) :
    (∃ (n : ℕ) (π : Signal Ω n), senderPayoff u v p < signalValue u v p π) ↔
      senderPayoff u v p < concavification u v p.val := by
  sorry

end BayesianPersuasion
