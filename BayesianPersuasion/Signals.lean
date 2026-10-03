module

public import BayesianPersuasion.Primitives
public import Mathlib.Tactic

@[expose] public section

universe uΩ uA

open Set Finset
namespace BayesianPersuasion

variable {Ω : Type uΩ} [Fintype Ω]

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

/-- Realization of a splitting. Full support is needed for this division formula. -/
noncomputable def splittingVector (p : Belief Ω) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) (ω : Ω) (s : Fin n) : ℝ := w.val s * (b s).val ω / p.val ω

namespace Proof

theorem signalMass_nonneg (p : Belief Ω) {n : ℕ} (π : Signal Ω n) (s : Fin n) :
    0 ≤ signalMass p π s :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (p.property.1 ω) ((π ω).property.1 s)

theorem signalMass_sum (p : Belief Ω) {n : ℕ} (π : Signal Ω n) :
    ∑ s, signalMass p π s = 1 := by
  unfold signalMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (π _).property.2, mul_one]
  exact p.property.2

theorem joint_eq_zero_of_null (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) (hs : signalMass p π s = 0) (ω : Ω) : p.val ω * (π ω).val s = 0 := by
  apply le_antisymm _ (mul_nonneg (p.property.1 ω) ((π ω).property.1 s))
  calc
    _ ≤ signalMass p π s := Finset.single_le_sum
      (fun ω _ => mul_nonneg (p.property.1 ω) ((π ω).property.1 s)) (mem_univ ω)
    _ = 0 := hs

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

noncomputable def signalWeights (p : Belief Ω) {n : ℕ} (π : Signal Ω n) : Belief (Fin n) :=
  ⟨signalMass p π, Proof.signalMass_nonneg p π, Proof.signalMass_sum p π⟩

noncomputable def signalPosterior (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) : Belief Ω := ⟨posteriorVector p π s, Proof.posteriorVector_isBelief p π s⟩

namespace Proof

theorem mass_mul_posterior (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) (ω : Ω) :
    signalMass p π s * (signalPosterior p π s).val ω = p.val ω * (π ω).val s := by
  classical
  change signalMass p π s * posteriorVector p π s ω = _
  unfold posteriorVector
  split_ifs with h
  · simp only [h, zero_mul]
    exact (joint_eq_zero_of_null p π s h ω).symm
  · field_simp

theorem signal_bayesPlausible (p : Belief Ω) {n : ℕ} (π : Signal Ω n) :
    BayesPlausible p (signalWeights p π) (signalPosterior p π) := by
  intro ω
  change ∑ s, signalMass p π s * (signalPosterior p π s).val ω = _
  simp_rw [mass_mul_posterior, ← Finset.mul_sum, (π ω).property.2, mul_one]

theorem splittingVector_isBelief (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b) (ω : Ω) :
    (∀ s, 0 ≤ splittingVector p w b ω s) ∧ ∑ s, splittingVector p w b ω s = 1 := by
  constructor
  · intro s
    exact div_nonneg (mul_nonneg (w.property.1 s) ((b s).property.1 ω)) (hp ω).le
  · unfold splittingVector
    rw [← Finset.sum_div, hb ω, div_self (ne_of_gt (hp ω))]

end Proof

noncomputable def splittingSignal (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b) : Signal Ω n :=
  fun ω => ⟨splittingVector p w b ω, Proof.splittingVector_isBelief p hp w b hb ω⟩

namespace Proof

theorem splitting_joint (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b)
    (ω : Ω) (s : Fin n) :
    p.val ω * (splittingSignal p hp w b hb ω).val s = w.val s * (b s).val ω := by
  change p.val ω * (w.val s * (b s).val ω / p.val ω) = _
  field_simp [ne_of_gt (hp ω)]

theorem splitting_mass (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b)
    (s : Fin n) : signalMass p (splittingSignal p hp w b hb) s = w.val s := by
  unfold signalMass
  simp_rw [splitting_joint, ← Finset.mul_sum, (b s).property.2, mul_one]

theorem splitting_posterior (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b)
    (s : Fin n) (hs : w.val s ≠ 0) :
    signalPosterior p (splittingSignal p hp w b hb) s = b s := by
  apply Subtype.ext
  funext ω
  change posteriorVector _ _ _ _ = _
  unfold posteriorVector
  rw [splitting_mass, ite_eq_right hs, splitting_joint]
  field_simp

theorem splitting_payoff (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b)
    (f : Belief Ω → ℝ) :
    ∑ s, signalMass p (splittingSignal p hp w b hb) s *
      f (signalPosterior p (splittingSignal p hp w b hb) s) = ∑ s, w.val s * f (b s) := by
  apply Finset.sum_congr rfl
  intro s _
  rw [splitting_mass]
  by_cases hs : w.val s = 0
  · simp [hs]
  · rw [splitting_posterior p hp w b hb s hs]

end Proof
end BayesianPersuasion
