module

public import BayesianPersuasion.Theorems

/-! # Nonvacuous economic examples -/
@[expose] public section

namespace BayesianPersuasion.Examples
open Set Finset

noncomputable def bernoulli (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : Belief (Fin 2) :=
  ⟨fun i => if i = 0 then 1 - t else t, by
    constructor
    · intro i; fin_cases i <;> simp <;> linarith [ht.1, ht.2]
    · simp [Fin.sum_univ_two]⟩

noncomputable local instance : MetricSpace (Fin 2) :=
  MetricSpace.induced (fun i : Fin 2 => (i.val : ℝ))
    (by intro i j h; apply Fin.ext; change (i.val : ℝ) = (j.val : ℝ) at h; exact_mod_cast h) inferInstance

def judge (a ω : Fin 2) : ℝ := if a = ω then 1 else 0
def prosecutor (a _ω : Fin 2) : ℝ := if a = 1 then 1 else 0

theorem judge_continuous (ω : Fin 2) : Continuous (fun a => judge a ω) :=
  continuous_of_discreteTopology

theorem prosecutor_continuous (ω : Fin 2) : Continuous (fun a => prosecutor a ω) :=
  continuous_of_discreteTopology

noncomputable def prior : Belief (Fin 2) := bernoulli (3 / 10) (by norm_num)
noncomputable def innocent : Belief (Fin 2) := bernoulli 0 (by norm_num)
noncomputable def indifferent : Belief (Fin 2) := bernoulli (1 / 2) (by norm_num)
noncomputable def weights : Belief (Fin 2) := bernoulli (3 / 5) (by norm_num)
noncomputable def beliefs (s : Fin 2) : Belief (Fin 2) := if s = 0 then innocent else indifferent

theorem prior_fullSupport : FullSupport prior := by
  intro ω; fin_cases ω <;> norm_num [prior, bernoulli]

theorem prior_tieRule : SenderPreferred judge prosecutor prior 0 := by
  constructor
  · intro b; fin_cases b <;> norm_num [expected, prior, bernoulli, judge, Fin.sum_univ_two]
  · intro b hb
    fin_cases b
    · exact le_rfl
    · have h := hb 0
      norm_num [expected, prior, bernoulli, judge, Fin.sum_univ_two] at h

theorem innocent_tieRule : SenderPreferred judge prosecutor innocent 0 := by
  constructor
  · intro b; fin_cases b <;> norm_num [expected, innocent, bernoulli, judge, Fin.sum_univ_two]
  · intro b hb
    fin_cases b
    · exact le_rfl
    · have h := hb 0
      norm_num [expected, innocent, bernoulli, judge, Fin.sum_univ_two] at h

theorem indifferent_tieRule : SenderPreferred judge prosecutor indifferent 1 := by
  constructor
  · intro b; fin_cases b <;> norm_num [expected, indifferent, bernoulli, judge, Fin.sum_univ_two]
  · intro b _; fin_cases b <;>
      norm_num [expected, indifferent, bernoulli, prosecutor, Fin.sum_univ_two]

theorem prior_payoff : senderPayoff judge prosecutor prior = 0 := by
  rw [Proof.senderPayoff_eq judge prosecutor judge_continuous prosecutor_continuous prior prior_tieRule]
  norm_num [expected, prosecutor, prior, bernoulli, Fin.sum_univ_two]

theorem innocent_payoff : senderPayoff judge prosecutor innocent = 0 := by
  rw [Proof.senderPayoff_eq judge prosecutor judge_continuous prosecutor_continuous innocent innocent_tieRule]
  norm_num [expected, prosecutor, innocent, bernoulli, Fin.sum_univ_two]

theorem indifferent_payoff : senderPayoff judge prosecutor indifferent = 1 := by
  rw [Proof.senderPayoff_eq judge prosecutor judge_continuous prosecutor_continuous indifferent indifferent_tieRule]
  norm_num [expected, prosecutor, indifferent, bernoulli, Fin.sum_univ_two]

theorem prosecutor_split : BayesPlausible prior weights beliefs := by
  intro ω
  fin_cases ω <;> norm_num [Fin.sum_univ_two, weights, beliefs, prior, innocent, indifferent, bernoulli]

theorem prosecutor_split_value : splitValue judge prosecutor weights beliefs = 3 / 5 := by
  simp [splitValue, Fin.sum_univ_two, beliefs, innocent_payoff, indifferent_payoff, weights, bernoulli]

/-- The paper's prosecutor gains from 0 to 3/5 at prior guilt probability 3/10. -/
theorem prosecutor_strict_gain :
    ∃ π : Signal (Fin 2) 2,
      signalValue judge prosecutor prior π = 3 / 5 ∧
      senderPayoff judge prosecutor prior < signalValue judge prosecutor prior π := by
  let π := splittingSignal prior prior_fullSupport weights beliefs prosecutor_split
  have hπ : signalValue judge prosecutor prior π = 3 / 5 :=
    (Proof.splitting_payoff prior prior_fullSupport weights beliefs prosecutor_split
      (senderPayoff judge prosecutor)).trans prosecutor_split_value
  exact ⟨π, hπ, by rw [prior_payoff, hπ]; norm_num⟩

noncomputable def quadraticReceiver (a : Icc (0 : ℝ) 1) (ω : Fin 2) : ℝ :=
  -(a.val - (ω.val : ℝ)) ^ 2
def linearSender (a : Icc (0 : ℝ) 1) (_ω : Fin 2) : ℝ := a.val

/-- The theorem applies also to a continuum of actions, not only finite games. -/
theorem interval_action_optimum :
    ∃ (n : ℕ) (_ : n ≤ 4) (π : Signal (Fin 2) n),
      signalValue quadraticReceiver linearSender prior π =
        concavification quadraticReceiver linearSender prior.val ∧
      ∀ (m : ℕ) (σ : Signal (Fin 2) m),
        signalValue quadraticReceiver linearSender prior σ ≤
          signalValue quadraticReceiver linearSender prior π := by
  have hu : ∀ ω, Continuous (fun a => quadraticReceiver a ω) := by
    intro ω; unfold quadraticReceiver; fun_prop
  have hv : ∀ ω, Continuous (fun a => linearSender a ω) := by
    intro ω; exact continuous_subtype_val
  simpa using Proof.optimal_signal quadraticReceiver linearSender hu hv prior prior_fullSupport

end BayesianPersuasion.Examples
