/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0.
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact

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

namespace Proof

variable [TopologicalSpace A]

theorem continuous_expected (u : A → Ω → ℝ) (hu : ∀ ω, Continuous (fun a => u a ω)) :
    Continuous (fun x : Belief Ω × A => expected u x.1 x.2) := by
  unfold expected
  exact continuous_finsetSum _ fun ω _ =>
    ((continuous_apply ω).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((hu ω).comp continuous_snd)

theorem continuous_expected_action (u : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω)) (p : Belief Ω) :
    Continuous (expected u p) :=
  (continuous_expected u hu).comp (continuous_const.prodMk continuous_id)

theorem bestReply_isClosed (u : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω)) (p : Belief Ω) :
    IsClosed {a | BestReply u p a} := by
  unfold BestReply
  simp only [ofPred_forall]
  exact isClosed_iInter fun b => isClosed_le continuous_const (continuous_expected_action u hu p)

theorem bestReply_graph_isClosed (u : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω)) :
    IsClosed {x : Belief Ω × A | BestReply u x.1 x.2} := by
  unfold BestReply
  simp only [ofPred_forall]
  refine isClosed_iInter fun b => isClosed_le ?_ (continuous_expected u hu)
  exact (continuous_expected u hu).comp (continuous_fst.prodMk continuous_const)

variable [CompactSpace A] [Nonempty A]

theorem bestReply_exists (u : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω)) (p : Belief Ω) :
    ∃ a, BestReply u p a := by
  obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_expected_action u hu p).continuousOn
  exact ⟨a, fun b => ha (Set.mem_univ b)⟩

theorem senderPreferred_exists (u v : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) :
    ∃ a, SenderPreferred u v p a := by
  obtain ⟨a, ha⟩ := bestReply_exists u hu p
  obtain ⟨b, hb, hmax⟩ := (bestReply_isClosed u hu p).isCompact.exists_isMaxOn
    ⟨a, ha⟩ (continuous_expected_action v hv p).continuousOn
  exact ⟨b, hb, hmax⟩

theorem senderPayoff_eq (u v : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) {a : A}
    (ha : SenderPreferred u v p a) : senderPayoff u v p = expected v p a := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨_, a, ha.1, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact ha.2 b hb
  · intro w hw
    exact ⟨_, ⟨a, ha.1, rfl⟩, hw⟩

theorem bestReply_le_senderPayoff (u v : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) {a : A}
    (ha : BestReply u p a) : expected v p a ≤ senderPayoff u v p := by
  obtain ⟨b, hb⟩ := senderPreferred_exists u v hu hv p
  rw [senderPayoff_eq u v hu hv p hb]
  exact hb.2 a ha

theorem senderPayoff_upperSemicontinuous (u v : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) :
    UpperSemicontinuous (senderPayoff u v) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro c
  have hc : IsClosed {x : Belief Ω × A | BestReply u x.1 x.2 ∧ c ≤ expected v x.1 x.2} :=
    (bestReply_graph_isClosed u hu).inter (isClosed_le continuous_const (continuous_expected v hv))
  have heq : senderPayoff u v ⁻¹' Ici c =
      Prod.fst '' {x : Belief Ω × A | BestReply u x.1 x.2 ∧ c ≤ expected v x.1 x.2} := by
    ext p
    constructor
    · intro hp
      obtain ⟨a, ha⟩ := senderPreferred_exists u v hu hv p
      exact ⟨(p, a), ⟨ha.1, by simpa [senderPayoff_eq u v hu hv p ha] using hp⟩, rfl⟩
    · rintro ⟨⟨q, a⟩, ⟨ha, hc⟩, rfl⟩
      exact hc.trans (bestReply_le_senderPayoff u v hu hv q ha)
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ hc

end Proof
end BayesianPersuasion
