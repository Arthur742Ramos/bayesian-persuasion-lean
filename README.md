# Optimal Information and Concavification in Bayesian Persuasion

An admission-free Lean development of the finite-state economic theorem of
Kamenica and Gentzkow (2011), from receiver and sender utilities through an
attained optimal information signal and the least concave majorant.

The state space is finite and nonempty. Actions form a nonempty compact metric
space. Both utilities are continuous in the action at each state. The common
prior has full support. The receiver maximizes expected utility, resolving ties
in the sender's favor. Neither payoff regularity nor attainment is assumed.

The library proves receiver and sender-tie maximizers exist, the induced sender
payoff is bounded and upper semicontinuous, finite Bayes-plausible splittings
are realizable by normalized conditional signals, and an optimal finite signal
exists. Its value is the least concave majorant on the entire probability
simplex. Persuasion strictly helps exactly when this value exceeds the payoff
at the uninformed prior.

## Main contracts

| Declaration | Result |
|---|---|
| `economic_payoff_regular` | Achieved sender-preferred receiver payoff, uniform bound, and USC derived from continuous utility primitives. |
| `finite_signal_splitting` | Finite Bayes plausibility iff a conditional signal realizes the exact state/message joint law and payoff. |
| `optimal_information_and_concavification` | Some signal with at most `card Ω + 2` messages attains the least concave majorant and dominates every finite signal. |
| `persuasion_gain_iff` | Strict signal improvement iff there is a strict concavification gap. |

All four live in `BayesianPersuasion`; reusable supporting proofs live in
`BayesianPersuasion.Proof`. [Theorems.lean](BayesianPersuasion/Theorems.lean)
contains their exact binders. [Solution.lean](Solution.lean) imports the proved
library. The standalone [Challenge.lean](Challenge.lean) contains the shared
definitions, small normalization proofs required by subtype-valued posterior
definitions, and the four statement holes used by the official Comparator.
No authored library or Solution declaration contains an admission.

## Economic and measure scope

Signals and splittings have finite message spaces. Posterior vectors are
normalized probabilities. At null messages the posterior is defined to be the
prior; recovery of a prescribed splitting posterior is required only at nonzero
message weights. Those messages contribute zero to expected utility. Repeated
posterior beliefs are permitted as distinct indexed messages; their combined
mass gives the corresponding posterior distribution. All expectations here are
finite real sums. A Borel measurability corollary for the sender payoff is proved;
no arbitrary-measure signal or integration theorem is claimed.

The primitive state/message expectation is proved equal to `signalValue` for
any sender-preferred receiver actions. A single constant message has value
`senderPayoff` at the prior. Thus the baseline in the strict-gain theorem is the
actual no-information experiment.

This formalizes the signal/splitting portion of Proposition 1, the optimal-signal
existence argument, and Corollary 2. The straightforward recommendation branch
and compact-state online extension are excluded. The paper's requirements of
at least two actions and each action being receiver-optimal at some belief are unnecessary for these results
and are relaxed to nonempty actions. The proved support bound `card Ω + 2` is
conservative; no sharper support claim is made.

[Examples.lean](BayesianPersuasion/Examples.lean) checks the prosecutor/judge
example: prior guilt probability `3/10`, posterior guilt probabilities `0` and
`1/2`, weights `2/5` and `3/5`, sender value `3/5` versus zero without information.
It also instantiates optimal attainment with a continuum of actions `[0,1]`,
a quadratic receiver utility, and a linear sender utility.

## Proof and prior art

The receiver best-response graph is closed in the compact belief/action product.
Sender-favored tie maximization yields the payoff and its USC by closed compact
projection. The continuous image of all receiver-optimal outcomes is compact.
A proved finite-dimensional compact-convex-hull lemma gives a compact feasible
payoff fiber. Its maximum yields a finite splitting by Carathéodory; improving
ties and comparing with that same maximum forces equality. Finite Jensen proves
minimality among all concave majorants, without imposing continuity or bounds
on the competing majorant.

Primary source: Emir Kamenica and Matthew Gentzkow, [“Bayesian Persuasion,”
American Economic Review 101(6), 2011, pp. 2590–2615](https://doi.org/10.1257/aer.101.6.2590),
[author-hosted paper](https://web.stanford.edu/~gentzkow/research/BayesianPersuasion.pdf),
model pp. 2593–2594, Proposition 1, Corollary 2, and Appendix A.

Daniel Lyng's [Econlib at `003655ccf010cdf44c4f67d6675167b54ce0e9df`](https://github.com/danlyng/Econlib/tree/003655ccf010cdf44c4f67d6675167b54ce0e9df),
dated 2026-07-09 and source-inspected 2026-10-03 UTC, already proves finite
splitting and concavification with `n+1` signals in
[Finite/Caratheodory.lean](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/MechanismDesign/InformationDesign/Persuasion/Finite/Caratheodory.lean),
and attainment for a supplied bounded USC payoff over compact metric states in
[Duality/PrimalAttainment.lean](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/MechanismDesign/InformationDesign/Persuasion/Duality/PrimalAttainment.lean).
Econlib was inspected, not independently built for this project. CompactHull's
finite reindexing/padding arguments adapt its Apache-2.0 source with retained
copyright and attribution. This package depends on mathlib alone and proves
the economic chain from utility primitives. No first-formalization, missing
prior attainment, or mathematical novelty claim is made.

## Reproduce and verify

Lean `4.35.0-rc2`; mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
All dependencies are pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake build BayesianPersuasion Challenge Solution
lake env lean scripts/Audit.lean
lake comparator
```

The audit checks every authored constant, including examples and auxiliary
constants, against only `propext`, `Classical.choice`, and `Quot.sound`.
Comparator names are checked in both environments, with genuine definitions
in `definition_names`. On macOS the official Comparator lacks bubblewrap;
local runs use its explicit no-sandbox mode. The authoritative hosted full
verification uses the official sandbox and Lean, NanoDa, and con-ron.

The public workflows are predictive verification, independent of registry
intake. `proof.yml` calls official reusable `submission.yml` in `full` mode
under `palomar-standard-v1`; its workflow and pipeline SHA both equal
`65f0154ed776cd26c224254aa57b379137f28b0d`. `render.yml` ports the official
render dispatch with the same pinned trusted source, exact Verso selection,
trusted core-notation audit, sanitizer, and 8 MiB per-file cap (25 MiB total).
Reports, exact source hashes, and artifact digests must be inspected before
calling a commit ready. These workflows do not constitute Palomar intake,
review, acceptance, or registration.

Authors and responsible maintainers: Arthur Freitas Ramos, David Barros Hulak,
and Ruy Jose Guerra Barretto de Queiroz. License: Apache-2.0.
