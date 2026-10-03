# Independent mathematical review

Reviewed 2026-10-03 UTC. This is a proof-architecture and contract review, not certification of an implementation: no candidate source existed in this workspace when the review began, and no Lean build was run.

## Primary source and scope

Primary source: Emir Kamenica and Matthew Gentzkow, “Bayesian Persuasion,” *American Economic Review* 101(6), 2011, 2590–2615, DOI 10.1257/aer.101.6.2590, [author-hosted paper](https://web.stanford.edu/~gentzkow/research/BayesianPersuasion.pdf). Checked the model on pp. 2593–2594, Proposition 1 on p. 2595, concavification and existence discussion on p. 2596, Corollary 2 on p. 2597, and Appendix A on p. 2610.

The paper uses finitely many states, compact actions, continuous utilities, a common prior with positive mass at every state, finite signals, and sender-preferred receiver indifference resolution. It explicitly limits literal signal/posterior equivalence to finitely supported posterior distributions. Its selected sender payoff is upper semicontinuous; continuity is not asserted. The desired finite-state, compact-metric-action theorem is within this scope. The compact-state online extension is a different scope. Restrictions excluding redundant actions or requiring multiple actions are unnecessary for the central existence/concavification result and may be omitted as an explicitly stated generalization.

## Exact recommended contracts

Let `Ω` be a finite nonempty type, `A` a nonempty compact metric type, and `u v : A → Ω → ℝ`, with `Continuous (fun a => u a ω)` and `Continuous (fun a => v a ω)` for every `ω`. This is joint continuity when the finite state space is given the discrete topology. Let `Δ` be the actual probability simplex, not an unrestricted vector space. Write

```
U(p,a) = ∑ ω, p(ω) * u(a,ω)
W(p,a) = ∑ ω, p(ω) * v(a,ω)
BR(p,a) ↔ ∀ b, U(p,b) ≤ U(p,a)
TB(p,a) ↔ BR(p,a) ∧ ∀ b, BR(p,b) → W(p,b) ≤ W(p,a)
```

Prove `∀ p : Δ, ∃ a, BR(p,a)` and `∀ p : Δ, ∃ a, TB(p,a)`. Define an actual selected action by choice from the latter result, then `f(p)=W(p,a(p))`. Prove the characterization `TB(p,a) → W(p,a)=f(p)`; this removes dependence on the arbitrary tertiary tie choice. Prove `∃ M ≥ 0, ∀ p, |f(p)|≤M` and `UpperSemicontinuous f` from `u,v`, not as assumptions.

A finite experiment with realization type `S` has conditional probabilities `k(ω,s)≥0` and `∑ s,k(ω,s)=1`. A finite split has `w(s)≥0`, `∑ s,w(s)=1`, `p(s)∈Δ`, and `∀ω,∑s,w(s)*p(s)(ω)=p₀(ω)`. Define its value by the finite sum `∑s,w(s)*f(p(s))`. Do not replace either object with a supplied certificate that already asserts the claimed economic property.

For positive prior `p₀`, prove both conversions between these genuine objects and equality of values. A reconstruction can use `k(ω,s)=w(s)*p(s)(ω)/p₀(ω)`. State that posterior recovery holds when `w(s)>0`. Null messages need not recover an arbitrary padded posterior. The exact main result should quantify over *all* finite experiments, not only a preselected fixed number; a proved support-reduction lemma bridges that quantification to finite optimization.

Define `C(p)` on the *entire* simplex as the supremum of values of finite Bayes-plausible splits at `p`. Prove the following, with no attainment assumption:

1. At every `p∈Δ`, a finite split attains `C(p)`.
2. `C` is concave on `Δ` and `f(p)≤C(p)`.
3. For every real-valued `g` concave on `Δ` with `f≤g` there, `C≤g` there.
4. At a positive prior, a finite experiment attains `C(p₀)` and every finite experiment has value at most `C(p₀)`.
5. A strictly profitable experiment exists iff `f(p₀)<C(p₀)`.

Together (2) and (3) say least concave majorant, rather than simply applying that label to the definition. Concavity belongs on the simplex; a theorem only on positive priors does not establish the full majorant property at boundary beliefs.

## Feasible mathlib-only architecture

### Receiver optimization and derived regularity

Finite sums make `U,W` continuous on `Δ×A`. For each belief, use the extreme-value theorem on `A`. The set

```
K = {(p,a) : Δ × A | ∀ b, U(p,b) ≤ U(p,a)}
```

is closed: an arbitrary intersection of closed comparison sets. Consequently `K` is compact and each nonempty fiber `BR(p,·)` is compact. Maximize continuous `W(p,·)` on this fiber to obtain `TB`.

For any real threshold `c`,

```
{p | c ≤ f(p)} = Prod.fst '' {x∈K | c ≤ W(x)}.
```

The right-hand set is closed before projection; projection along compact `A` is closed. Thus all upper level sets of `f` are closed, which proves USC directly. Bounds follow by maximizing and minimizing `W` on the compact ambient `Δ×A`, then evaluating at the chosen action. None of these steps needs a continuous or measurable action selection. For finite signals all integration is a finite sum. If a measure-valued statement is later added, equip `Δ` with its Borel sigma algebra and derive measurability from USC and integrability from the bound; a merely arbitrary choice of `a(p)` does not establish its measurability.

### Attainment without weighted-USC bookkeeping

Use the compact best-response graph `K`, allowing all receiver best responses temporarily. Map `(p,a)` continuously to `(p,W(p,a))` in `(Ω→ℝ)×ℝ`. Given an arbitrary finite split and its chosen `TB` actions, its mean and payoff are in the convex hull of this image. Carathéodory reduces it to a convex combination of a uniformly bounded number of image points. The resulting actions are receiver best replies, though not necessarily sender-preferred.

For a fixed sufficiently large number `N`, optimize

```
∑ i : Fin N, w(i) * W(p(i),a(i))
```

on `simplexWeights × (Fin N → K)`, restricted by the closed coordinate equations `∑i,w(i)*p(i)=p₀`. This set is compact and nonempty (the uninformative split plus padding). The objective is continuous. Every genuine split is represented with identical value after Carathéodory, so this maximum bounds all genuine values. At the maximizing configuration, replace each action by a `TB` action at that belief. The payoff weakly increases. The resulting configuration remains feasible within the same compact set, so maximality forces equality. It is therefore a genuine sender-preferred optimal finite split.

This proof is mathematically stronger than simply assuming bounded USC and applying abstract attainment: it starts from the utilities and uses economic best-response constraints. USC is still separately proved, so the paper's regularity statement is supported.

Raw ambient dimension is `|Ω|+1`, yielding `N=|Ω|+2`. Dropping one belief coordinate gives `N=|Ω|+1`; its omitted coordinate follows from total probability one. Either bound suffices for existence. Do not advertise the sharp `|Ω|` bound unless separately proved. Zero-padding permits fixed `N` without altering barycenters or values.

Another correct route uses a bounded hypograph `{(p,t) | L≤t≤f(p)}`. This set is compact because of derived USC and the payoff bound. Its convex hull is compact in finite dimensions, and a maximal vertical fiber gives attainment. However the inspected mathlib checkout does not expose a ready-made theorem that the convex hull of an arbitrary compact set is compact. It exposes `Set.Finite.isCompact_convexHull`, which is insufficient for this route. The finite-product optimization above avoids writing this extra general compact-convex-hull theorem.

### Concavification

At arbitrary beliefs take the attained optimal splits and concatenate them with weights `αw` and `βw` for `α,β≥0`, `α+β=1`. The combined split at `αp+βq` proves concavity. The singleton split proves majorization. For any concave majorant `g`, finite Jensen yields

```
∑i,w(i)*f(p(i)) ≤ ∑i,w(i)*g(p(i)) ≤ g(∑i,w(i)*p(i)).
```

Taking the established finite maximum proves minimality. This needs no boundedness or continuity assumption on the competing `g`.

## Verified mathlib interfaces

Read-only source inspected at mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`, in `/Users/arthur/Documents/Codex/2026-10-01/task-3/render-diagnosis/reproduction/workspace/.lake/packages/mathlib`. Names must be checked against the implementation's eventual pin.

- `IsCompact.exists_isMaxOn` in `Mathlib/Topology/Order/Compact.lean`: compact set, nonempty set, continuous-on objective. Prefer this for `A` and best-response fibers. `Continuous.exists_forall_ge` has an additional cocompact limit premise; it is not the direct compact-space interface.
- `isClosed_iInter`, `isClosed_le`, `IsClosed.isCompact`, `IsCompact.of_isClosed_subset`, `IsCompact.image_of_continuousOn`, `IsCompact.bddAbove_image`, and `IsCompact.bddBelow_image` support the graph and bounds.
- `isClosedMap_fst_of_compactSpace` in `Mathlib/Topology/Maps/Proper/Basic.lean` and `upperSemicontinuous_iff_isClosed_preimage` in `Mathlib/Topology/Semicontinuity/Basic.lean` support the USC proof. `upperSemicontinuous_iff_IsClosed_hypograph` is also present, with exactly that capitalization.
- `UpperSemicontinuous.measurable` in `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean` supplies the optional measurable-payoff corollary.
- `mem_convexHull_of_exists_fintype` and `mem_convexHull_iff_exists_fintype` in `Mathlib/Analysis/Convex/Combination.lean` connect barycenters to convex hull. The forward construction lemma is universe polymorphic; the equivalence quantifies over `Type` in a fixed universe.
- `eq_pos_convex_span_of_mem_convexHull` in `Mathlib/Analysis/Convex/Caratheodory.lean` returns a finite index sort, points, positive weights, total weight one, barycenter equality, and affine independence.
- `AffineIndependent.card_le_finrank_succ` in `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean`, followed by subspace rank monotonicity, gives the support bound. `Module.finrank_prod` and `Module.finrank_pi` compute ambient dimension.
- `stdSimplex`/`StdSimplex`, `convex_stdSimplex`, `isCompact_stdSimplex`, and `isClosed_stdSimplex` exist. The lowercase compactness/closedness interfaces are deprecated in this checkout in favor of newer `StdSimplex` interfaces, so a small dedicated probability-simplex subtype may be easier to keep stable.
- `ConcaveOn.le_map_sum` and `ConcaveOn.le_map_centerMass` in `Mathlib/Analysis/Convex/Jensen.lean` establish least-majorant minimality.

## Edge cases and rejection criteria

- Never divide by signal mass zero. Define posterior at null messages by a chosen simplex element, prove the joint identity separately by nonnegativity, and restrict posterior recovery to positive mass.
- Duplicate beliefs are allowed in indexed splits. Their posterior *distribution* merges their masses; do not identify indexed message cardinality with support cardinality.
- Full support concerns the prior only; posterior beliefs may lie anywhere on the boundary. They cannot be restricted to positive beliefs to ease topology.
- Nonempty state and action spaces must be explicit or derived from actual witnesses. Empty realization types admit no probability distribution and must not create a vacuous optimality theorem.
- Boundedness of expected sender payoff must be derived globally from the compact continuous primitives. Compactness alone does not bound an arbitrary discontinuous real function below.
- A theorem conditional on `UpperSemicontinuous f`, supplied `IsCompact K`, a supplied optimizer, `C` already declared concave, or an assumed finite reduction is a useful support theorem but is not the economic main theorem until those facts are proved from primitives.
- An experiment is compared with *all* finite realization cardinalities; optimality solely within `Fin N` needs the proved reduction bridge.
- If implementing Proposition 1's straightforward-signal branch, coalescing messages recommending the same action preserves both receiver optimality and sender optimality: any action tied with the recommendation at the mean must tie in receiver utility at every positive-weight original belief, so its sender advantage cannot be positive in the mean. A global arbitrary tertiary tie selector may choose a different equally good action; use a recommendation-respecting tertiary convention or state obedience as existence. This subtlety does not affect the payoff/splitting theorem.
- Use an economically nonvacuous example with strict persuasion gain and a separate indifference-jump example. The prosecutor/judge game can serve both: at prior guilt probability `3/10`, posterior guilt probabilities `0` and `1/2` with weights `2/5` and `3/5` produce value `3/5`, versus zero without information. It also refutes an unjustified continuity claim at `1/2`.

## Prior art inspected

On 2026-10-03 UTC, read current source for Daniel Lyng's [finite Caratheodory file](https://github.com/danlyng/Econlib/blob/main/Econlib/MechanismDesign/InformationDesign/Persuasion/Finite/Caratheodory.lean) and [PrimalAttainment file](https://github.com/danlyng/Econlib/blob/main/Econlib/MechanismDesign/InformationDesign/Persuasion/Duality/PrimalAttainment.lean). The first proves finite splitting reduction and concavification with `n+1` signals. The second proves primal attainment for a supplied bounded USC payoff over compact state probability measures, using compact feasibility and an integral USC theorem. These are substantive related formalizations; they were source-inspected here, not built. Their headers specify Daniel Lyng and Apache 2.0. No first-formalization claim is supported. Distinguish the intended economic chain from utilities through tie breaking to finite experiment attainment. Pin an immutable Econlib commit for final citation; the browser did not retrieve GitHub API commit history in this review.

## Current verdict

The target is mathematically valid under the stated primitive assumptions. A mathlib-only proof is feasible through compact best-response graphs, finite Carathéodory reduction, continuous finite optimization, and Jensen. The principal implementation risks are dependent simplex topology, finite support reindexing/padding, and coercions in affine-dimension lemmas. No unproved regularity or attainment hypothesis is required.

## Independent candidate implementation review

On 2026-10-03 UTC, inspected all five requested candidate files, read-only, under `bayesian-persuasion-lean/BayesianPersuasion`. The candidate pins Lean `leanprover/lean4:v4.35.0-rc2` and mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, matching the interfaces inspected above. Compilation was reported by the implementation lead; this review did not independently run a build. The following SHA-256 hashes identify the inspected snapshot:

| File | SHA-256 |
| --- | --- |
| `Primitives.lean` | `8e9df44c6352139c853ae111fc3bccd3fde4268fa60596293389bb23d68ac271` |
| `Signals.lean` | `08075bd67275afe24e974a8fdf6435ea54f382f837ef89cbcbeca5e29c0490fd` |
| `CompactHull.lean` | `a4e0a9ee39bcb0b7307d31e04274adc4e11b206b2cc15c34385a63add1d8098a` |
| `Attainment.lean` | `0c807cb24cc1f16efc9bfeba4da24027e1adadf076c9763c15db57ac645c9d82` |
| `Theorems.lean` | `a55e3050ba8714ff0d0cd5bdfac4812722cf13c36ca0be980141e2f3885ecd7a` |

Verdict: **no mathematical or contract blocker found in this snapshot**. The main assumptions are finite nonempty states, compact nonempty metric actions, action-continuous real sender and receiver utilities for every state, and a full-support common prior only where signal reconstruction is required. There is no hypothesis supplying upper semicontinuity, concavity, an optimizer, finite support reduction, or the desired conclusion.

### Primitive chain and tie breaking

`Belief` is an actual nonnegative normalized real probability vector subtype. `BestReply` compares receiver expected utility against all actions; `SenderPreferred` imposes sender maximization only among those best replies. `senderPayoff` is defined as the supremum of sender expected utility over receiver best replies, rather than a chosen arbitrary function. The proofs derive existence of receiver and sender-preferred maxima using compactness and continuity. `senderPayoff_eq` proves that *every* sender-preferred maximizer achieves this supremum, so any tertiary choice has the same payoff. This is a legitimate choice-independent payoff construction.

`senderPayoff_upperSemicontinuous` proves closed upper level sets by projection along compact actions of the closed best-response graph intersected with an expected-payoff comparison. `senderPayoff_bounded` derives a global absolute bound from compactness of the range of continuous absolute expected sender utility. Neither property is silently assumed. `economic_payoff_regular` correctly packages existence of an actual sender-preferred maximizing action, boundedness, and USC from the primitives. Its continuity assumptions are coordinatewise in actions, appropriate for finite discrete states. The extra measurable-payoff corollary uses the Borel structure and the proved USC. No global action selection or its measurability is asserted.

### Signals, null realizations, and splitting

`Signal Ω n = Ω → Belief (Fin n)` is an actual normalized conditional probability kernel. `signalMass` is the unconditional realization probability. A null message is assigned the prior as its totalized posterior. `joint_eq_zero_of_null` uses nonnegative joint terms to show each joint probability vanishes, and `mass_mul_posterior` remains correct at null messages. These identities prove Bayes plausibility for arbitrary signals.

Reconstruction divides only by positive prior coordinates; posterior recovery is asserted only for nonzero split weights. At zero split weights the expected-value term vanishes, so the totalized null posterior does not affect value. Duplicate posterior vectors remain allowed as separate indexed messages, consistent with finite splitting; no support-cardinality equality is asserted. Empty signal types are not an optimization loophole: for a nonempty state type, a signal into `Belief (Fin 0)` cannot exist because its coordinates would sum to zero instead of one.

`finite_signal_splitting` is a correct exact equivalence for a proposed finite indexed split: Bayes plausibility iff there exists an experiment with the matching joint distribution, recovery on nonnull messages, and identical value. The converse needs only the joint equality, as expected. Arbitrary experiment-to-split conversion is also explicitly proved in the library by `signal_bayesPlausible`; thus the scope is not limited to only constructed experiments.

### Compact convex hull and attainment

The implementation takes the general compact-convex-hull route identified above and supplies the missing reusable `compact_convexHull` proof. It establishes a finite-support bound by mathlib Carathéodory plus affine dimension, reindexes to `Fin k`, then pads with zero weights and points genuinely in the original set. It realizes the convex hull as the continuous image of compact fixed-size simplex weights and a finite product of the compact set. Its empty-set branch is handled separately. This proves compactness without any closed-hull substitution or assumed finite support theorem.

`bestReplyPayoffs` includes belief/payoff pairs from *all* receiver best replies; its compactness is derived from the graph. This larger set is intentionally used instead of the graph of the sender-preferred payoff, which need not be closed. `concavification_max_point` obtains an actual top point in the compact vertical fiber and identifies its value with the real supremum.

`optimal_split` applies finite support reduction at that top point. The represented actions are receiver best replies, and replacing their sender payoffs by the derived sender-preferred payoff can only increase the split value. `split_le_concavification`, proved for all finite splits independently of this optimization, bounds the improved value by the same hull maximum. These two inequalities force exact equality. Thus the apparently larger best-response hull has the same upper boundary as genuine sender-preferred finite experiment values. The dimensional bound `k ≤ Fintype.card Ω + 2` is the valid conservative bound for ambient `(Ω → ℝ) × ℝ`; it is not falsely advertised as sharp.

`optimal_signal` reconstructs the optimum and compares it against **every** `m : ℕ` and every `σ : Signal Ω m`. Each arbitrary competitor is converted to its Bayes-plausible split before applying the common hull upper bound. Hence the optimization is global over finite experiments of all cardinalities.

### Least concave majorant and gain

`concavification` is totalized off the simplex, but all economic majorant conclusions are correctly restricted to simplex beliefs. `concavification_concave` uses actual attained top points at arbitrary simplex beliefs, including boundary beliefs, and convexity of their hull to prove the concavity inequality. `concavification_majorizes` uses actual sender-preferred pairs. `concavification_le_majorant` quantifies over every real-valued function concave on the entire simplex with the derived payoff as a majorized function; finite Jensen and an attained optimal split prove minimality without regularity assumptions on the competitor. This is the actual least-concave-majorant property.

`persuasion_gain_iff` correctly characterizes strict gain using the no-information sender payoff at the prior and the attained concavification value. The first direction uses the bound for arbitrary finite signals; the reverse direction supplies an optimal finite signal.

### Scope and remaining verification

This snapshot covers the requested finite-signal existence and concavification chain from economic primitives, including bounded USC payoff and sender-preferred tie breaking. It does not claim all of the paper's later propositions, compact-state extensions, or a global measurable action selector. It also does not expose the straightforward-signal branch of Proposition 1 as a main theorem; any prose should specify the signal/splitting equivalence and optimal-value result actually proved.

A useful optional library clarification would equate `signalValue` with `∑ω∑s,p(ω)k(ω,s)v(a_s,ω)` for any sender-preferred action `a_s` at each message posterior. This follows directly from `mass_mul_posterior` and `senderPayoff_eq`. The current definition as posterior expected sender utility is already legitimate and this is not a mathematical blocker.

A source-text search of the five files found no `sorry`, `admit`, declared `axiom`, `unsafe`, `implemented_by`, or `extern`. This is not a substitute for the required compiler axiom audit of all authored constants. Examples, standalone comparator declarations, official preflight, hosted exact-source checks, and source/artifact digest reports were outside this implementation review and still require their respective evidence.

## Final candidate rereview

On 2026-10-03 UTC, reread the final five core files, the new `Examples.lean`, and standalone `Challenge.lean`, without running a heavy build. This final inspected snapshot supersedes the earlier five-file snapshot:

| File | Final inspected SHA-256 |
| --- | --- |
| `BayesianPersuasion/Primitives.lean` | `dc6f52410a206bff1d09a8e065ce8cb9805ef5e6b1fee584338d0c894d933ae6` |
| `BayesianPersuasion/Signals.lean` | `887dbe321d952e211ca24482f2679bdbb885562f6f703297a427700bdcfcdfd9` |
| `BayesianPersuasion/CompactHull.lean` | `506a87f48a85a495edd09df85a88b221025136862aaf54f0ed25b9f23d668f6a` |
| `BayesianPersuasion/Attainment.lean` | `9946e1407d2e511eaf6ce6402aeb32ab61299f30e64aa7f9a936da9928f88e1e` |
| `BayesianPersuasion/Theorems.lean` | `4fad7565be09c53ba38cbc92ace28c83e54d1250cb1cea7ee97ffbda8579f2ba` |
| `BayesianPersuasion/Examples.lean` | `9e80a285ad647aa2d5753e5065e0eda725a40c055cf0b4e11d985c6a1be5555f` |
| `Challenge.lean` | `4e293d7f7d83e04195bf5686021b2c6b28909cb0296fcb03480770222025ba1d` |

The final core retains the reviewed economic assumptions and proof chain. Explicit state and action universe parameters do not change mathematical scope. CompactHull now retains the Daniel Lyng portion copyright attribution as well as the immutable Econlib adaptation reference.

`Proof.signalValue_primitive` resolves the optional clarification identified earlier: for any sender-preferred receiver actions at message posteriors, it proves signal value is exactly the finite state/message expectation of the original sender utility. The calculation multiplies posterior expected utility by each message mass, uses the valid joint identity including null messages, and exchanges finite sums. The action-maximizer condition is available at every posterior by the proved existence theorem, rather than a new economic restriction. No measurable selector is needed for this finite message family. `Proof.noInformation_value` proves the constant one-message experiment has value exactly the sender payoff at the common prior; thus the gap theorem's baseline is supported by an actual experiment.

The prosecutor/judge example is nonvacuous: `prior_fullSupport` proves positivity for guilt prior `3/10`; `prior_tieRule`, `innocent_tieRule`, and `indifferent_tieRule` verify receiver/sender optimization from utilities; the latter correctly favors conviction at guilt probability `1/2`. The split with masses `2/5` and `3/5` at posterior guilt probabilities `0` and `1/2` is proved Bayes plausible. `prosecutor_strict_gain` constructs an actual two-message conditional experiment, with value `3/5` and strict gain over the proved zero default payoff. It does not assert this example's numerical global upper bound or formal discontinuity theorem, which have not been proved here. Its positive-gain conclusion suffices to establish nonvacuity.

`interval_action_optimum` uses the actual compact continuum action type `Icc (0 : ℝ) 1`, squared-loss receiver utility, and linear sender utility. It verifies utility continuity and instantiates the all-cardinality global-optimum theorem with at most four messages at the same full-support two-state prior. It proves optimum existence and comparison with every finite experiment, rather than a computed numerical optimum; descriptions should keep that distinction.

Standalone `Challenge.lean` reproduces genuine probability, utility, best-response, posterior, and convex-hull definitions and the same four reviewed main research contracts. Its explicit scope note accurately excludes the straightforward-recommendation branch and compact-state extension, and identifies the conservative support bound. Its four `sorry` placeholders are confined to the standalone challenge interface; they are not evidence of a proof and must remain separate from admission-free library/Solution claims. The small posterior-normalization support proof in Challenge is substantive rather than an assumed probability-property certificate. Exact comparator identity and official acceptance are reported by the implementation lead and belong to their separate evidence.

**Final mathematical verdict: passed; no mathematical or semantic blocker identified in the final inspected files.** All central regularity, compactness, finite support, attainment, and least-majorant properties are proved from the utility primitives. A repeated source scan of all six library files found no admissions, custom axioms, unsafe definitions, or implementation overrides. This read-only mathematical review does not replace compiler axiom audits, exact comparator reports, final source matching, or hosted proof/preflight/render gates; those must be linked separately for the published revision.
