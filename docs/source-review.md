# Independent exact-source and prior-art review

Reviewed 2026-10-03 UTC. This is a source-and-scope review, not a completed audit of a Lean implementation. The cited Econlib files were inspected as source; they were not built or kernel-replayed in this review.

## Primary economic source

Emir Kamenica and Matthew Gentzkow, “Bayesian Persuasion,” *American Economic Review* 101(6), 2011, pp. 2590–2615, DOI [10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590). [Author-hosted PDF](https://web.stanford.edu/~gentzkow/research/BayesianPersuasion.pdf), inspected pp. 2593–2597 and Appendix A, p. 2610.

The model has a finite state space, compact action space, continuous receiver and sender utilities, and a shared interior prior. Signals have finite realization spaces. The receiver maximizes expected utility; among best responses she maximizes the sender’s expected utility. The paper additionally assumes at least two actions and that each action is optimal somewhere. Proposition 1 connects signals, straightforward recommendations, and Bayes-plausible posterior distributions. Footnote 4 explicitly qualifies direct realization by finite support. Corollary 2 identifies the optimal value with concavification and characterizes strict gains over no information. Page 2596 states that sender-favored ties yield an upper semicontinuous induced payoff and optimal-signal existence. Appendix A uses Carathéodory reduction and the likelihood formula `π(s | ω) = τ(s) μ_s(ω) / μ₀(ω)`. The paper’s binary prosecutor example has a discontinuous threshold payoff. Compact metric state extensions are outside this task’s main-paper scope.

The requested nonempty compact **metric** action space is an explicit specialization of the paper’s compact action space. Omitting the two-action and action-relevance restrictions relaxes assumptions that are unnecessary for the targeted core claims; this should be disclosed rather than attributed verbatim to the paper. A development omitting straightforward recommendation equivalence should describe its target as the signal/splitting part of Proposition 1 plus Corollary 2 and existence, rather than all of Proposition 1.

## Independent mathematical contract checks

These are reviewer-derived proof obligations for a faithful implementation:

- Expected receiver and sender utility must be defined from state weights and primitive utilities. Compactness and continuity should prove receiver-best-response existence and the existence of a sender-maximizing best response. Supplying an arbitrary posterior payoff or assuming an optimal response does not fulfill this economic scope.
- The induced sender payoff should be the maximum sender value over the receiver’s best-response set. Prove boundedness and upper semicontinuity from primitives; continuity is generally false. A closed best-response graph plus compact actions supports this proof. The action selector itself need not be continuous.
- A finite signal is a stochastic likelihood row for every state, including zero-prior states if boundary priors are allowed. Bayes posteriors are determined only at messages with positive marginal probability. Use an explicitly documented fallback belief at null messages, whose contribution to payoff is zero. Do not assert a prescribed posterior there.
- A splitting is a finite list of posterior distributions with nonnegative weights summing to one and mean equal to the prior. Zero-weight entries are harmless padding and are not part of probabilistic support. Duplicate entries are aggregated if the result is described as a posterior distribution.
- A finite-signal characterization covers finite splittings directly. An arbitrary measure claim additionally needs Borel measurability, integrability, a barycenter definition, and a proved finite reduction. Bounded USC payoff gives measurability and integrability, but does not alone prove that reduction.
- For support reduction that preserves both prior and payoff, augment posterior coordinates by payoff. With `n` states the belief affine dimension is `n − 1`; adding payoff gives dimension `n`, so Carathéodory gives at most `n + 1` positive atoms. Keeping all `n` state coordinates without affine reduction gives a safe `n + 2` bound. Do not report a sharper support bound than is proved.
- An USC function’s graph need not be closed. Optimal finite attainment can use a bounded truncated hypograph or optimization over a proved fixed support bound. In the latter route, varying zero weights require boundedness when proving USC of `weight × payoff`.
- Least concave majorant requires an actual concavity proof, domination, and minimality against every concave majorant on the simplex. Merely naming a supremum “concave closure” does not establish that contract. A one-point splitting supplies the no-information baseline.

## Precise formalized prior art

Daniel Lyng’s **Econlib** revision [`003655ccf010cdf44c4f67d6675167b54ce0e9df`](https://github.com/danlyng/Econlib/commit/003655ccf010cdf44c4f67d6675167b54ce0e9df), authored 2026-07-09 01:37:01 UTC and committed 01:38:11 UTC (GitHub commit API verified). All inspected Lean files identify Daniel Lyng as author and carry an Apache-2.0 notice; the exact revision’s [LICENSE](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/LICENSE) was fetched. Any reused code must preserve its source attribution and applicable license notices. The review itself does not authorize dropping notices or relabeling borrowed source.

| Inspected immutable source | Exact declarations and scope |
| --- | --- |
| [Finite/Basic.lean](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/MechanismDesign/InformationDesign/Persuasion/Finite/Basic.lean) | `SignalStructure`, `signalLaw`, `BayesPlausible`, `SignalStructure.bayesPlausible`, `concaveClosure`, `expectedSenderPayoff`, `expectedSenderPayoff_mem_achievableSet`. The payoff argument is an arbitrary function on `FinDist (Fin n)`; `concaveClosure` is defined as the supremum over finite mean-preserving splittings. |
| [Finite/Splitting.lean](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/MechanismDesign/InformationDesign/Persuasion/Finite/Splitting.lean) | `signalFromSplitting`, `signalMarginal_signalFromSplitting`, `posterior_signalFromSplitting`, `exists_signal_from_splitting`. Reconstruction works for arbitrary priors, assigning an irrelevant valid likelihood row at a zero-prior state. Prescribed posteriors are recovered on positive-weight messages. |
| [Finite/Caratheodory.lean](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/MechanismDesign/InformationDesign/Persuasion/Finite/Caratheodory.lean) | `caratheodory_simplex`, `concavification_finite`, `achievable_with_bounded_signals`. Every already-finite Bayes-plausible splitting is reduced to `Fin (n + 1)` with the same mean and arbitrary supplied payoff; zero padding is allowed. Its “general” splitting set quantifies over a natural-number signal count, not arbitrary probability measures. It does not by itself prove optimal attainment. |
| [Duality/Basic.lean](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/MechanismDesign/InformationDesign/Persuasion/Duality/Basic.lean) | `IsBayesPlausible` uses bounded continuous test-function barycenters. `primalValue` integrates supplied payoff; `concaveClosure` is its supremum over all feasible posterior probability measures. |
| [Duality/PrimalAttainment.lean](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/MechanismDesign/InformationDesign/Persuasion/Duality/PrimalAttainment.lean) | `feasiblePrimal_isCompact` and `primalAttainment` already prove abstract optimal attainment. Assumptions are compact Hausdorff second-countable pseudometric states with the Borel sigma algebra, an absolute uniform bound on the supplied payoff, and USC. The conclusion is a Bayes-plausible posterior probability measure attaining `concaveClosure`. The proof establishes payoff measurability and integrability. It does not derive the supplied payoff from receiver/sender utility primitives or prove finite support here. Its cited mathematical source is Dworczak–Kolotilin (2024), Theorem 2, first conjunct. |
| [Finite/StepFunction.lean](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/MechanismDesign/InformationDesign/Persuasion/Finite/StepFunction.lean) | `stepOptimalSignal_payoff`, `binarySignal_achieves_stepClosure`, and `stepConcaveClosure_eq` include a binary threshold/prosecutor-style optimal signal and concave-closure equality. This is additional concrete prior art, not the general compact-action economic theorem. |

A responsible scope description is: an end-to-end finite-state, compact-metric-action theorem deriving optimal signal existence and concavification from economic utilities and sender-favored receiver best responses. No “first formalization” claim is supported. In particular, do not describe Econlib as lacking attainment. An earlier team-reported public registry search found no persuasion matches on 2026-10-03 UTC; this reviewer did not repeat that search, and its API limitation prevents treating it as an exhaustive novelty result.

## Pinned official verification-source check

GitHub’s `PalomarRegistry/PalomarSubmission` commit API and `main` endpoint both returned [`65f0154ed776cd26c224254aa57b379137f28b0d`](https://github.com/PalomarRegistry/PalomarSubmission/commit/65f0154ed776cd26c224254aa57b379137f28b0d) on the review date. Committer time: 2026-09-28 05:27:38 UTC. Exact pinned workflow and scripts were downloaded and inspected. The historical local `task-4/pipeline` is a non-Git unpacked tree; the remote immutable bytes are the authoritative evidence.

- Reusable `.github/workflows/submission.yml` accepts `mode: full` and `pipeline_commit`; the requested `uses` pin and `pipeline_commit` must be the same full SHA. Its profile catalogue default is `palomar-standard-v1`.
- `scripts/submission_contract.py` validates proof request IDs with `^[0-9a-z]{12}$`. Its actual parser should be called before launching CI, not replaced by a local regex-only approximation.
- `scripts/verify_submission.py` has a compact Challenge cap of **1000 lines and 100 KiB**. The commit title’s mention of a 10,000-line cap does not override this explicitly enforced Challenge limit. It permits only `propext`, `Quot.sound`, and `Classical.choice`, and requires Lean, NanoDa, and con-ron tooling.
- `scripts/render_challenge.py` resolves the official Verso release tag for the submitted toolchain to a full commit; a stable positive patch may fall back only to patch zero on the same release line. It builds a trusted core-notation audit executable away from candidate-writable state and runs sanitizer stages. It limits each rendered file to **8 MiB**, total rendered bytes to 25 MiB, and file count to 2000. Rendering uses its own 32-lowercase-hex request ID contract, distinct from proof request IDs.
- `verification-profile.json` records `palomar-standard-v1`, a 19,800-second execution budget, 350-minute job timeout, and a toolchain floor of `v4.35.0-rc2`.

No build, publication, hosted gate, or implementation audit is certified by this source review.

## Downloaded evidence digests

The snapshots below are local review inputs, not authored theorem-library source. The paper download is an evidence copy; it need not be redistributed in the published package. Immutable URLs and digests suffice for publication.

| Local input | SHA-256 |
| --- | --- |
| `evidence/primary/BayesianPersuasion.pdf` | `64ddd2908c8da90c8e7551ec1ad74b5c17bd10816f1773490835f07a63af8591` |
| `evidence/prior-art/Caratheodory.lean` | `ade3ee2796caf7928dd495255e42fde5503f2e98db230b60767c5b29113d560b` |
| `evidence/prior-art/PrimalAttainment.lean` | `7913f134e9e5413d9ad6c417456f524a2eb9771508ad1700a18b241dae738d86` |
| `evidence/prior-art/Splitting.lean` | `da6dd58b528be6ce5bccd158521c94becd9342e7c7c0ab089098d28f0a64c12a` |
| `evidence/prior-art/FiniteBasic.lean` | `3f78fb0df2131033ab993c2f4888f94de2ca732468ebc9b80deafb8e67a42167` |
| `evidence/prior-art/DualityBasic.lean` | `65d51bf075e7bca05ec5e72631370d0827b3f6bba089d5a904f57993d989518f` |
| `evidence/prior-art/StepFunction.lean` | `6151fef0858c21220af7f56757dcd8d8e98f35d4e68951506b345d3171859b50` |
| `evidence/primary/submission.yml` | `a116f9a84bf5287e8ed9cda55b98d3023c3c4215fe084b61ce7988e9bc9dc2f0` |
| `evidence/primary/submission_contract.py` | `724f82211ef702e2d1b4e5012183e532bd8f8ba03ba676022e4722a420c5be75` |
| `evidence/primary/render_challenge.py` | `9f702f736c87133a9535aa19b89e073ae84c45edf8b165d417bf34709232f9c1` |
| `evidence/primary/verify_submission.py` | `1c1b4b7c8319bd31960d4484e747d23eb6664d6bf7e4e901bc724aacf34f282d` |
| `evidence/primary/verification-profile.json` | `94fcd7906a1b6c076c0036d742e1c5add8625e49bb474818ec8924576dbf0caa` |
| `evidence/primary/render-challenge.yml` | `d89c07650b3ec0843fc7e041c04a14efcacf01cdb53d750a3d960e377a631736` |


## Candidate core review — 2026-10-03 UTC

Reviewed the five files in `bayesian-persuasion-lean/BayesianPersuasion/` listed below and the direct Mathlib dependency pin `065356127b1dc0016f66b7283ce0ce2c4055aa55`. This was a read-only independent source review; the parent reported the core compiled. This reviewer did not run another build, Comparator, axiom audit, or hosted verification.

**Verdict: the core is faithful to the specified economic scope, subject to the attribution and wording repairs below.** No mathematical scope blocker was found in the inspected definitions and proofs. Challenge, Solution, examples, metadata, and workflow packaging were still being prepared and are not certified here.

`expected` is the finite-state utility expectation. `BestReply` maximizes receiver utility; `SenderPreferred` maximizes sender utility over the receiver-optimal set. `senderPayoff` is defined from these economic primitives, with receiver and tie-break existence proved by compact maximization. `economic_payoff_regular` proves that this supremum equals a chosen sender-preferred action value, is uniformly bounded in absolute value, and is USC. It does not assume a supplied payoff regularity certificate.

`Signal Ω n` gives normalized likelihood rows at every state. `posteriorVector` uses the prior as a documented null-message fallback; `mass_mul_posterior` proves the joint identity in both the positive and zero cases. `finite_signal_splitting` requires `FullSupport p`, recovers prescribed beliefs only at nonzero weights, preserves joint state/message weights, and preserves the economic payoff. Its converse derives Bayes plausibility from the joint identity. Every arbitrary finite signal also supplies its splitting through `signalWeights`, `signalPosterior`, and `Proof.signal_bayesPlausible`. The development does not claim realization for boundary priors or arbitrary posterior probability measures.

`bestReplyPayoffs` includes outcome pairs from **all receiver best replies**, rather than only the discontinuous tie-selected payoff graph. This set is compact as the continuous image of a closed best-reply graph in compact belief/action space. Its convex hull is compact by finite-dimensional Carathéodory and fixed-support padding. A maximal fiber is therefore attained. `optimal_split` upgrades its finitely many receiver-best-response values to sender-favored tie values; the existing hull upper bound forces equality. This proves attainment without assuming USC or attainment as hypotheses. The support bound is explicitly `k ≤ Fintype.card Ω + 2`, consistent with the unreduced ambient dimension. It is conservative and is not misidentified as Econlib’s `n + 1` bound.

The main `optimal_information_and_concavification` binds finite nonempty states, nonempty compact metric actions, continuity of each state’s primitive utilities, and a full-support prior. It proves an actual finite signal attaining `concavification`, dominating every finite signal, together with concavity, domination of the induced sender payoff, and pointwise minimality among all concave majorants on the simplex. Thus the definition via all-best-reply outcomes has the same least-majorant interpretation as the sender-favored payoff. `persuasion_gain_iff` proves the strict gap criterion for finite signals. Measurability is a separate USC consequence; no arbitrary-measure objective or integrability theorem is claimed.

Required release repairs/checks:

1. Retain Daniel Lyng’s original copyright attribution for the adapted reindexing/padding portions of `CompactHull.lean`, in addition to its existing immutable Econlib source citation and Apache-2.0 notice. The inspected header credits the source and author but lists only the new authors’ copyright. Suggested added line: `Portions Copyright (c) 2026 Daniel Lyng.` This is an attribution correction, not a mathematical change.
2. Public abstracts must explicitly say **full-support common prior**, since finite optimal-signal existence is proved with `hp : FullSupport p`. The current short `Theorems.lean` module abstract omits this condition; its theorem binder contains it. The signal/splitting theorem doc should likewise expose the full-support restriction rather than appear to cover all priors.
3. Describe the result as the finite signal/splitting characterization plus concavification and existence, or explicitly the signal/splitting part of Proposition 1 and Corollary 2. Do not advertise the omitted straightforward-recommendation branch as proved.
4. Keep the stated support bound at `|Ω| + 2`; do not claim `|Ω| + 1` or an optimal minimal bound.
5. Complete the separate Challenge exact-definition comparison, admission/axiom audit, examples, and hosted gate review before treating the package as verified for release.

No first-formalization claim is justified. The relationship to Econlib is more concrete than independent background: `CompactHull.lean` explicitly adapts its reindexing and padding arguments. Other economic source distinctions and the existing abstract attainment theorem remain as recorded above.

| Inspected core candidate file | SHA-256 at review |
| --- | --- |
| `Primitives.lean` | `8e9df44c6352139c853ae111fc3bccd3fde4268fa60596293389bb23d68ac271` |
| `Signals.lean` | `08075bd67275afe24e974a8fdf6435ea54f382f837ef89cbcbeca5e29c0490fd` |
| `CompactHull.lean` | `506a87f48a85a495edd09df85a88b221025136862aaf54f0ed25b9f23d668f6a` |
| `Attainment.lean` | `0c807cb24cc1f16efc9bfeba4da24027e1adadf076c9763c15db57ac645c9d82` |
| `Theorems.lean` | `a55e3050ba8714ff0d0cd5bdfac4812722cf13c36ca0be980141e2f3885ecd7a` |


## Final standalone Challenge and packaging review — 2026-10-03 UTC

**Source-scope and pinned-workflow verdict: pass.** The earlier copyright and full-support disclosure requests are repaired. This review does not substitute for the official parser, final build/axiom checks, downloaded hosted reports, independent kernels, or render artifact verification.

Reviewed the final standalone `Challenge.lean`, `Solution.lean`, Comparator configuration, formalization metadata, README, author/license records, examples, and proof/render workflows. At this snapshot the Challenge is 168 lines and 7474 UTF-8 bytes, below the official 1000-line/100-KiB cap. It imports Mathlib only. All 17 `definition_names` name actual definitions/abbreviations present in the statement surface. They expose probability vectors, utilities, best responses, sender tie preferences, signal probabilities, null-message posterior convention, economic outcome hull, values, and the no-information experiment. The four listed research theorem names are actual declarations and are the only four statement holes. Auxiliary normalization proofs support the subtype-valued posterior definition; they do not embed the economic existence/attainment proof into the compact Challenge. `Solution.lean` imports the admission-free proved `BayesianPersuasion.Theorems` library. Parent-reported local official Comparator result: “Your solution is okay!”; this reviewer inspected the sources and configuration without rerunning it.

The main statements and their explanatory metadata preserve the exact assumptions: finite nonempty states, nonempty compact metric actions, continuous statewise utility primitives, and full-support common prior for signal reconstruction/attainment. Sender payoff regularity is derived. Null-message posterior recovery is restricted to nonzero message weights. The support claim is the proved conservative `card Ω + 2`. Concavification/majorant statements range over the entire simplex and do not require full support of the comparison belief. No arbitrary-measure signal or integration theorem is advertised. The omission of straightforward-recommendation equivalence and the compact-state extension is explicit. Dated Econlib prior art, abstract attainment, the adaptation relationship, and Apache-2.0 attribution are accurately acknowledged. `CompactHull.lean` now retains “Portions Copyright (c) 2026 Daniel Lyng.”

The newly inspected `Proof.signalValue_primitive` equates the posterior-value objective to the state/message expectation of primitive sender utility for sender-preferred receiver actions. `Proof.noInformation_value` proves the constant one-message signal has value `senderPayoff` at the prior. These support the README’s economic payoff and no-information descriptions. Examples explicitly witness the prosecutor’s 3/10 prior, 2/5 and 3/5 posterior weights, 0 and 1/2 guilt posteriors, 3/5 signal payoff, and strict gain over zero. A separate interval-action instantiation uses compact continuum actions. The examples do not claim to prove a unique optimal prosecutor signal or a sharper signal support theorem.

`proof.yml` uses official reusable `submission.yml@65f0154ed776cd26c224254aa57b379137f28b0d`, sets the same full `pipeline_commit`, and selects `mode: full` and `execution_profile: palomar-standard-v1`. It passes the exact requested source commit and a twelve-lowercase-alphanumeric request ID input to the official parser. It is predictive and does not perform registry intake or registration.

Compared `render.yml` by textual diff against the downloaded official `.github/workflows/render-challenge.yml` at that same immutable commit. The only changes are the predictive workflow name, exact trusted pipeline checkout references, the explicit `repository: PalomarRegistry/PalomarSubmission` on the renderer checkout, and exact `--renderer-commit`. Both the profile resolver and renderer check out **PalomarSubmission**, never the candidate repository. The latter uses `path: pipeline`, from which the trusted `render_challenge` module and pinned hashed requirements run. Candidate source is fetched and bound only by official `prepare`, using supplied source commit and Challenge SHA-256. Bubblewrap, pinned elan, exact official Verso selection, trusted core-notation audit, sanitizer, artifact upload, and final `status == pass` enforcement remain intact. The source commit itself is not substituted for the renderer commit. Proof and render request IDs remain correctly distinct.

Minor bibliographic wording clarification: README and the primary-source metadata note use “no redundant actions.” The paper’s exact setup restriction is that **each action is receiver-optimal at some belief** (weak optimality). Prefer that exact wording; this does not change the Lean contract or the valid relaxation to nonempty actions. No mathematical or workflow blocker was found.

Final inspected source snapshot:

| Candidate file | SHA-256 |
| --- | --- |
| `Challenge.lean` | `4e293d7f7d83e04195bf5686021b2c6b28909cb0296fcb03480770222025ba1d` |
| `Solution.lean` | `9607ef0481dcb0095af02d141705e1bdf63fbb443109e41653d380af911aaee1` |
| `comparator.json` | `8aacfb20da97fcef829f3f0dfd091cd758a571d1a5f51d0839fd8324f70e10bc` |
| `formalization.yaml` | `2c99e44f1dac58df8b09c7a2f02933c7ef1bd27ac24a4e36ded652409d2ab485` |
| `README.md` | `cd29a34a8f32859bae1dd62518201231bdd4382f950836dca18144cceca21e31` |
| `.github/workflows/proof.yml` | `da9635ea8f070535b82c4f0505d1f0eb8ccdf3a6baabe9301562fc059103112c` |
| `.github/workflows/render.yml` | `82899ad9801fcc426596767b3052656d9c98597bc0afa808019fb054fa0e61bf` |
| `BayesianPersuasion/CompactHull.lean` | `506a87f48a85a495edd09df85a88b221025136862aaf54f0ed25b9f23d668f6a` |
| `BayesianPersuasion/Attainment.lean` | `9946e1407d2e511eaf6ce6402aeb32ab61299f30e64aa7f9a936da9928f88e1e` |
| `BayesianPersuasion/Signals.lean` | `887dbe321d952e211ca24482f2679bdbb885562f6f703297a427700bdcfcdfd9` |
| `BayesianPersuasion/Primitives.lean` | `dc6f52410a206bff1d09a8e065ce8cb9805ef5e6b1fee584338d0c894d933ae6` |
| `BayesianPersuasion/Theorems.lean` | `4fad7565be09c53ba38cbc92ace28c83e54d1250cb1cea7ee97ffbda8579f2ba` |
| `BayesianPersuasion/Examples.lean` | `9e80a285ad647aa2d5753e5065e0eda725a40c055cf0b4e11d985c6a1be5555f` |
| `scripts/Audit.lean` | `20a725edf31ed3c01e2a242567b617320a95afdfbe030cdada64bfb97f00573b` |
| `LICENSE` | `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` |
| `lakefile.toml` | `e62c95f6b106a764de16588f5577b1e93a213c521aa1183294987b516c20a582` |
| `lake-manifest.json` | `e132b1e103b8555ad399f8c5d6c132a348478d9e28c7eaca4bb9bc10059f6cc2` |
| `lean-toolchain` | `8dc8d6f560141069d9073e370611716ef77ada0da8ffa37e2149f44b2e63ac7a` |


## Final Solution import confirmation — 2026-10-03 UTC

Read-only confirmation: `Solution.lean` now publicly imports the `BayesianPersuasion` root module, which publicly imports both `BayesianPersuasion.Theorems` and `BayesianPersuasion.Examples`. Thus the hosted Solution build includes the nonvacuous examples. The import change adds example declarations to the exported environment; it does not redefine or change the four selected research contracts or their 17 shared economic definitions. Comparator configuration is unchanged. The four research contracts still come from `Theorems.lean`.

The primary setup wording correction is present in README and formalization metadata: each action is receiver-optimal at some belief. This resolves the earlier bibliographic wording comment. Parent reports another successful official Comparator and Lean/NanoDa/con-ron run plus module-origin audit of 121 authored constants; this reviewer did not rerun those checks. The source-scope/pinned-workflow pass stands; final hosted report and artifact inspection remain separate requirements.

| Final confirmation file | SHA-256 |
| --- | --- |
| `Solution.lean` | `371a9d2d625a5e2f0354d3f5ab2752b0efd921975bceaebb2a6f115e9ca4d218` |
| `BayesianPersuasion.lean` | `5cd29e0c9cacc356186f9bf2a61665918a9684a6fdb2b541bb19bb6dea64e8b0` |
| `README.md` | `b6eeddb1c37b9aa8ca52f8842be61ec8d44888b164819a2dd16a0107b2ccee52` |
| `formalization.yaml` | `219abad34b2999476ad95631d6faf7fecb8d9654995d160b78405b19f9153222` |
| `comparator.json` | `8aacfb20da97fcef829f3f0dfd091cd758a571d1a5f51d0839fd8324f70e10bc` |
