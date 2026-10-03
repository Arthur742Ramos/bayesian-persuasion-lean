#!/usr/bin/env python3
"""Build the standalone statement from exact shared definitions and contracts."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[1]
p=(root/'BayesianPersuasion/Primitives.lean').read_text()
s=(root/'BayesianPersuasion/Signals.lean').read_text()
a=(root/'BayesianPersuasion/Attainment.lean').read_text()
t=(root/'BayesianPersuasion/Theorems.lean').read_text()
header='''/-
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
'''
primitives=p.split('namespace BayesianPersuasion\n',1)[1].split('namespace Proof',1)[0]
signals=s.split('variable {Ω : Type uΩ} [Fintype Ω]\n',1)[1].split('/-- Realization of a splitting.',1)[0]
nonneg=s[s.index('theorem signalMass_nonneg'):s.index('theorem signalMass_sum')]
normal=s[s.index('theorem posteriorVector_isBelief'):s.index('\nend Proof')]
poster=s[s.index('noncomputable def signalPosterior'):s.index('\nnamespace Proof\n',s.index('noncomputable def signalPosterior'))]
values=a.split('variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]\n',1)[1].split('\nnamespace Proof',1)[0]
main=t.split('variable {Ω : Type uΩ} {A : Type uA}',1)[1].split('\nnamespace Proof',1)[0]
main='variable {Ω : Type uΩ} {A : Type uA}'+main
pattern=r'(theorem [\s\S]*?)(:= by[\s\S]*?|:=\n[\s\S]*?)(?=\n(?:include hu hv in\n)?/--|\Z)'
main=re.sub(pattern,lambda m:m.group(1)+':= by\n  sorry\n',main)
result=header+primitives+signals+'namespace Proof\n\n'+nonneg+normal+'\nend Proof\n\n'+poster+'section ValueDefinitions\nvariable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]\n'+values+'\nend ValueDefinitions\n'+main+'\nend BayesianPersuasion\n'
(root/'Challenge.lean').write_text(result)
print(f'Challenge: {len(result.splitlines())} lines, {len(result.encode())} bytes')
