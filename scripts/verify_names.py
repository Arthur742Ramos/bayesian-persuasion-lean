#!/usr/bin/env python3
"""Elaborate the exact Comparator names and assert that definition_names are definitions."""
import json
from pathlib import Path
import subprocess
import tempfile
root=Path(__file__).resolve().parents[1]
cfg=json.loads((root/'comparator.json').read_text())
for module in (cfg['challenge_module'],cfg['solution_module']):
    src=['module',f'public import {module}','import Lean','open Lean Elab Command']
    for name in cfg['theorem_names']+cfg['definition_names']:
        src.append('#check @'+name)
    for name in cfg['definition_names']:
        src+=['#eval show CommandElabM Unit from do','  let env ← getEnv',
              f'  match env.find? `{name} with',
              f'  | some (.defnInfo _) => logInfo "DEF-OK {name}"',
              f'  | _ => throwError "NOT-A-DEF {name}"']
    with tempfile.TemporaryDirectory(prefix='kg-names-') as tmp:
        path=Path(tmp)/'CheckNames.lean'
        path.write_text('\n'.join(src)+'\n')
        subprocess.run(['lake','env','lean',str(path)],cwd=root,check=True)
