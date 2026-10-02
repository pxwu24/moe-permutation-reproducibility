#!/usr/bin/env python3
"""Generate the numbered result guide and complete local import closures."""
from __future__ import annotations
import argparse
import json
import re
from pathlib import Path
from verify_lean import ROOT, IMPORT, source_modules

KINDS = {'II.2':'Lemma', 'II.3':'Lemma', 'III.1':'Theorem', 'III.2':'Corollary',
         'III.3':'Lemma', 'III.4':'Lemma', 'IV.1':'Theorem', 'IV.2':'Corollary',
         'V.1':'Theorem', 'V.2':'Proposition', 'I.1':'Theorem', 'VI.1':'Proposition',
         'A.1':'Lemma', 'A.2':'Lemma', 'A.3':'Proposition', 'A.4':'Proposition',
         'B.1':'Proposition', 'B.2':'Proposition', 'C.1':'Lemma', 'C.2':'Lemma'}


def generate():
    data = json.loads((ROOT / 'RESULTS.json').read_text())
    modules = source_modules()
    artifacts, index, declarations = {}, [], []
    for row in data['results']:
        seen = set()
        def visit(module):
            if module in seen:
                return
            if module not in modules:
                raise ValueError('Unknown local module ' + module)
            seen.add(module)
            for dep in IMPORT.findall(modules[module].read_text()):
                if dep in modules:
                    visit(dep)
        for name in row['entry_modules']:
            visit(name)
        related = [{'module': m, 'path': str(modules[m].relative_to(ROOT))}
                   for m in sorted(seen)]
        number, title = row['number'], row['title']
        filename = number.replace('.', '_') + '.md'
        kind = KINDS[number]
        status = {'complete': 'Complete',
                  'complete_under_permitted_black_box': 'Complete under the permitted block-modified strong-convergence input'
                 }.get(row['status'], 'Components checked; full statement unfinished')
        body = f'# {kind} {number}: {title}\n\n**Status: {status}.**\n\n'
        body += row['proved_scope'] + '\n\n'
        body += '## Check this result\n\nFirst run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root. '
        body += 'Then, from `lean_arXiv_2607.15210/`, run:\n\n```sh\n'
        body += "cat > InspectResult.lean <<'LEAN'\nimport AllProofs\n\n"
        for decl in row['declarations']:
            body += '#check ' + decl + '\n#print axioms ' + decl + '\n'
            declarations.append(decl)
        body += 'LEAN\nlake env lean InspectResult.lean\nrm InspectResult.lean\n```\n\n'
        body += 'The displayed hypotheses are part of the checked statement. '
        body += 'A theorem conditional on an intermediate assertion does not verify that assertion.\n\n'
        body += '## Entry files\n\n'
        for module in row['entry_modules']:
            path = modules[module].relative_to(ROOT).as_posix()
            body += f'- [{module}](../{path})\n'
        body += '\n## All related Lean files\n\n'
        body += 'This is the complete transitive local import closure of the entry files. '
        body += 'Mathlib dependencies are pinned in `lake-manifest.json`.\n\n'
        for item in related:
            body += f'- [{item["path"]}](../{item["path"]})\n'
        body += '\n## Assumptions and dependencies\n\n'
        body += '\n'.join('- ' + x for x in row['paper_assumptions']) + '\n'
        if row['paper_dependencies']:
            body += '\nPaper dependencies: ' + ', '.join(row['paper_dependencies']) + '.\n'
        if row['missing_for_paper_statement']:
            body += '\n## Remaining proof obligations\n\n'
            body += '\n'.join('- ' + x for x in row['missing_for_paper_statement']) + '\n'
        if row['python_files']:
            body += '\n## Python checks\n\n'
            for path in row['python_files']:
                if not (ROOT / path).is_file():
                    raise ValueError('Missing Python file ' + path)
                body += f'- [{Path(path).name}](../{path})\n'
            body += '\nThe exact rational certificate is a certificate of its scalar inequalities; '
            body += 'the other numerical checks are cross-checks, not universal proofs.\n'
        artifacts[ROOT / 'results' / filename] = body
        index.append({'number': number, 'status': row['status'],
                      'declarations': row['declarations'], 'local_import_closure': related})
    artifacts[ROOT / 'verification/result_sources.json'] = json.dumps(index, indent=2) + '\n'
    readme = (ROOT / 'README.md').read_text()
    table = '| Paper result | Checked result | Status |\n| --- | --- | --- |\n'
    for row in data['results']:
        status = {'complete': 'Complete',
                  'complete_under_permitted_black_box': 'Complete under the permitted convergence theorem'
                 }.get(row['status'], 'Unfinished')
        number = row['number']
        table += (f"| [{KINDS[number]} {number}](results/{number.replace('.', '_')}.md) | "
                  f"{row['title']} | {status} |\n")
    readme = re.sub(r'<!-- RESULT_TABLE_START -->.*?<!-- RESULT_TABLE_END -->',
                    '<!-- RESULT_TABLE_START -->\n' + table + '<!-- RESULT_TABLE_END -->',
                    readme, flags=re.S)
    artifacts[ROOT / 'README.md'] = readme
    artifacts[ROOT / 'ResultChecks.lean'] = ('import AllProofs\n\n'
        + '\n'.join('#check ' + name for name in dict.fromkeys(declarations)) + '\n')
    return artifacts


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path, content in generate().items():
        if args.check:
            if not path.is_file() or path.read_text() != content:
                raise SystemExit('Result index is stale: ' + str(path.relative_to(ROOT)))
        else:
            path.parent.mkdir(exist_ok=True)
            path.write_text(content)
    print('Numbered result index and complete import closures checked.' if args.check else
          'Numbered result index and complete import closures generated.')
