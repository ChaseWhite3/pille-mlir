#!/usr/bin/env python3
"""Build the fixture of what the native plugin made of each lowering request, from comparison records.

  fixture.py OUT.json RECORDS_DIR...
"""
import json, re, sys, hashlib
from pathlib import Path

KNOWN = {
    'json': "the JSON reader's own words for malformed text follow the shared prefix, and the two readers word them differently",
    'effects': "a hand-written manifest models a registered operation with memory effects; the text of a module does not say which operations have them, and no operation a dialect declares through IRDL does",
}

def message(error):
    found = re.search(r'error: (.*)', error)
    return found.group(1) if found else error

def sha(text): return hashlib.sha256(text.encode()).hexdigest()

modules, index, requests, seen = [], {}, [], set()
for directory in sys.argv[2:]:
    for path in sorted(Path(directory).glob('*.json')):
        record = json.loads(path.read_text())
        key = (record['ir'], record['irdl'], record['manifest'])
        if key in seen: continue
        seen.add(key)
        p, r = record['plugin'], record['rhombus']
        if 'error' in p and 'no SMT query plugin was selected' in p['error']: continue   # a test with the plugin deselected
        module = index.setdefault(key[:2], len(index))
        if module == len(modules): modules.append(dict(ir=record['ir'], irdl=record['irdl']))
        entry = dict(module=module, manifest=record['manifest'])
        if 'error' in p:
            entry['plugin'] = dict(refused=message(p['error']))
            if message(r['error']) != message(p['error']):
                entry['lowering'] = dict(refused=message(r['error']))
                entry['differs_because'] = KNOWN['json'] if 'malformed SMT query manifest: ' in message(p['error']) else KNOWN['effects']
        else:
            assert p['verified'] == r['verified'] and p['smtlib'] == r['smtlib'], path
            entry['plugin'] = dict(mlir_sha256=sha(p['verified']), smtlib_sha256=sha(p['smtlib']),
                                   questions=p['smtlib'].count('(check-sat)'))
        requests.append(entry)
out = dict(
    about=("What pille/mlir's native SMT query plugin (pille/mlir/native/smt-query-plugin.cpp, since removed) made of each "
           "lowering request, recorded on 2026-11-14 with MLIR 23.1.5 before it was removed: a refusal's message, or the "
           "SHA-256 of the verified SMT module's text and of its exported SMT-LIB. The requests are every lowering the "
           "package's tests asked for on that day, a sweep of every refusal a manifest or a verified module can reach, "
           "and a module whose unselected operations are awkward to pass over. smt-lowering.rkt holds the Rhombus "
           "lowering to these. Never regenerate this file: the plugin that wrote it is gone."),
    modules=modules, requests=requests)
Path(sys.argv[1]).write_text(json.dumps(out, indent=0, sort_keys=True) + '\n')
refused = sum('refused' in e['plugin'] for e in requests)
print(len(modules), 'modules', len(requests), 'requests', refused, 'refused', sum('differs_because' in e for e in requests), 'known differences',
      sum(e['plugin'].get('questions', 0) for e in requests), 'questions', Path(sys.argv[1]).stat().st_size, 'bytes')
