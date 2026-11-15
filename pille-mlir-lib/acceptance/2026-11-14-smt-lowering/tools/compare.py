#!/usr/bin/env python3
"""Compare the native plugin's lowering with the Rhombus lowering, from the records
query.rkt wrote while PILLE_MLIR_SMT_COMPARE was set (work order E1 and E4).

  compare.py RECORDS_DIR [--solve] [--out SUMMARY.json]

Each record holds one lowering request (a module, its IRDL and a manifest) and what
each side made of it: a refusal, or the verified SMT module and its exported SMT-LIB.
"""
import json, re, subprocess, sys, hashlib
from pathlib import Path

def message(error):
    """The diagnostic itself: what follows `error: ` on its line."""
    found = re.search(r'error: (.*)', error)
    return found.group(1) if found else error

def questions(smtlib):
    parts, current = [], []
    for line in smtlib.splitlines():
        current.append(line)
        if line.strip() == '(reset)':
            parts.append('\n'.join(current) + '\n'); current = []
    assert not ''.join(current).strip(), 'text after the last reset'
    return parts

def normalized(script):
    """Names and let bindings normalized: every let-bound name is replaced by what it is bound to, and
    declared names by their position."""
    tokens = re.findall(r'\(|\)|[^\s()]+', re.sub(r';[^\n]*', '', script))
    def parse(i):
        if tokens[i] == '(':
            items, i = [], i + 1
            while tokens[i] != ')':
                item, i = parse(i); items.append(item)
            return items, i + 1
        return tokens[i], i + 1
    forms, i = [], 0
    while i < len(tokens):
        form, i = parse(i); forms.append(form)
    names = {}
    def expand(term, env):
        if isinstance(term, str): return env.get(term, names.get(term, term))
        if term and term[0] == 'let':
            inner = dict(env)
            for name, value in term[1]: inner[name] = expand(value, env)
            return expand(term[2], inner)
        return [expand(t, env) for t in term]
    out = []
    for form in forms:
        if form[0] in ('declare-const', 'declare-fun'):
            names[form[1]] = f'v{len(names)}'
            out.append([form[0], names[form[1]]] + form[2:])
        else: out.append(expand(form, {}))
    return json.dumps(out)

def z3(script, extra=''):
    text = script.replace('(check-sat)', extra + '(check-sat)')
    names = re.findall(r'\(declare-const (\S+) ', script)
    ask = text.replace('(reset)', (f'(get-value ({" ".join(names)}))\n' if names else '') + '(reset)')
    out = subprocess.run(['z3', '-in', '-T:20'], input=ask, capture_output=True, text=True).stdout
    status = out.split()[0] if out.split() else 'none'
    values = dict(re.findall(r'\(([^\s()]+) (#[xb][0-9a-f]+)\)', out)) if status == 'sat' else {}
    return status, values

def value_set(script, names, limit=600):
    """Every assignment of `names` the script admits, by blocking each as it is found."""
    found, block = [], ''
    while len(found) < limit:
        status, values = z3(script, block)
        if status != 'sat': return sorted(found), status
        point = tuple(values[n] for n in names); found.append(point)
        block += '(assert (not (and ' + ' '.join(f'(= {n} {v})' for n, v in zip(names, point)) + ' true)))\n'
    return sorted(found), 'limit'

def main():
    directory = Path(sys.argv[1]); solve = '--solve' in sys.argv
    out = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
    summary = dict(records=0, both_lowered=0, both_refused=0, refusals_equal=0, verified_equal=0, smtlib_equal=0,
                   members_equal=0, questions=0, questions_text_equal=0, questions_normalized_equal=0,
                   proof_questions=0, values_questions=0, statuses={}, status_equal=0, counterexamples_cross_checked=0,
                   value_sets_equal=0, differences=[], distinct_requests=0, refusal_messages={})
    seen = set()
    for path in sorted(directory.glob('*.json')):
        record = json.loads(path.read_text()); summary['records'] += 1
        key = hashlib.sha256(json.dumps([record['ir'], record['irdl'], record['manifest']]).encode()).hexdigest()
        fresh = key not in seen; seen.add(key)
        p, r = record['plugin'], record['rhombus']
        def differ(what, **more): summary['differences'].append(dict(record=path.name, what=what, **more))
        if 'verify_error' in p or 'verify_error' in r:
            differ('a lowered module failed stock verification', plugin=p.get('verify_error'), rhombus=r.get('verify_error')); continue
        if 'error' in p or 'error' in r:
            if 'error' in p and 'error' in r:
                summary['both_refused'] += 1
                if message(p['error']) == message(r['error']):
                    summary['refusals_equal'] += 1
                    if fresh: summary['refusal_messages'][message(p['error'])] = summary['refusal_messages'].get(message(p['error']), 0) + 1
                else: differ('refusal messages differ', plugin=message(p['error']), rhombus=message(r['error']))
            else: differ('one side refused', plugin=p.get('error', 'lowered'), rhombus=r.get('error', 'lowered'))
            continue
        summary['both_lowered'] += 1
        if p['verified'] == r['verified']: summary['verified_equal'] += 1
        else: differ('verified MLIR differs', plugin=p['verified'], rhombus=r['verified'])
        if p['smtlib'] == r['smtlib']: summary['smtlib_equal'] += 1
        if p['members'] == [] and isinstance(r['members'], list) and len(r['members']) == 1: pass  # a single query: the plugin wrote no sidecar
        elif p['members'] == r['members']: summary['members_equal'] += 1
        else: differ('standalone query modules differ')
        pq, rq = questions(p['smtlib']), questions(r['smtlib'])
        if len(pq) != len(rq): differ('question counts differ', plugin=len(pq), rhombus=len(rq)); continue
        try: manifest = json.loads(record['manifest'])
        except ValueError: manifest = {}
        specs = manifest.get('queries', [manifest]) if isinstance(manifest, dict) else []
        for index, (a, b) in enumerate(zip(pq, rq)):
            summary['questions'] += 1
            if a == b: summary['questions_text_equal'] += 1
            if normalized(a) == normalized(b): summary['questions_normalized_equal'] += 1
            else: differ('SMT-LIB differs after normalization', question=index, plugin=a, rhombus=b)
            spec = specs[index] if index < len(specs) and isinstance(specs[index], dict) else {}
            values = spec.get('mode') == 'values'
            summary['values_questions' if values else 'proof_questions'] += 1
            if not (solve and fresh): continue
            if values:
                names = [spec['result_symbol'], spec['defined_symbol']]
                sa, sb = value_set(a, names), value_set(b, names)
                if sa == sb: summary['value_sets_equal'] += 1
                else: differ('value sets differ', question=index, plugin=sa, rhombus=sb)
            else:
                (sa, va), (sb, vb) = z3(a), z3(b)
                summary['statuses'][sa] = summary['statuses'].get(sa, 0) + 1
                if sa == sb: summary['status_equal'] += 1
                else: differ('statuses differ', question=index, plugin=sa, rhombus=sb)
                # a refutation's counterexample is also refuted by the other side's query
                for (status, model, other, side) in ((sa, va, b, 'plugin'), (sb, vb, a, 'rhombus')):
                    if status != 'sat': continue
                    pin = ''.join(f'(assert (= {n} {v}))\n' for n, v in model.items())
                    again, _ = z3(other, pin)
                    if again == 'sat': summary['counterexamples_cross_checked'] += 1
                    else: differ(f"the {side} lowering's counterexample is not one of the other's", question=index, model=model, other=again)
    summary['distinct_requests'] = len(seen)
    text = json.dumps(summary, indent=1, sort_keys=True)
    if out: Path(out).write_text(text + '\n')
    shown = dict(summary); shown['differences'] = len(summary['differences']); shown['refusal_messages'] = len(summary['refusal_messages'])
    print(json.dumps(shown, indent=1, sort_keys=True))
    for d in summary['differences'][:12]: print(json.dumps(d, indent=1)[:1500])

main()
