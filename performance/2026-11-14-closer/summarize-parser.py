import json, statistics, pathlib, sys
base = pathlib.Path('/tmp/pille-perf-bw1z4aif/artifacts')
prefix = sys.argv[1]
modes = sys.argv[2:]
stages = ['annotate', 'supertag', 'pointer_bytes', 'request_of', 'request_array', 'decode', 'formula']
results = {}
for mode in modes:
    directory = base / f'parser-{mode}'
    events = json.loads((directory / f'{prefix}.events.json').read_text())
    raw = [json.loads(line) for line in (directory / f'{prefix}.events.jsonl').read_text().splitlines() if line.startswith('{')]
    summary = {
        'module_load_ms': raw[1]['monotonic_ms'] - raw[0]['monotonic_ms'],
        'parser_init_ms': events[1]['ms'],
        'first_invocation_ms': {e['stage']: e['ms'] for e in events if e.get('index') == 0 and e.get('pass') == 0 and 'ms' in e},
        'validated_calls': len([e for e in events if e['stage'] == 'validated']),
        'warm_stages': {}, 'warm_per_sentence': {}, 'warm_five_sentence_pass_total_ms': {},
    }
    for stage in stages:
        values = [e['ms'] for e in events if e.get('stage') == stage and e.get('pass', -1) > 0]
        summary['warm_stages'][stage] = {'count': len(values), 'median_ms': statistics.median(values), 'min_ms': min(values), 'max_ms': max(values)}
    for index in [0, 8, 12, 34, 38]:
        summary['warm_per_sentence'][index] = {stage: statistics.median([e['ms'] for e in events if e.get('stage') == stage and e.get('index') == index and e.get('pass', -1) > 0]) for stage in stages}
    for rep in [1, 2]:
        summary['warm_five_sentence_pass_total_ms'][rep] = sum(e['ms'] for e in events if e.get('pass') == rep and e.get('stage') in stages)
    (directory / f'{prefix}.summary.json').write_text(json.dumps(summary, indent=2))
    results[mode] = summary
out = base / f'parser-{modes[-1]}' / f'{prefix}-comparison.json'
out.write_text(json.dumps(results, indent=2))
print('warm median ms:')
for stage in stages:
    print(stage, {mode: round(results[mode]['warm_stages'][stage]['median_ms'], 4) for mode in modes})
print('five-sentence total ms:')
for mode, summary in results.items():
    print(mode, summary['warm_five_sentence_pass_total_ms'])
print('neural per sentence:')
for index in [0, 8, 12, 34, 38]:
    print(index, [(mode, round(results[mode]['warm_per_sentence'][index]['annotate'], 4), round(results[mode]['warm_per_sentence'][index]['supertag'], 4)) for mode in modes])
print(out)
