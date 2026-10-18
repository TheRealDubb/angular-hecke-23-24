"""Strict native-Windows replay of an explicitly frozen module bundle.

Each statement fixture retains its original module boundary. Only theorem
proofs are admitted in the challenge; every definition remains a copied body.
No checker modifications, definition holes, or independent-specification claim.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import subprocess
import sys
import time

sys.path.insert(1, str(Path(__file__).resolve().parents[1]))
import run_native
from run_native import OUT, RUNTIME, sha
import replay


def theorem_body_assignment(text):
    """Find a declaration's :=, excluding nested terms and let assignments.

    This scanner retains byte-for-byte header text. It ignores comments and
    strings, tracks Lean binder/term brackets, and consumes each let/letI/letI'
    assignment before looking for the outer declaration body. Elaboration and
    strict comparison remain the authoritative checks of the reconstructed type.
    """
    closing = {'(': ')', '[': ']', '{': '}', '⦃': '⦄', '⟨': '⟩'}
    stack, lets, i, comment = [], {}, 0, 0
    while i < len(text):
        if comment:
            if text.startswith('/-', i): comment += 1; i += 2
            elif text.startswith('-/', i): comment -= 1; i += 2
            else: i += 1
            continue
        if text.startswith('/-', i): comment = 1; i += 2; continue
        if text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end + 1
            continue
        char = text[i]
        if char == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\': i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
            continue
        if char in closing: stack.append(closing[char]); i += 1; continue
        if stack and char == stack[-1]:
            lets.pop(len(stack), None)
            stack.pop(); i += 1; continue
        if char.isalpha() or char == '_':
            end = i + 1
            while end < len(text) and (text[end].isalnum() or text[end] in "_'ᵢ"):
                end += 1
            token = text[i:end]
            if token in ('let', 'letI', "letI'"):
                lets[len(stack)] = lets.get(len(stack), 0) + 1
            i = end
            continue
        if text.startswith(':=', i):
            if lets.get(len(stack), 0): lets[len(stack)] -= 1
            elif not stack: return i
            i += 2; continue
        i += 1
    return None


def fixture(source):
    """Local replacement for the frozen v1 fixture scanner; full types retained."""
    lines = source.splitlines(keepends=True)
    result, stack, theorems, definitions, i = [], [], [], [], 0
    while i < len(lines):
        line = lines[i]
        ns = re.match(r'^namespace (\S+)\s*$', line)
        if ns: stack.append(ns[1])
        elif re.match(r'^(?:noncomputable )?section(?:\s+\S+)?\s*$', line): stack.append(None)
        elif re.match(r'^end(?:\s+\S+)?\s*$', line):
            assert stack, line
            stack.pop()
        decl = re.match(r'^(?:@\[[^\]]+\]\s*)?(?:noncomputable )?(theorem|lemma|def|abbrev) (\w+(?:\.\w+)*)\b', line)
        if not decl:
            result.append(line); i += 1; continue
        name = '.'.join([part for part in stack if part] + [decl[2]])
        if decl[1] in ('def', 'abbrev'):
            definitions.append(name); result.append(line); i += 1; continue
        theorems.append(name)
        tail = ''.join(lines[i:])
        body = theorem_body_assignment(tail)
        assert body is not None, ('No theorem body delimiter', name)
        head = tail[:body]
        result.append(head + ':= by sorry\n')
        i += head.count('\n') + 1
        while i < len(lines) and (not lines[i].strip() or lines[i][0].isspace()): i += 1
        result.append('\n')
    assert not any(part is not None for part in stack), stack
    assert theorems
    return ''.join(result), theorems, definitions


def save(path, value):
    path.write_text(json.dumps(value, indent=2), encoding='utf-8')


def write_same_or_new(path, text):
    content = text.encode('utf-8')
    if path.exists():
        assert path.read_bytes() == content, f'Archive changed fixture explicitly before replacing: {path}'
    else:
        path.write_bytes(content)


def imports(source):
    return [dep for line in source.splitlines() if line.startswith('import ')
            for dep in line.split('--', 1)[0].split()[1:]]


def imports_current(receipt):
    return all(not item.get('olean') or
               sha(Path(item['olean'])) == item['olean_sha256']
               for item in receipt.get('imports', []))


def source_record(module):
    path = OUT / (module + '.lean')
    receipt = json.loads(path.with_suffix('.compile.json').read_text())
    assert receipt['exit_code'] == 0, module
    assert receipt['source_sha256'] == sha(path), module
    assert receipt['olean_sha256'] == sha(path.with_suffix('.olean')), module
    assert imports_current(receipt), f'Actual dependency changed after compilation: {module}'
    source = path.read_text(encoding='utf-8')
    assert not re.search(r'(?m)^\s*(axiom|opaque)\s', source), module
    assert not re.search(r'\bsorry\b|\badmit\b', source), module
    fixture_text, targets, definitions = fixture(source)
    return {'module': module, 'source_sha256': sha(path),
            'olean_sha256': sha(path.with_suffix('.olean')),
            'compile_receipt_sha256': sha(path.with_suffix('.compile.json')),
            'theorem_names': targets, 'definitions_exported': definitions}, source, fixture_text


def rewrite_imports(source, modules):
    def rewrite(match):
        code, sep, comment = match[0].partition('--')
        return 'import ' + ' '.join(dep + 'Expected' if dep in modules else dep
                                    for dep in code.split()[1:]) + ((' --' + comment) if sep else '')
    return re.sub(r'(?m)^import [^\n]+', rewrite, source)


def prepare(spec_path):
    spec = json.loads(spec_path.read_text())
    assert spec.get('ready') is True, 'Bundle list is a draft; await explicit source freeze.'
    name, modules = spec['name'], spec['modules']
    assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', name)
    assert not (OUT / (name + '.replay.json')).exists(), 'Existing replay receipt must be reviewed before preparing another run.'
    assert modules and len(modules) == len(set(modules))
    assert all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', m) for m in modules)
    records, fixtures, targets, definitions, external, seen = [], [], [], [], [], set()
    for module in modules:
        record, source, fixture = source_record(module)
        for dep in imports(source):
            if dep in modules:
                assert dep in seen, (module, 'not in topological order', dep)
            elif dep not in external:
                external.append(dep)
        fixtures.append((module, rewrite_imports(fixture, modules)))
        records.append(record)
        targets.extend(record['theorem_names'])
        definitions.extend(record['definitions_exported'])
        seen.add(module)
    assert len(targets) == len(set(targets))
    visited = set()
    def check_external(dep):
        assert dep not in modules, ('External import reaches a redeclared original', dep)
        if dep in visited: return
        visited.add(dep)
        path = next((p / (dep + '.lean') for p in run_native.OVERLAYS
                     if (p / (dep + '.lean')).is_file()), None)
        if path:
            for child in imports(path.read_text(encoding='utf-8')): check_external(child)
    for dep in external: check_external(dep)
    for record, (module, fixture) in zip(records, fixtures):
        shadow = module + 'Expected'
        path = OUT / (shadow + '.lean')
        write_same_or_new(path, '/- STATEMENT-ONLY FIXTURE; NOT A SOLUTION. Module boundary retained. -/\n' + fixture)
        record.update(shadow_module=shadow, shadow_source_sha256=sha(path))
    write_same_or_new(OUT / (name + '.lean'), ''.join('import ' + m + '\n' for m in modules)
                      + '\n/- Export-only union of frozen modules; no new theorem. -/\n')
    write_same_or_new(OUT / (name + 'Expected.lean'), '/- STATEMENT-ONLY FIXTURE; NOT A SOLUTION. -/\n'
                      + ''.join('import ' + m + 'Expected\n' for m in modules))
    record = {'module': name, 'modules': records, 'theorem_names': targets,
              'definition_names': [], 'definitions_exported': definitions,
              'permitted_axioms': replay.AXIOMS, 'external_imports': external,
              'spec_path': str(spec_path.resolve()), 'spec_sha256': sha(spec_path),
              'fixture_layout': 'One shadow per original module; exact external imports.',
              'scope': spec.get('scope', '')}
    save(OUT / (name + '.members.json'), record)
    config = {k: record[k] for k in ('theorem_names', 'definition_names', 'permitted_axioms')}
    write_same_or_new(OUT / (name + '.replay_config.json'), json.dumps(config, indent=2))
    print(f'Prepared {name}: {len(modules)} modules, {len(targets)} theorems, {len(definitions)} definitions', flush=True)
    return record


def ensure_fixture_compiled(module):
    path = OUT / (module + '.compile.json')
    receipt = json.loads(path.read_text()) if path.exists() else {}
    if receipt and not imports_current(receipt):
        assert run_native.compile_one(module) == 0, module
    else:
        replay.ensure_compiled(module)


def verify_members(record):
    for member in record['modules']:
        now, _, _ = source_record(member['module'])
        assert all(member[k] == value for k, value in now.items()), member['module']
        shadow = OUT / (member['shadow_module'] + '.lean')
        assert sha(shadow) == member['shadow_source_sha256']
        if 'shadow_olean_sha256' in member:
            assert sha(shadow.with_suffix('.olean')) == member['shadow_olean_sha256']
            assert sha(shadow.with_suffix('.compile.json')) == member['shadow_compile_receipt_sha256']


def export_once(module, targets):
    cache_path = OUT / (module + '.export.json')
    target_hash = hashlib.sha256(json.dumps(targets).encode()).hexdigest()
    signature = {'source_sha256': sha(OUT / (module + '.lean')),
                 'olean_sha256': sha(OUT / (module + '.olean')),
                 'targets_sha256': target_hash,
                 'exporter_binary_sha256': sha(replay.EXPORTER)}
    if cache_path.exists():
        cached = json.loads(cache_path.read_text())
        assert all(cached[k] == v for k, v in signature.items()), 'Stale export needs an explicit archive.'
        assert cached['exit_code'] == 0
        assert sha(OUT / (module + '.ndjson')) == cached['export_sha256']
        print('Reusing verified export', module, flush=True)
        return {**cached, 'reused_frozen_export': True}
    result = {**replay.export(module, targets), **signature}
    save(cache_path, result)
    return result


def compile_only(spec_path):
    record = prepare(spec_path)
    name = record['module']
    for member in record['modules']:
        ensure_fixture_compiled(member['shadow_module'])
        shadow = OUT / (member['shadow_module'] + '.lean')
        member['shadow_olean_sha256'] = sha(shadow.with_suffix('.olean'))
        member['shadow_compile_receipt_sha256'] = sha(shadow.with_suffix('.compile.json'))
    ensure_fixture_compiled(name)
    ensure_fixture_compiled(name + 'Expected')
    save(OUT / (name + '.members.json'), record)
    verify_members(record)
    print('COMPILE_ONLY_PASSED', name, flush=True)
    return record


def run(spec_path):
    record = compile_only(spec_path)
    name = record['module']
    prior = OUT / (name + '.replay.json')
    targets = record['theorem_names'] + record['definitions_exported'] + replay.AXIOMS + [
        'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'] + replay.PRIMITIVES
    exports = [export_once(name + 'Expected', targets), export_once(name, targets)]
    verify_members(record)
    config_path = OUT / (name + '.replay_config.json')
    log_path = OUT / (name + '.replay.log')
    command = [str(replay.COMPARATOR), str(config_path), str(OUT / (name + 'Expected.ndjson')),
               str(OUT / (name + '.ndjson'))]
    started = time.time()
    # Stream checker output to its log so progress is inspectable during replay.
    with log_path.open('wb') as log:
        proc = subprocess.run(command, cwd=OUT, env=run_native.environment(),
                              stdout=log, stderr=subprocess.STDOUT, timeout=900)
    positive = {'exit_code': proc.returncode, 'seconds': time.time() - started,
                'log_sha256': sha(log_path), 'command': command}
    verify_members(record)
    record.update(positive=positive, negative_controls={}, exports=exports,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        source_sha256=sha(OUT / (name + '.lean')),
        members_sha256=sha(OUT / (name + '.members.json')),
        lean_binary_sha256=sha(RUNTIME / 'lean.exe'),
        comparator_binary_sha256=sha(replay.COMPARATOR),
        exporter_binary_sha256=sha(replay.EXPORTER),
        validation_scope='Strict copied-statement and recursive-definition comparison, permitted-axiom audit, '
            'fresh same-Lean-kernel replay and quotient postcheck on native Windows. No definition holes. '
            'Not an independent analytic specification, alternate kernel, Linux sandbox, or zero-free theorem.')
    save(prior, record)
    text = log_path.read_text(encoding='utf-8')
    print(text[-3500:], flush=True)
    assert proc.returncode == 0, 'Strict replay failed; receipt and log retained.'
    print('PASS', name, len(record['theorem_names']), 'theorems', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('spec', type=Path)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--compile-only', action='store_true')
    args = parser.parse_args()
    assert not (args.prepare_only and args.compile_only)
    if args.prepare_only: prepare(args.spec)
    elif args.compile_only: compile_only(args.spec)
    else: run(args.spec)
