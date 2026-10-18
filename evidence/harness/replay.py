"""Transparent statement fixtures, axiom audit and fresh Lean-kernel replay.

Fixtures copy declared types and definitions, replacing only theorem proofs by
sorry. They are not independent analytic specifications and never solutions.
The native Windows comparator rejects sorryAx in every solution dependency.
"""
from pathlib import Path
import json, re, subprocess, sys, time
from run_native import ROOT, OUT, RUNTIME, compile_one, environment, sha

EXPORTER = ROOT / 'work/formal/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export.exe'
COMPARATOR = ROOT / 'work/formal/comparator/.lake/build/bin/offline-replay.exe'
AXIOMS = ['propext', 'Quot.sound', 'Classical.choice']
PRIMITIVES = ('Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble '
    'Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat '
    'List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam').split()

def fixture(source):
    lines = source.splitlines(keepends=True)
    result, stack, theorems, definitions = [], [], [], []
    i = 0
    while i < len(lines):
        line = lines[i]
        ns = re.match(r'^namespace (\S+)\s*$', line)
        if ns:
            stack.append(ns[1])
        elif re.match(r'^(?:noncomputable )?section(?:\s+\S+)?\s*$', line):
            stack.append(None)
        elif re.match(r'^end(?:\s+\S+)?\s*$', line):
            assert stack, line
            stack.pop()
        decl = re.match(r'^(?:@\[[^\]]+\]\s*)?(theorem|lemma|def|abbrev) (\w+)\b', line)
        if not decl:
            result.append(line)
            i += 1
            continue
        name = '.'.join([x for x in stack if x] + [decl[2]])
        if decl[1] in ['def', 'abbrev']:
            definitions.append(name)
            result.append(line)
            i += 1
            continue
        theorems.append(name)
        head = line
        while ':=' not in head:
            i += 1
            head += lines[i]
        before, _ = head.split(':=', 1)
        result.append(before + ':= by sorry\n')
        i += 1
        # Proof bodies in the authored overlay are indented, including any
        # multiline term proof. Stop at the next top-level declaration/comment.
        while i < len(lines) and (not lines[i].strip() or lines[i][0].isspace()):
            i += 1
        result.append('\n')
    # Lean permits an anonymous section to extend to end of file. Its lack of
    # a name has no effect on declaration names or the copied specification.
    assert not any(part is not None for part in stack), stack
    assert theorems
    return ''.join(result), theorems, definitions

def ensure_compiled(module):
    source = OUT / (module + '.lean')
    receipt_path = OUT / (module + '.compile.json')
    receipt = json.loads(receipt_path.read_text()) if receipt_path.exists() else {}
    if receipt.get('exit_code') != 0 or receipt.get('source_sha256') != sha(source):
        if compile_one(module):
            raise RuntimeError('Elaboration failed: ' + module)
    receipt = json.loads(receipt_path.read_text())
    assert receipt['olean_sha256'] == sha(OUT / (module + '.olean'))

def export(module, targets):
    dst = OUT / (module + '.ndjson')
    command = [str(EXPORTER), module, '--', *targets]
    start = time.time()
    with dst.open('wb') as out:
        proc = subprocess.run(command, cwd=OUT, env=environment(), stdout=out,
                              stderr=subprocess.PIPE, timeout=900)
    (OUT / (module + '.export.log')).write_bytes(proc.stderr)
    record = {'module': module, 'exit_code': proc.returncode, 'seconds': time.time()-start,
              'bytes': dst.stat().st_size, 'source_sha256': sha(OUT/(module+'.lean')),
              'export_sha256': sha(dst), 'command': command}
    print(json.dumps({k:v for k,v in record.items() if k!='command'}), flush=True)
    assert proc.returncode == 0, proc.stderr.decode(errors='replace')
    return record

def compare(config_path, expected, solution, label):
    command = [str(COMPARATOR), str(config_path), str(OUT/(expected+'.ndjson')),
               str(OUT/(solution+'.ndjson'))]
    start = time.time()
    proc = subprocess.run(command, cwd=OUT, env=environment(), capture_output=True, timeout=900)
    log = proc.stdout.decode(errors='replace') + proc.stderr.decode(errors='replace')
    log_path = OUT / (label + '.log')
    log_path.write_text(log, encoding='utf-8')
    record = {'exit_code': proc.returncode, 'seconds': time.time()-start,
              'log_sha256': sha(log_path), 'command': command}
    print(label, log[-3500:], flush=True)
    return record, log

def run(module):
    ensure_compiled(module)
    source = (OUT/(module+'.lean')).read_text(encoding='utf-8')
    assert not re.search(r'(?m)^\s*(axiom|opaque)\s', source)
    expected, theorems, definitions = fixture(source)
    name = module+'Expected'
    (OUT/(name+'.lean')).write_text('/- STATEMENT-ONLY FIXTURE; NOT A SOLUTION. -/\n'+expected,
                                    encoding='utf-8')
    ensure_compiled(name)
    config = {'theorem_names': theorems, 'definition_names': [], 'permitted_axioms': AXIOMS}
    config_path = OUT/(module+'.replay_config.json')
    config_path.write_text(json.dumps(config, indent=2), encoding='utf-8')
    targets = theorems + definitions + AXIOMS + ['Quot','Quot.mk','Quot.lift','Quot.ind'] + PRIMITIVES
    exports = [export(name, targets), export(module, targets)]
    positive, log = compare(config_path, name, module, module+'.replay')
    assert positive['exit_code'] == 0, log[-5000:]
    negatives = {}
    if module == 'AngularOrientation':
        bad, badlog = compare(config_path, name, name, module+'.unproved_control')
        assert bad['exit_code'] != 0 and 'sorryAx' in badlog
        bad['rejected_for_sorryAx'] = True
        negatives['unproved'] = bad
        needle = 'harmonic k e < 0 :='
        assert expected.count(needle) == 1
        altered = name+'Weaker'
        (OUT/(altered+'.lean')).write_text(expected.replace(needle,'harmonic k e ≤ 0 :='),encoding='utf-8')
        ensure_compiled(altered)
        exports.append(export(altered, targets))
        bad, badlog = compare(config_path, altered, module, module+'.statement_control')
        assert bad['exit_code'] != 0 and 'paired_harmonic_negative' in badlog
        negatives['statement_mismatch'] = bad
    if module == 'FrontierCertificate':
        needle = 'def theta : ℝ := 8748389/10000000'
        assert expected.count(needle) == 1
        altered = name+'WrongTheta'
        (OUT/(altered+'.lean')).write_text(expected.replace(needle,
            'def theta : ℝ := 7/8'), encoding='utf-8')
        ensure_compiled(altered)
        exports.append(export(altered, targets))
        bad, badlog = compare(config_path, altered, module, module+'.definition_control')
        # The checker may detect a dependent definition before it reaches
        # theta itself; the only fixture mutation is the theta body above.
        assert bad['exit_code'] != 0 and 'Const does not match' in badlog
        bad['changed_definition'] = 'AngularFrontierFormal.theta'
        bad['reported_mismatch'] = badlog.strip()
        negatives['definition_mismatch'] = bad
    receipt = {'module': module, **config, 'definitions_exported': definitions,
               'positive': positive, 'negative_controls': negatives, 'exports': exports,
               'source_sha256': sha(OUT/(module+'.lean')),
               'lean_binary_sha256': sha(RUNTIME/'lean.exe'),
               'comparator_binary_sha256': sha(COMPARATOR), 'exporter_binary_sha256':sha(EXPORTER),
               'scope': 'Exact copied-statement comparison, recursive definition comparison, permitted-axiom audit and fresh Lean-kernel replay on Windows. Not an independent analytic specification, an alternate kernel, a Linux sandbox run, or a full angular zero-free theorem.'}
    (OUT/(module+'.replay.json')).write_text(json.dumps(receipt,indent=2),encoding='utf-8')
    print('PASS', module, len(theorems), 'theorems', flush=True)

if __name__ == '__main__':
    for module in sys.argv[1:]:
        run(module)
