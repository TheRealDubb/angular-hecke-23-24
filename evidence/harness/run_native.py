"""Compile an additive angular overlay on Windows using pinned, read-only caches.

Setup maps resolve imports only. A successful compile is not an analytic theorem,
nor a substitute for statement comparison and independent kernel replay.
"""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'outputs/ANGULAR_LEAN/v1'
BASE = ROOT / 'work/formal/original/lean'
RUNTIME = ROOT / 'work/formal/runtime/lean-4.34.1-windows/bin'

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()

def environment():
    env = os.environ.copy()
    env['PATH'] = str(RUNTIME) + os.pathsep + env['PATH']
    env['LEAN_NUM_THREADS'] = '1'
    cache = ROOT / 'work/formal/windows-comparator/path-smoke-LEAN_PATH.txt'
    env['LEAN_PATH'] = str(OUT) + os.pathsep + cache.read_text().strip()
    return env

def compose_setup(name, source):
    imports = []
    for line in source.read_text(encoding='utf-8').splitlines():
        if line.startswith('import '):
            imports.extend(line.split('--', 1)[0].split()[1:])
    assert imports, 'A module must declare its imports explicitly.'
    seed = BASE / '.lake/build/ir/OAI/NumberTheory/DirichletL/Endpoint.setup.json'
    setup = json.loads(seed.read_text(encoding='utf-8'))
    setup['name'] = name
    evidence = [{'module': 'seed (dependency resolution only)', 'setup': str(seed), 'sha256': sha(seed)}]
    roots = [BASE, *sorted((BASE / '.lake/packages').iterdir())]
    for dep in imports:
        rel = Path(*dep.split('.'))
        local = OUT / rel.with_suffix('.lean')
        dep_setup = None
        if local.is_file():
            receipt = json.loads((OUT / rel.with_suffix('.compile.json')).read_text())
            assert receipt['exit_code'] == 0 and receipt['source_sha256'] == sha(local), dep
            olean = OUT / rel.with_suffix('.olean')
            assert receipt['olean_sha256'] == sha(olean), dep
            dep_setup = OUT / rel.with_suffix('.setup.json')
        else:
            candidates = [(r / '.lake/build/ir' / rel.with_suffix('.setup.json'),
                           r / '.lake/build/lib/lean' / rel.with_suffix('.olean')) for r in roots]
            match = next(((s, o) for s, o in candidates if s.is_file() and o.is_file()), None)
            if match:
                dep_setup, olean = match
            elif dep in setup['importArts']:
                evidence.append({'module': dep, 'resolution': 'pinned seed map'})
                continue
            else:
                paths = environment()['LEAN_PATH'].split(os.pathsep)
                olean = next((Path(p) / rel.with_suffix('.olean') for p in paths
                              if (Path(p) / rel.with_suffix('.olean')).is_file()), None)
                assert olean is not None, f'No cached import: {dep}'
        if dep_setup is not None:
            other = json.loads(dep_setup.read_text(encoding='utf-8'))
            for key in ['plugins', 'package', 'options', 'isModule', 'dynlibs']:
                # Dependencies from mathlib have their own package name/options;
                # their import artifact maps remain usable for the OAI overlay.
                if key in ['plugins', 'dynlibs']:
                    assert not other[key], (dep, key)
            for key, value in other['importArts'].items():
                previous = setup['importArts'].get(key)
                if previous is not None and previous != value:
                    assert previous[0][0] == value[0][0], (dep, key)
                setup['importArts'][key] = value
        setup['importArts'][dep] = [[str(olean)]]
        evidence.append({'module': dep, 'olean': str(olean), 'olean_sha256': sha(olean),
                         'setup': str(dep_setup) if dep_setup else None,
                         'setup_sha256': sha(dep_setup) if dep_setup else None})
    return setup, evidence

def compile_one(name):
    assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', name), name
    OUT.mkdir(parents=True, exist_ok=True)
    attempts = OUT / 'attempts'
    attempts.mkdir(exist_ok=True)
    indices = [int(p.stem.split('.')[-1]) for p in attempts.glob(name + '.*.json')]
    number = max(indices, default=0) + 1
    stem = attempts / f'{name}.{number:03d}'
    source = OUT / (name + '.lean')
    source_bytes = source.read_bytes()
    Path(str(stem) + '.lean').write_bytes(source_bytes)
    setup, imports = compose_setup(name, source)
    setup_path = OUT / (name + '.setup.json')
    setup_path.write_text(json.dumps(setup), encoding='utf-8')
    command = [str(RUNTIME / 'lean.exe'), str(source), '--setup', str(setup_path),
               '-o', str(OUT / (name + '.olean'))]
    started = time.time()
    try:
        proc = subprocess.run(command, cwd=OUT, env=environment(), capture_output=True, timeout=900)
    except subprocess.TimeoutExpired as error:
        proc = subprocess.CompletedProcess(command, 124, error.stdout or b'',
                 (error.stderr or b'') + b'\n900-second bounded compile timeout.\n')
    log = proc.stdout.decode('utf-8', errors='replace') + proc.stderr.decode('utf-8', errors='replace')
    assert source.read_bytes() == source_bytes, 'Source changed while compiling; do not certify it.'
    record = {'module': name, 'attempt': number, 'exit_code': proc.returncode,
              'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'seconds': time.time() - started, 'command': command,
              'source_sha256': sha(source), 'setup_sha256': sha(setup_path),
              'setup_kind': 'composed pinned cached artifact maps', 'imports': imports,
              'lean_binary_sha256': sha(RUNTIME / 'lean.exe'),
              'scope': 'Native Windows compilation only; read module statement for scope. No full angular zero-free theorem claimed.'}
    if proc.returncode == 0:
        record['olean_sha256'] = sha(OUT / (name + '.olean'))
    for path in [Path(str(stem) + '.log'), OUT / (name + '.compile.log')]:
        path.write_text(log, encoding='utf-8')
    for path in [Path(str(stem) + '.json'), OUT / (name + '.compile.json')]:
        path.write_text(json.dumps(record, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in record.items() if k != 'imports'}), flush=True)
    if len(log) <= 6000:
        print(log, flush=True)
    else:
        print(log[:1000] + '\n[Full diagnostics saved in compile.log]\n' + log[-1500:], flush=True)
    return proc.returncode

if __name__ == '__main__':
    for module in sys.argv[1:]:
        result = compile_one(module)
        if result:
            raise SystemExit(result)
