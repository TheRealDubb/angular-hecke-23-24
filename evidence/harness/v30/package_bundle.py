"""Validate and losslessly preserve a completed v30 strict replay bundle."""
from pathlib import Path
import datetime, gzip, hashlib, json, os, re, shutil, sys

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'outputs/ANGULAR_LEAN'
AXIOMS = ['propext', 'Quot.sound', 'Classical.choice']

def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def read(path):
    return json.loads(path.read_text(encoding='utf-8'))

def pin(path):
    return {'path': str(path.relative_to(ROOT)), 'sha256': sha(path), 'bytes': path.stat().st_size}

def content_pin(path):
    h, n = hashlib.sha256(), 0
    with gzip.open(path, 'rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''):
            h.update(block); n += len(block)
    return h.hexdigest(), n

def validate(out, name):
    r = read(out / (name + '.replay.json'))
    assert r['positive']['exit_code'] == 0
    assert r['definition_names'] == [] and r['permitted_axioms'] == AXIOMS
    assert sha(out / (name + '.lean')) == r['source_sha256']
    assert sha(out / (name + '.members.json')) == r['members_sha256']
    assert read(out / (name + '.members.json'))['modules'] == r['modules']
    log = out / (name + '.replay.log')
    assert sha(log) == r['positive']['log_sha256']
    text = log.read_text(encoding='utf-8')
    assert all(x in text for x in ['STATEMENT_COMPARISON_PASSED', 'AXIOM_AUDIT_PASSED',
        'KERNEL_REPLAY_AND_QUOTIENT_POSTCHECK_PASSED', 'OFFLINE_REPLAY_PASSED'])
    assert r['lean_binary_sha256'] == sha(ROOT / 'work/formal/runtime/lean-4.34.1-windows/bin/lean.exe')
    assert r['comparator_binary_sha256'] == sha(ROOT / 'work/formal/comparator/.lake/build/bin/offline-replay.exe')
    assert r['exporter_binary_sha256'] == sha(ROOT / 'work/formal/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export.exe')
    names = []
    for m in r['modules']:
        names.extend(m['theorem_names'])
        for mod, src_hash, obj_hash, receipt_hash in [
            (m['module'], m['source_sha256'], m['olean_sha256'], m['compile_receipt_sha256']),
            (m['shadow_module'], m['shadow_source_sha256'], m['shadow_olean_sha256'], m['shadow_compile_receipt_sha256'])]:
            assert sha(out / (mod + '.lean')) == src_hash
            assert sha(out / (mod + '.olean')) == obj_hash
            assert sha(out / (mod + '.compile.json')) == receipt_hash
            c = read(out / (mod + '.compile.json'))
            assert c['exit_code'] == 0 and c['source_sha256'] == src_hash and c['olean_sha256'] == obj_hash
    assert len(names) == len(set(names)) and names == r['theorem_names']
    return r

def main(version, name):
    assert version == 'v30' and re.fullmatch(r'[A-Za-z][A-Za-z0-9]*Bundle', name)
    out = BASE / version
    assert out.resolve().parent == BASE.resolve()
    r = validate(out, name)
    previous = [BASE / 'v1/FORMALIZATION_STATUS.json', BASE / 'v2/AngularGaussianSchwartz.replay.json',
        BASE / 'v3/VERIFIED_MANIFEST.json']
    if version == 'v30':
        previous.extend([BASE / 'v4/VERIFIED_MANIFEST.json', BASE / 'v5/VERIFIED_MANIFEST.json', BASE / 'v6/AngularNonpoleTransferBundle.VERIFIED_MANIFEST.json', BASE / 'v6/AngularAllOrderCuspBundle.VERIFIED_MANIFEST.json', BASE / 'v7/AngularPhysicalCoefficientBundle.VERIFIED_MANIFEST.json', BASE / 'v8/AngularFiniteProjectorBundle.VERIFIED_MANIFEST.json', BASE / 'v9/AngularShiftedReflectionBundle.VERIFIED_MANIFEST.json', BASE / 'v10/AngularKernelEnergyBundle.VERIFIED_MANIFEST.json', BASE / 'v11/AngularCuspPhaseBundle.VERIFIED_MANIFEST.json', BASE / 'v12/AngularStratumModelBundle.VERIFIED_MANIFEST.json', BASE / 'v13/AngularRowClosureBundle.VERIFIED_MANIFEST.json', BASE / 'v14/AngularRowSourceBundle.VERIFIED_MANIFEST.json'])
    previous.append(BASE / 'v15/AngularBranchExtractionBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v16/AngularFiberConnectionBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v17/AngularPhysicalFiberBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v18/AngularPhysicalMeanSquareBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v19/AngularPhysicalDyadicBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v20/AngularHeightUniformityBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v21/AngularRaySieveBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v22/AngularInitialSourceBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v23/AngularSixthPowerSeedBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v24/AngularEulerCorrectionBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v25/AngularSeedNonvanishingBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v26/AngularPlainReflectionBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v27/AngularImprimitiveReflectionBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v28/AngularPlainGrowthBundle.VERIFIED_MANIFEST.json')
    previous.append(BASE / 'v29/AngularNormTwistBundle.VERIFIED_MANIFEST.json')
    old = [pin(p) for p in previous]
    evidence = []
    for e in r['exports']:
        assert e['exit_code'] == 0
        module = e['module']
        assert module in [name, name + 'Expected']
        assert sha(out / (module + '.lean')) == e['source_sha256']
        raw = out / (module + '.ndjson')
        gz = raw.with_suffix('.ndjson.gz')
        wanted = e['export_sha256'], e['bytes']
        if raw.exists():
            assert (sha(raw), raw.stat().st_size) == wanted
            tmp = gz.with_suffix('.gz.tmp')
            assert raw.resolve().parent == out.resolve() and tmp.resolve().parent == out.resolve()
            with raw.open('rb') as inp, gzip.GzipFile(filename=str(tmp), mode='wb', compresslevel=1, mtime=0) as target:
                shutil.copyfileobj(inp, target, 1024*1024)
            assert content_pin(tmp) == wanted
            os.replace(tmp, gz)
            raw.unlink()  # Verified redundant raw export only; no source or receipt deletion.
        assert content_pin(gz) == wanted
        evidence.append({'module': module, 'raw_sha256': wanted[0], 'raw_bytes': wanted[1], 'gzip': pin(gz)})
        print('VERIFIED', module, flush=True)
    assert r == validate(out, name)
    assert old == [pin(p) for p in previous]
    manifest = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'status': 'all_bundle_modules_replayed', 'genuine_module_count': len(r['modules']),
        'theorem_count': len(r['theorem_names']), 'definition_count': len(r['definitions_exported']),
        'modules': r['modules'], 'exports': evidence, 'replay_receipt': pin(out / (name + '.replay.json')),
        'members': pin(out / (name + '.members.json')), 'packaging_script': pin(Path(__file__)),
        'prior_milestones_unchanged': old, 'full_zero_free_theorem_verified': False,
        'scope': 'Native Windows exact copied-statement/recursive-definition comparison, standard-axiom '
            'audit and fresh same-Lean-kernel replay. No independent analytic specification, alternate kernel or Linux sandbox.'}
    prefix = name + '.' if version == 'v30' else ''
    (out / (prefix + 'COMPRESSED_EXPORTS.json')).write_text(json.dumps(evidence, indent=2), encoding='utf-8')
    (out / (prefix + 'VERIFIED_MANIFEST.json')).write_text(json.dumps(manifest, indent=2), encoding='utf-8')
    print(json.dumps({k: manifest[k] for k in ['status', 'genuine_module_count', 'theorem_count', 'definition_count']}))

if __name__ == '__main__':
    assert len(sys.argv) == 3
    main(*sys.argv[1:])







