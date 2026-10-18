"""Freeze unchanged source/evidence for the 23/24 timestamp, without a rebuild."""
from pathlib import Path
import datetime, gzip, hashlib, json, re, shutil, subprocess, zipfile

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT/'outputs/ANGULAR_LEAN'
DEST = ROOT/'outputs/ANGULAR_23_24_TIMESTAMP_2026-10-18'
REPO = DEST/'repository'
ASSETS = DEST/'release-assets'
TOP = BASE/'v30'
NAME = 'AngularPrincipalExceptionBundle'
PIN = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
ORIGINAL = ROOT/'work/formal/original'
COMP = ROOT/'work/formal/comparator'

def sha(p):
    with p.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def read(p):
    return json.loads(p.read_text(encoding='utf-8'))

def git(*args, cwd=ORIGINAL):
    return subprocess.check_output(['git', '-C', str(cwd), *args], text=True).strip()

assert git('rev-parse','HEAD') == PIN
assert git('status','--short','--untracked-files=no') == ''
manifest = read(TOP/(NAME+'.VERIFIED_MANIFEST.json'))
receipt = read(TOP/(NAME+'.replay.json'))
assert manifest['status'] == 'all_bundle_modules_replayed'
assert receipt['positive']['exit_code'] == 0
assert receipt['definition_names'] == []
assert set(receipt['permitted_axioms']) == {'propext','Quot.sound','Classical.choice'}
log = TOP/(NAME+'.replay.log')
assert sha(log) == receipt['positive']['log_sha256']
for marker in ['STATEMENT_COMPARISON_PASSED','AXIOM_AUDIT_PASSED',
               'KERNEL_REPLAY_AND_QUOTIENT_POSTCHECK_PASSED','OFFLINE_REPLAY_PASSED']:
    assert marker in log.read_text()
assert sha(TOP/(NAME+'.replay.json')) == manifest['replay_receipt']['sha256']
assert sha(TOP/(NAME+'.members.json')) == receipt['members_sha256']
assert sha(TOP/(NAME+'.lean')) == receipt['source_sha256']
for m in manifest['modules']:
    for stem, a, b, c in [(m['module'],'source_sha256','olean_sha256','compile_receipt_sha256'),
                          (m['shadow_module'],'shadow_source_sha256','shadow_olean_sha256','shadow_compile_receipt_sha256')]:
        for suffix, key in [('.lean',a),('.olean',b),('.compile.json',c)]:
            assert sha(TOP/(stem+suffix)) == m[key], (stem,key)
for label, p in [('lean', ROOT/'work/formal/runtime/lean-4.34.1-windows/bin/lean.exe'),
                 ('comparator',COMP/'.lake/build/bin/offline-replay.exe'),
                 ('exporter',COMP/'.lake/packages/lean4export/.lake/build/bin/lean4export.exe')]:
    assert sha(p) == receipt[label+'_binary_sha256']

# Resolve each direct import through its actual frozen setup map.
modules, external = {}, set()
def visit(src):
    name = src.stem
    if name in modules:
        assert modules[name]['source'] == str(src)
        return
    rec = read(src.with_suffix('.compile.json'))
    assert rec['exit_code'] == 0 and sha(src) == rec['source_sha256'], name
    assert sha(src.with_suffix('.olean')) == rec['olean_sha256'], name
    data = src.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|sorryAx)\b|^axiom\s', data, re.M), name
    imports = []
    for line in data.splitlines():
        if line.startswith('import '):
            imports.extend(line.split('--',1)[0].split()[1:])
    setup = read(src.with_suffix('.setup.json'))
    modules[name] = {'module':name,'source':str(src), 'source_sha256':sha(src),
        'olean_sha256':rec['olean_sha256'], 'compile_receipt_sha256':sha(src.with_suffix('.compile.json')),
        'source_path':src.relative_to(ROOT).as_posix(), 'imports':imports,
        'lines':len(data.splitlines())}
    for dep in imports:
        arts = setup['importArts'].get(dep)
        candidate = Path(arts[0][0]).with_suffix('.lean') if arts else None
        if candidate and candidate.is_file() and candidate.is_relative_to(BASE):
            visit(candidate)
        else:
            assert dep.startswith(('OAI.','Mathlib','Lean','Init','Batteries','Qq','Aesop')), (name,dep,candidate)
            external.add(dep)
visit(TOP/'AngularFullFamilySeed.lean')
assert len(modules) == 130, len(modules)

assert not (REPO/'.git').exists(), 'Do not change a committed package.'
DEST.mkdir(exist_ok=True)
REPO.mkdir(exist_ok=True)
ASSETS.mkdir(exist_ok=True)
def copy(p, target):
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(p,target)
    assert sha(p) == sha(target)

for m in modules.values():
    src = Path(m['source'])
    for suffix in ['.lean','.compile.json','.compile.log']:
        p = src.with_suffix(suffix)
        copy(p, REPO/'snapshot'/p.relative_to(ROOT))
    del m['source']
for p in TOP.iterdir():
    if p.is_file() and p.suffix in {'.lean','.json','.log','.md'} and not p.name.endswith('.setup.json'):
        copy(p, REPO/'evidence/windows/v30'/p.name)
for version in ['v25','v29']:
    for p in (BASE/version).iterdir():
        if p.is_file() and (p.name.endswith(('.replay.json','.replay.log','.replay_config.json',
                  '.VERIFIED_MANIFEST.json','.members.json'))):
            copy(p, REPO/'evidence/windows'/version/p.name)
for p in (ROOT/'work/angular_lean/v30').iterdir():
    if p.suffix in {'.py','.json'}:
        copy(p, REPO/'evidence/harness/v30'/p.name)
for filename in ['run_native.py','replay.py']:
    p = ROOT/'work/angular_lean'/filename
    if p.exists(): copy(p,REPO/'evidence/harness'/filename)
for p in COMP.iterdir():
    if p.is_file() and p.name in ['Comparator.lean','OfflineReplay.lean','Main.lean','WindowsWhich.lean',
            'WindowsDevelopmentRunner.lean','lakefile.toml','lake-manifest.json','lean-toolchain','LICENSE']:
        copy(p, REPO/'evidence/checker-source'/p.name)
for p in (COMP/'Comparator').rglob('*.lean'):
    copy(p, REPO/'evidence/checker-source'/p.relative_to(COMP))
for filename in ['lake-manifest.json','lean-toolchain','lakefile.lean']:
    copy(ORIGINAL/'lean'/filename, REPO/'dependencies/oai003'/filename)
copy(ORIGINAL/'LICENSE', REPO/'dependencies/oai003/LICENSE')

original_modules = {}
def visit_original(name):
    if not name.startswith('OAI') or name in original_modules: return
    p = ORIGINAL/'lean'/Path(*name.split('.')).with_suffix('.lean')
    assert p.is_file(), ('missing pinned source',name,p)
    original_modules[name]=p
    for line in p.read_text(encoding='utf-8').splitlines():
        if line.startswith('import '):
            for dep in line.split('--',1)[0].split()[1:]: visit_original(dep)
for dep in sorted(external): visit_original(dep)
# This is a partial clone. Snapshot the actual locally present dependency closure,
# verifying each byte against its committed Git blob id without fetching other paths.
index = {}
raw_index = subprocess.check_output(['git','-C',str(ORIGINAL),'ls-files','-s','-z'])
for entry in raw_index.split(b'\0'):
    if not entry: continue
    meta,path = entry.split(b'\t',1)
    mode,blob,stage = meta.decode().split()
    assert stage == '0'
    index[path.decode('utf-8')]=blob
original_files = set(original_modules.values())
original_files.update(ORIGINAL/'lean'/n for n in ['lakefile.lean','lake-manifest.json','lean-toolchain','README.md'])
original_files.update(ORIGINAL/n for n in ['LICENSE','README.md'])
original_pins=[]
archive = ASSETS/'oai003-pinned-lean-source.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in sorted(original_files):
        rel=p.relative_to(ORIGINAL).as_posix()
        data=p.read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        # On this checkout, tracked Lean text may use CRLF. Compare exact raw
        # bytes first, then Git's declared line-ending normalization only.
        if blob != index[rel]:
            clean = data.replace(b'\r\n',b'\n')
            blob=hashlib.sha1(b'blob '+str(len(clean)).encode()+b'\0'+clean).hexdigest()
            assert blob==index[rel], ('tracked source mismatch',rel)
            normalization='working-tree CRLF; committed blob LF'
        else: normalization='none'
        original_pins.append({'path':rel,'sha256':hashlib.sha256(data).hexdigest(),
             'git_blob':blob,'normalization':normalization,'bytes':len(data)})
        z.writestr('oai003-'+PIN+'/'+rel,data)
(REPO/'ORIGINAL_DEPENDENCY_SNAPSHOT.json').write_text(json.dumps({'revision':PIN,
    'module_count':len(original_modules),'files':original_pins},indent=2)+'\n')
asset_records = [{'file':archive.name,'bytes':archive.stat().st_size,'sha256':sha(archive),
    'scope':'Unchanged working-tree source closure of pinned original Lean dependencies; each file checked against committed Git blob, with original build manifests/license.'}]
for exp in manifest['exports']:
    p = TOP/(exp['module']+'.ndjson.gz')
    assert sha(p)==exp['gzip']['sha256'] and p.stat().st_size==exp['gzip']['bytes']
    copy(p,ASSETS/p.name)
    # Validate the existing compressed proof stream without replay or extraction to disk.
    h, count = hashlib.sha256(), 0
    with gzip.open(p,'rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):
            h.update(b);count+=len(b)
    assert h.hexdigest()==exp['raw_sha256'] and count==exp['raw_bytes']
    asset_records.append({'file':p.name,'bytes':p.stat().st_size,'sha256':sha(p),
        'raw_sha256':h.hexdigest(),'raw_bytes':count})

now = datetime.datetime.now(datetime.timezone.utc).isoformat()
pins = {'original_oai003': {'url':'https://github.com/openai/math','revision':PIN,'tracked_checkout_clean':True},
    'lean':{'version':'4.34.1','revision':'5045d0056413266e57c625dcd7c365b10e377c52',
            'windows_executable_sha256':receipt['lean_binary_sha256']},
    'mathlib':{'revision':'d13f23b723b8a846827a245b89c10fc7d3f11612',
               'all_lake_dependencies':'dependencies/oai003/lake-manifest.json'},
    'comparator':{'url':'https://github.com/leanprover/comparator','upstream_revision':git('rev-parse','HEAD',cwd=COMP),
        'local_adaptation':'evidence/checker-source/OfflineReplay.lean and exact local lakefile.toml included',
        'executable_sha256':receipt['comparator_binary_sha256']},
    'exporter':{'revision':'076e8e57707e813375e8f9da8bf989799ace9680',
                'executable_sha256':receipt['exporter_binary_sha256']}}
(REPO/'DEPENDENCY_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(REPO/'SOURCE_CLOSURE.json').write_text(json.dumps({'root_module':'AngularFullFamilySeed',
    'module_count':len(modules),'line_count':sum(m['lines'] for m in modules.values()),
    'modules':sorted(modules.values(),key=lambda m:m['source_path']), 'external_direct_imports':sorted(external)},indent=2)+'\n')
(REPO/'RELEASE_ASSETS.json').write_text(json.dumps({'assets':asset_records},indent=2)+'\n')
audit = {'utc':now,'scope':'Artifact integrity audit only; existing successful replay retained unchanged.',
    'source_modules':len(modules),'source_lines':sum(m['lines'] for m in modules.values()),
    'source_and_object_hashes_match_compile_receipts':True,'final_bundle_hashes_match_verified_manifest':True,
    'statement_comparison_recorded_pass':True,'axiom_audit_recorded_pass':True,
    'fresh_windows_kernel_replay_recorded_pass':True,'quotient_postcheck_recorded_pass':True,
    'proof_gzip_and_uncompressed_hashes_rechecked':True,'original_tracked_checkout_clean':True,
    'new_compilation_performed':False,'new_kernel_replay_performed':False,
    'portable_clean_rebuild':False,'linux_replay':False,'stronger_08748389_complete':False,
    'published_to_github':False,'publication_owner':'user'}
(REPO/'PACKAGE_INTEGRITY_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps({'destination':str(DEST),'source_modules':len(modules),
                  'source_lines':audit['source_lines'],'assets':asset_records}))
