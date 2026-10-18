"""Make a frozen local commit/tag and upload-ready assets. Never publishes."""
from pathlib import Path
import datetime, hashlib, json, shutil, subprocess, sys, zipfile
ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT/'outputs/ANGULAR_23_24_TIMESTAMP_2026-10-18'
REPO = DEST/'repository'
ASSETS = DEST/'release-assets'
TAG = 'v23-24-2026-10-18'
def sha(p):
    with p.open('rb') as f: return hashlib.file_digest(f,'sha256').hexdigest()
def git(*args):
    return subprocess.check_output(['git','-C',str(REPO),*args],text=True,stderr=subprocess.STDOUT).strip()
assert not (REPO/'.git').exists(), 'Refuse to replace a frozen commit.'
verifier = r'''"""Check published source/evidence integrity; this does not run Lean."""
from pathlib import Path
import argparse, gzip, hashlib, json
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--assets',type=Path,help='Folder containing the three assets listed in RELEASE_ASSETS.json')
p.add_argument('--deep',action='store_true',help='Also verify uncompressed proof-stream hashes; no Lean replay')
args=p.parse_args()
root=Path(__file__).resolve().parent
count=0
for line in (root/'SHA256SUMS').read_text(encoding='utf-8').splitlines():
    digest,name=line.split('  ',1)
    path=(root/name).resolve()
    assert root in path.parents, ('unsafe path',name)
    assert sha(path)==digest, ('file hash mismatch',name)
    count+=1
assets=0
if args.assets:
    for record in json.loads((root/'RELEASE_ASSETS.json').read_text())['assets']:
        path=args.assets/record['file']
        assert path.stat().st_size==record['bytes'], ('asset size',path.name)
        assert sha(path)==record['sha256'], ('asset hash',path.name)
        if args.deep and 'raw_sha256' in record:
            h=hashlib.sha256(); size=0
            with gzip.open(path,'rb') as f:
                for b in iter(lambda:f.read(1024*1024),b''):
                    h.update(b); size+=len(b)
            assert h.hexdigest()==record['raw_sha256'] and size==record['raw_bytes'], path.name
        assets+=1
print(json.dumps({'tracked_files_checked':count,'release_assets_checked':assets,
 'integrity':'PASS','new_lean_replay':False}))
'''
(REPO/'verify_package.py').write_text(verifier,encoding='utf-8')
copy = REPO/'evidence/packaging'
copy.mkdir(parents=True,exist_ok=True)
for name in ['prepare_2324_timestamp.py','write_2324_timestamp_docs.py','finalize_2324_timestamp.py']:
    shutil.copy2(ROOT/'work/angular_lean'/name,copy/name)
paths=sorted(p for p in REPO.rglob('*') if p.is_file())
(REPO/'SHA256SUMS').write_text(''.join(f'{sha(p)}  {p.relative_to(REPO).as_posix()}\n' for p in paths),encoding='utf-8')
validation=subprocess.check_output([sys.executable,str(REPO/'verify_package.py'),'--assets',str(ASSETS)],text=True)
print(validation.strip(),flush=True)
git('init','-b','main')
git('config','core.autocrlf','false')
git('add','--all')
git('commit','-m','Freeze 23/24 angular Hecke source and Windows verification evidence')
commit=git('rev-parse','HEAD')
git('tag','-a',TAG,'-F',str(REPO/'RELEASE_NOTES.md'))
tag_object=git('rev-parse',TAG)
assert git('rev-parse',TAG+'^{}')==commit
assert git('status','--porcelain')==''
bundle=ASSETS/'angular-hecke-23-24.git.bundle'
git('bundle','create',str(bundle),'main',TAG)
bundle_check=git('bundle','verify',str(bundle))
source_zip=ASSETS/'angular-hecke-23-24-source.zip'
git('archive','--format=zip','--prefix=angular-hecke-23-24/','--output='+str(source_zip),commit)
with zipfile.ZipFile(source_zip) as z:
    for p in sorted(REPO.rglob('*')):
        if p.is_file() and '.git' not in p.relative_to(REPO).parts:
            assert hashlib.sha256(z.read('angular-hecke-23-24/'+p.relative_to(REPO).as_posix())).hexdigest()==sha(p)
record={'commit':commit,'tag':TAG,'tag_object':tag_object,'branch':'main',
    'working_tree_clean':True,'git_bundle_verified':True,
    'source_zip_matches_commit':True,'published':False,'upload_by':'user',
    'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(DEST/'FROZEN_COMMIT.json').write_text(json.dumps(record,indent=2)+'\n')
shutil.copy2(REPO/'RELEASE_NOTES.md',DEST/'RELEASE_NOTES.md')
instructions=f'''# Upload-ready 23/24 timestamp package

Frozen commit: `{commit}`
Annotated tag: `{TAG}`
Branch: `main`

This package is LOCAL and has not been published. You will perform the upload.
The source/evidence integrity audit passed, and the Git bundle verifies.
The stronger 0.8748389 theorem remains unfinished. Clean portable reproduction
and Linux replay remain pending. No full 130-module clean rebuild was run.

## Preserve the exact commit and tag

Create an empty GitHub repository in your account. In PowerShell, from this
package folder, replace YOUR-ACCOUNT and YOUR-REPOSITORY below:

```powershell
git clone .\\release-assets\\angular-hecke-23-24.git.bundle angular-hecke-23-24
git -C angular-hecke-23-24 remote set-url origin https://github.com/YOUR-ACCOUNT/YOUR-REPOSITORY.git
git -C angular-hecke-23-24 push -u origin main
git -C angular-hecke-23-24 push origin {TAG}
```

The original workspace's `repository` folder also retains the local Git data.
The upload ZIP contains a plain source copy plus the Git bundle; use the bundle
to preserve the exact commit and tag when transferring it.

Create a GitHub release using the EXISTING tag `{TAG}`. Paste RELEASE_NOTES.md
as the release description. Attach the files in `release-assets`, including
its SHA256SUMS. The three proof/upstream-source assets listed in the committed
RELEASE_ASSETS.json are essential; include the source ZIP and Git bundle too.

## Local integrity check (no Lean build)

```powershell
python .\\repository\\verify_package.py --assets .\\release-assets
```

Add `--deep` to stream-decompress and recheck the raw proof-export hashes.
This checks data integrity, not a fresh proof replay.

## Check after uploading

Confirm the public tag resolves to `{commit}` and that every listed release
asset is present. Download the three essential assets and run the integrity
checker against them. The published commit plus asset hashes identifies the
public timestamp. These post-upload checks have not been performed locally.

CHECKPOINT B for the stronger investigation is a separate local archive and
is intentionally not bundled into this 23/24 public theorem claim.
'''
(DEST/'UPLOAD_INSTRUCTIONS.md').write_text(instructions,encoding='utf-8')
(ASSETS/'SHA256SUMS').write_text(''.join(f'{sha(p)}  {p.name}\n' for p in sorted(ASSETS.iterdir()) if p.is_file()))
(DEST/'SHA256SUMS').write_text(''.join(f'{sha(p)}  {p.relative_to(DEST).as_posix()}\n'
    for p in sorted(DEST.rglob('*')) if p.is_file() and '.git' not in p.relative_to(DEST).parts
    and p!=DEST/'SHA256SUMS'))
outer=ROOT/'outputs/ANGULAR_23_24_UPLOAD_READY.zip'
assert not outer.exists()
with zipfile.ZipFile(outer,'w') as z:
    for p in sorted(DEST.rglob('*')):
        if not p.is_file() or '.git' in p.relative_to(DEST).parts: continue
        compression=zipfile.ZIP_STORED if p.suffix in {'.gz','.zip','.bundle'} else zipfile.ZIP_DEFLATED
        z.write(p,'ANGULAR_23_24_TIMESTAMP/'+p.relative_to(DEST).as_posix(),compress_type=compression)
with zipfile.ZipFile(outer) as z:
    assert z.testzip() is None
(outer.with_suffix('.sha256')).write_text(f'{sha(outer)}  {outer.name}\n')
print(json.dumps({**record,'upload_zip':str(outer),'bytes':outer.stat().st_size,
                  'sha256':sha(outer),'bundle_check':bundle_check}),flush=True)
