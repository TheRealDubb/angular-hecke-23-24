"""Check published source/evidence integrity; this does not run Lean."""
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
