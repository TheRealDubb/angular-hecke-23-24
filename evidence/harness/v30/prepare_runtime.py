from pathlib import Path
import hashlib, json
ROOT = Path(__file__).resolve().parents[3]
WORK = ROOT / 'work/angular_lean/v30'
OUT = ROOT / 'outputs/ANGULAR_LEAN/v30'
OUT.mkdir(exist_ok=True)
for name in ['run_native.py', 'replay_shadow_bundle.py', 'package_bundle.py']:
    text = (ROOT / 'work/angular_lean/v29' / name).read_text(encoding='utf-8')
    if name == 'run_native.py':
        text = text.replace("OUT = ROOT / 'outputs/ANGULAR_LEAN/v29'", "OUT = ROOT / 'outputs/ANGULAR_LEAN/v30'")
        text = text.replace('OVERLAYS = [OUT,', "OVERLAYS = [OUT, ROOT / 'outputs/ANGULAR_LEAN/v29',")
    elif name == 'package_bundle.py':
        text = text.replace('v29', 'v30')
        text = text.replace("    old = [pin(p) for p in previous]", "    previous.append(BASE / 'v29/AngularNormTwistBundle.VERIFIED_MANIFEST.json')\n    old = [pin(p) for p in previous]")
    dest = WORK / name
    assert not dest.exists()
    dest.write_text(text, encoding='utf-8')
(WORK / 'principal_exception_bundle.json').write_text(json.dumps({
    'name': 'AngularPrincipalExceptionBundle', 'ready': False,
    'modules': ['AngularTypeZeroEntire', 'AngularFullFamilySeed'],
    'scope': 'Actual type-zero nonprincipal entireness, global identification with the original finite Hecke continuation, nonvanishing at one, and physical 23/24 seed for all angular types and real norm twists with only the principal translated pole excluded. Does not prove 8748389/10000000.'}, indent=2), encoding='utf-8')
paths = ['outputs/ANGULAR_LEAN/v6/AngularFiniteIdentification.lean',
    'outputs/ANGULAR_LEAN/v3/AngularPrimitiveReduction.lean',
    'outputs/ANGULAR_LEAN/v3/AngularThetaFEPair.lean',
    'work/formal/original/lean/OAI/NumberTheory/DirichletL/Hecke/CharacterAnalytic.lean',
    'work/formal/original/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteDeletion.lean',
    'work/formal/original/lean/OAI/NumberTheory/DirichletL/Hecke/BoundaryIntegration.lean']
(OUT / 'SOURCE_PINS.json').write_text(json.dumps({'original_revision':
    'adc7f1241b42e322a6451854ab7e4b4c146bf78a', 'sources': [
    {'path': p, 'sha256': hashlib.sha256((ROOT/p).read_bytes()).hexdigest()} for p in paths]}, indent=2), encoding='utf-8')
