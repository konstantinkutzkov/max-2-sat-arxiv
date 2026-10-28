#!/usr/bin/env python3
"""Build the artifact, audit proof dependencies, and record source fingerprints."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
(OUT / 'result.json').unlink(missing_ok=True)

# A result label alone is not enough: flag edits to the statement for a new
# mathematical correspondence review. Proof prose may be edited independently.
paper = ROOT.parent / 'paper' / 'dense_max2sat_arxiv.tex'
if not paper.exists():
    paper = ROOT / 'paper' / 'dense_max2sat_arxiv.tex'
if not paper.exists():
    raise SystemExit('Missing working manuscript or bundled paper snapshot')
paper_text = paper.read_text()
pattern = r'\\begin\{(lemma|theorem|corollary|proposition|target)\}(?:\[([^\]]*)\])?(.*?)\\end\{\1\}'
statements = {}
for match in re.finditer(pattern, paper_text, re.DOTALL):
    labels = re.findall(r'\\label\{([^}]*)\}', match[3])
    if not labels or labels[0] in statements:
        raise SystemExit('Missing or duplicate label on a paper result')
    normalized = ' '.join(match[0].split())
    statements[labels[0]] = hashlib.sha256(normalized.encode()).hexdigest()
correspondence = json.loads((OUT / 'paper-correspondence.json').read_text())
entries = correspondence['results']
if len({entry['paper_label'] for entry in entries}) != len(entries):
    raise SystemExit('Duplicate correspondence entries')
if {entry['paper_label'] for entry in entries} != set(statements):
    raise SystemExit('Paper result labels and correspondence entries differ')
status_counts = {}
for entry in entries:
    if entry['status'] not in {'checked', 'checked_core', 'partial', 'unverified'}:
        raise SystemExit(f'Unknown status for {entry["paper_label"]}')
    if entry['statement_sha256'] != statements[entry['paper_label']]:
        raise SystemExit(f'Review changed paper statement: {entry["paper_label"]}')
    if entry['kind'] == 'target' and (entry['status'] != 'unverified' or entry['lean_declarations']):
        raise SystemExit('A proposed research target must not be marked verified')
    if entry['status'] != 'unverified' and not entry['lean_declarations']:
        raise SystemExit(f'Missing declarations for {entry["paper_label"]}')
    status_counts[entry['status']] = status_counts.get(entry['status'], 0) + 1


def run(args, log):
    result = subprocess.run(args, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    (OUT / log).write_text(result.stdout)
    print(result.stdout, end='', flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


sources = sorted(ROOT.glob('Max2SAT/**/*.lean')) + [ROOT / 'Max2SAT.lean', ROOT / 'Audit.lean', ROOT / 'ExternalAudit.lean']
external = json.loads((OUT / 'external-results.json').read_text())
external_ids = {item['id'] for item in external['results']}
if len(external_ids) != len(external['results']):
    raise SystemExit('Duplicate external result identifiers')
if hashlib.sha256((ROOT / external['statement_module']).read_bytes()).hexdigest() != external['statement_module_sha256']:
    raise SystemExit('Review changed formal statement of a published result')
for theorem, ids in external['conditional_declarations'].items():
    if not ids or not set(ids) <= external_ids:
        raise SystemExit(f'Invalid external dependencies for {theorem}')
for entry in entries:
    if not set(entry.get('external_dependencies', [])) <= external_ids:
        raise SystemExit(f"Unknown external dependency for {entry['paper_label']}")
# The proof-dependency audit below is the primary check. This catches accidental
# placeholders and postulates in the delivered sources before the build starts.
for source in sources:
    text = source.read_text()
    # A structure field such as `constant : ℚ` is not a postulate.
    if re.search(r'\b(sorry|admit)\b|^\s*(axiom|constant|unsafe)\b(?!\s*:)', text, re.MULTILINE):
        raise SystemExit(f'Forbidden placeholder or declaration in {source.relative_to(ROOT)}')

version = run(['lean', '--version'], 'toolchain.log').strip()
run(['lake', 'build', 'Max2SAT', 'Max2SAT.Examples', 'Max2SAT.Bias.Examples', 'Max2SAT.Random.Examples', 'Max2SAT.Random.ProbabilityExamples', 'Max2SAT.Random.ConcentrationExamples', 'Max2SAT.Random.AccumulationExamples', 'Max2SAT.Counts.Examples', 'Max2SAT.Counts.AnalyticsExamples', 'Max2SAT.Counts.RoundExamples', 'Max2SAT.Counts.CompleteExamples', 'Max2SAT.Random.RuntimeExamples', 'Max2SAT.Random.SupportExamples', 'Max2SAT.Regular.Examples', 'Max2SAT.IndependentPairs.Examples', 'Max2SAT.Community.Examples'], 'build.log')
audit = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Audit.lean'], 'axioms.log')
expected = len(re.findall(r'^#print axioms ', (ROOT / 'Audit.lean').read_text(), re.MULTILINE))
records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit, re.DOTALL)
axiom_free = re.findall(r"'([^']+)' does not depend on any axioms", audit)
if len(records) + len(axiom_free) != expected:
    raise SystemExit(f'Incomplete audit: expected {expected}, parsed {len(records)+len(axiom_free)}')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
dependencies = {}
for theorem, raw in records:
    axioms = {x.strip() for x in raw.split(',') if x.strip()}
    if not axioms <= allowed:
        raise SystemExit(f'Unexpected axioms in {theorem}: {sorted(axioms-allowed)}')
    dependencies[theorem] = sorted(axioms)
for theorem in axiom_free:
    dependencies[theorem] = []
for entry in entries:
    for theorem in entry['lean_declarations']:
        if theorem not in dependencies:
            raise SystemExit(f'Unaudited declaration in correspondence: {theorem}')
external_signatures = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'ExternalAudit.lean'], 'external-signatures.log')
for theorem in external['conditional_declarations']:
    if theorem not in dependencies or theorem not in external_signatures:
        raise SystemExit(f'Missing audit or signature for conditional declaration {theorem}')
run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Examples.lean'], 'examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Bias/Examples.lean'], 'bias-examples.log')
run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Random/Examples.lean'], 'random-examples.log')
run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Random/ProbabilityExamples.lean'], 'probability-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Random/ConcentrationExamples.lean'], 'concentration-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Random/AccumulationExamples.lean'], 'accumulation-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Counts/Examples.lean'], 'count-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Counts/AnalyticsExamples.lean'], 'count-analytics-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Counts/RoundExamples.lean'], 'count-round-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Counts/CompleteExamples.lean'], 'count-complete-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Random/RuntimeExamples.lean'], 'runtime-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Random/SupportExamples.lean'], 'support-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Regular/Examples.lean'], 'regular-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/IndependentPairs/Examples.lean'], 'independent-pairs-examples.log')

run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Max2SAT/Community/Examples.lean'], 'community-examples.log')

manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
package_revisions = {}
for package in manifest['packages']:
    directory = ROOT / '.lake' / 'packages' / package['name']
    head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
    if head != package['rev']:
        raise SystemExit(f'Dependency revision mismatch for {package["name"]}')
    dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain'], text=True)
    if dirty:
        raise SystemExit(f'Modified dependency checkout: {package["name"]}')
    package_revisions[package['name']] = head

files = sources + [ROOT / name for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'verify.py', 'README.md', 'verification/BIAS_PROOF.txt', 'verification/RANDOM_CORRECTNESS.txt', 'verification/RANDOM_PROBABILITY.txt', 'verification/RANDOM_EXPOSURE.txt', 'verification/RANDOM_MOMENTS.txt', 'verification/RANDOM_CONCENTRATION.txt', 'verification/RANDOM_ACCUMULATION.txt', 'verification/RANDOM_RUNTIME.txt', 'verification/RANDOM_COMPLETE.txt', 'verification/COUNT_GUESSING.txt', 'verification/COUNT_ANALYTICS.txt', 'verification/COUNT_ROUNDS.txt', 'verification/COUNT_COMPLETE.txt', 'verification/REGULAR_GRAPHS.txt', 'verification/INDEPENDENT_PAIRS_SCALAR.txt', 'verification/EXTERNAL_RESULTS.txt', 'verification/INDEPENDENT_PAIR_MEMBERSHIP.txt', 'verification/COMMUNITY_PREPROCESSING.txt', 'verification/COMMUNITY_ASSEMBLY.txt', 'verification/SPECTRAL_TRUNCATION.txt', 'verification/RATIONAL_DIAGONALIZATION.txt', 'verification/SBM_COMPLETE.txt', 'verification/SUBMISSION_SCOPE.txt', 'verification/external-results.json', 'verification/paper-correspondence.json')]
fingerprints = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
report = {
    'status': 'PASS',
    'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'lean': version,
    'audited_theorems': len(dependencies),
    'allowed_standard_axioms': sorted(allowed),
    'theorem_dependencies': dependencies,
    'external_mathematical_dependencies': external,
    'dependency_revisions': package_revisions,
    'source_sha256': fingerprints,
    'manuscript_reference': {'file': paper.name, 'sha256': hashlib.sha256(paper.read_bytes()).hexdigest()},
    'paper_result_status_counts': status_counts,
    'scope': 'All 34 numbered proved statements have checked mathematical content: 23 checked and 11 checked_core, with no partial entries. The sole unverified numbered statement is the explicitly unproved biased-subset research target. Actual algorithm correctness, reductions, constraint arithmetic, enumeration and exponential search-node bounds are checked for all four main families and the proved appendix results. The independent-pair auxiliary proposition is now explicitly scoped to integer coefficients, as in every computational input model in the paper; the earlier additional assertion for arbitrary continuously distributed real coefficients is not claimed. This changes no Max 2-SAT/Max Cut input family. General original probability spaces, almost-sure integer bounds, independent product transport, exact expectations and ordinary variance are checked. Discovery yields a measurable good event uniform in all subsequently chosen units, with one fixed base c<2 and constants for every size. Two published probability estimates remain explicit hypotheses, with source quotations and their applications audited separately. No internal proof obligation is classified as external. Standard-axiom checking does not prove those hypotheses. Polynomial bit-operation overhead and polynomial space remain conventional manuscript arguments, not machine-cost or compiler proofs. The registry and fingerprints track intended paper correspondence; independent review of its semantic correctness remains distinct from kernel checking. See SUBMISSION_SCOPE.txt for the final boundary; older milestone notes record historical states.'
}
(OUT / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
print(f'PASS: {len(dependencies)} audited theorems; only permitted standard axioms; {len(external_ids)} explicitly recorded published-result hypotheses.', flush=True)
