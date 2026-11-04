#!/usr/bin/env python3
"""Build Memento's offline rank artifacts for one database (Section 5.1).

The artifacts depend only on which columns the policies mention, never on
their operators or constants. One build serves every binding of every policy
in the workload.

    python3 memento_artifacts.py --db tpch --workload experiments/workloads/tpch \
        --out artifacts/tpch --run-id tpch

Steps:
  1. collect the columns the policy templates mention and group columns that
     the policies compare with each other into one rank universe
  2. extract per-column ranks, dictionaries and row ids inside PostgreSQL
  3. merge each group into one universe of ranks (emit_universe)
  4. keep the files the engine reads and load them into the files table

Only the psql client and the two builder binaries (make builder) are needed.
"""
import argparse
import base64
import collections
import hashlib
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = pathlib.Path(__file__).resolve().parent
EXTENSION = HERE / 'build' / 'artifact_builder.so'
UNIVERSE = HERE / 'build' / 'emit_universe'
ENGINE_FILES = re.compile(r'(?:universe/domain/[^/]+|canon_(?:fwdidx|invidx)/[^/]+/[^/]+'
                          r'|meta/(?:col_domain|join_classes|cols/[^/]+)|[^/]+_ctid)\Z')
REPLACED = ('canon_invidx/', 'canon_fwdidx/', 'rank/domain/', 'meta/canon_invidx')


def step(text):
    print(f'[{time.strftime("%H:%M:%S")}] {text}', flush=True)


class Database:
    def __init__(self, args):
        self.command = ['psql', '-X', '-q', '-v', 'ON_ERROR_STOP=1', '-d', args.db]
        if args.host: self.command += ['-h', args.host]
        if args.port: self.command += ['-p', str(args.port)]

    def run(self, script, *extra):
        result = subprocess.run(self.command + ['-At', '-F', '\t'] + list(extra), input=script,
                                text=True, capture_output=True)
        if result.returncode:
            raise SystemExit('psql failed:\n' + result.stderr)
        return result.stdout


def definition(workload, db):
    """Columns the policies mention, and the groups compared with each other."""
    templates = sorted(workload.rglob('policy_template.txt'))
    if not templates:
        raise SystemExit(f'No policy_template.txt under {workload}')
    columns, edges = set(), set()
    for path in templates:
        text = path.read_text()
        aliases = dict(re.findall(r'^occ\s+(\w+):\s*(\w+)\s*$', text, re.M))
        physical = lambda v: aliases.get(v.split('.')[0], v.split('.')[0]) + '.' + v.split('.')[1]
        for line in text.splitlines():
            if not line.startswith('atom '):
                continue
            atom = line.split(':', 1)[1].split()
            left = physical(atom[0]); columns.add(left)
            if re.fullmatch(r'\w+\.\w+', atom[2]):
                right = physical(atom[2]); columns.add(right); edges.add((left, right))
    parent = {c: c for c in columns}

    def find(c):
        while parent[c] != c:
            parent[c] = parent[parent[c]]; c = parent[c]
        return c
    for a, b in sorted(edges):
        a, b = find(a), find(b); parent[max(a, b)] = min(a, b)
    groups = collections.defaultdict(list)
    for c in sorted(columns):
        groups[find(c)].append(c)
    tables = sorted({c.split('.')[0] for c in columns})
    rows = db.run("SELECT c.relname||'.'||a.attname, format_type(a.atttypid,a.atttypmod) "
                  "FROM pg_attribute a JOIN pg_class c ON c.oid=a.attrelid "
                  "JOIN pg_namespace n ON n.oid=c.relnamespace "
                  f"WHERE n.nspname='public' AND c.relname IN ({','.join(repr(t) for t in tables)}) "
                  "AND a.attnum>0 AND NOT a.attisdropped")
    types = dict(line.split('\t') for line in rows.splitlines())
    missing = sorted(c for c in columns if c not in types)
    if missing:
        raise SystemExit('Columns not found in public schema: ' + ', '.join(missing))
    return dict(templates=len(templates), tables=tables, columns=sorted(columns),
                universes=sorted(groups.values()), types={c: types[c] for c in columns})


def requirements(d):
    """The extraction input: one equality atom per column, one per universe link."""
    lines = ['policy 1', 'target: ' + d['tables'][0]] + ['occ ' + t + ': ' + t for t in d['tables']]
    atoms = [c + " = '0'" for c in d['columns']]
    atoms += [g[0] + ' = ' + c for g in d['universes'] for c in g[1:]]
    return '\n'.join(lines + [f'atom a{i}: {a}' for i, a in enumerate(atoms, 1)] + ['end']) + '\n'


def kinds(base, d):
    """Value kind per universe: 0 text/date, 1 exact number, 2 floating point."""
    result = {}
    for line in (base / 'meta/col_domain').read_text().splitlines():
        if not line:
            continue
        column, domain = line.split('=', 1)
        declared = d['types'][column]
        kind = 2 if declared in ('real', 'double precision') else \
            1 if declared.startswith(('smallint', 'integer', 'bigint', 'numeric', 'decimal')) else 0
        result[domain] = max(result.get(domain, 0), kind)
    return ''.join(f'{domain}={kind}\n' for domain, kind in sorted(result.items()))


def extract(db, inputs, base):
    """Per-column ranks, dictionaries and row ids, written by the PostgreSQL extension."""
    db.run(f"""
CREATE SCHEMA IF NOT EXISTS memento_build;
CREATE OR REPLACE FUNCTION memento_build.build_base(text) RETURNS void
  AS '{EXTENSION}', 'build_base' LANGUAGE C;
CREATE OR REPLACE FUNCTION memento_build.emit_invidx() RETURNS void
  AS '{EXTENSION}', 'emit_invidx' LANGUAGE C;
DROP TABLE IF EXISTS memento_build.base_files;
CREATE TABLE memento_build.base_files (run_id text, name text, file bytea);
SET work_mem = '1GB';
SET maintenance_work_mem = '1GB';
LOAD '{EXTENSION}';
SET custom_filter_new.run_id = 'base';
SET custom_filter_new.files_table = 'memento_build.base_files';
SELECT memento_build.build_base('{inputs}');
SELECT memento_build.emit_invidx();
""")
    dump = db.run("\\copy (SELECT name, encode(file,'base64') FROM memento_build.base_files) TO stdout")
    count = 0
    for line in dump.splitlines():
        name, payload = line.split('\t', 1)
        if name.startswith('/') or '..' in name.split('/'):
            raise SystemExit('Unsafe artifact name: ' + name)
        path = base / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(base64.b64decode(payload.replace('\\n', '')))
        count += 1
    db.run('DROP TABLE memento_build.base_files;')
    return count


def assemble(base, universe, out):
    """Keep only the files the engine reads: universes, rank columns, inverted indexes, row ids."""
    files = {}
    for root, keep in ((universe, lambda n: True), (base, lambda n: not n.startswith(REPLACED))):
        for path in sorted(root.rglob('*')):
            name = str(path.relative_to(root))
            if path.is_file() and keep(name) and name not in files and ENGINE_FILES.fullmatch(name):
                files[name] = path
    for name, path in files.items():
        target = out / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    return sorted(files)


def load(db, out, names, table, run_id):
    """One row per file in the table the engine reads at query time."""
    schema = table.split('.')[0] if '.' in table else 'public'
    with tempfile.NamedTemporaryFile('w', suffix='.tsv') as rows:
        for name in names:
            rows.write(name + '\t' + base64.b64encode((out / name).read_bytes()).decode() + '\n')
        rows.flush()
        db.run(f"""
CREATE SCHEMA IF NOT EXISTS {schema};
CREATE TABLE IF NOT EXISTS {table} (run_id text NOT NULL, name text NOT NULL, file bytea NOT NULL,
                                    PRIMARY KEY (run_id, name));
DELETE FROM {table} WHERE run_id = '{run_id}';
CREATE TEMP TABLE incoming (name text, payload text);
\\copy incoming FROM '{rows.name}'
INSERT INTO {table} SELECT '{run_id}', name, decode(payload, 'base64') FROM incoming;
""")
    stored = db.run(f"SELECT name, encode(sha256(file),'hex') FROM {table} WHERE run_id = '{run_id}'")
    stored = dict(line.split('\t') for line in stored.splitlines())
    for name in names:
        if stored.get(name) != hashlib.sha256((out / name).read_bytes()).hexdigest():
            raise SystemExit('Stored artifact differs from file: ' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--db', required=True, help='PostgreSQL database holding the data')
    parser.add_argument('--host'); parser.add_argument('--port', type=int)
    parser.add_argument('--workload', required=True, type=pathlib.Path,
                        help='folder with one policy_template.txt per policy')
    parser.add_argument('--out', required=True, type=pathlib.Path, help='new folder for the artifacts')
    parser.add_argument('--run-id', required=True, help='name of this artifact set in the files table')
    parser.add_argument('--files-table', default='memento.files')
    args = parser.parse_args()
    for binary in (EXTENSION, UNIVERSE):
        if not binary.exists():
            raise SystemExit(f'Missing {binary}. Run "make builder" first.')
    if args.out.exists():
        raise SystemExit(f'{args.out} already exists')
    db = Database(args)
    started = time.time()

    d = definition(args.workload.resolve(), db)
    step(f"{d['templates']} policies mention {len(d['columns'])} columns of {len(d['tables'])} tables, "
         f"grouped into {len(d['universes'])} rank universes")
    # The PostgreSQL server reads the requirements file, so keep the work folder
    # beside the output rather than in a private temporary directory.
    work = args.out.resolve().with_name(args.out.name + '.build')
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    try:
        inputs = work / 'requirements.txt'
        inputs.write_text(requirements(d))
        base = work / 'base'
        count = extract(db, inputs, base)
        step(f'extracted {count} per-column files (ranks, dictionaries, row ids)')
        (work / 'kinds.txt').write_text(kinds(base, d))
        subprocess.run([str(UNIVERSE), str(base), str(work / 'universe'), str(work / 'kinds.txt')],
                       check=True, stdout=subprocess.DEVNULL)
        step(f'merged columns into {len(d["universes"])} rank universes')
        args.out.mkdir(parents=True)
        names = assemble(base, work / 'universe', args.out)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    size = sum((args.out / n).stat().st_size for n in names)
    step(f'kept {len(names)} files, {size / 2**20:.1f} MiB, in {args.out}')
    load(db, args.out, names, args.files_table, args.run_id)
    step(f"loaded into {args.files_table} as run '{args.run_id}' ({time.time() - started:.1f} s total)")


if __name__ == '__main__':
    sys.exit(main())
