#!/usr/bin/env python3
"""Run one policy with Memento and, optionally, the same policy as plain SQL.

    python3 experiments/run_memento.py --db tpch --run-id tpch \
        experiments/workloads/tpch/T05 --check

Memento needs the engine library (make), the artifacts of the database
(src/ranks/builder/memento_artifacts.py) and the policy folder, which holds
the template, its binding and the query.
"""
import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIBRARY = ROOT / 'build' / 'clean' / 'custom_filter_new.memento.so'
SETTINGS = ROOT / 'src' / 'postgres' / 'paper_settings.sql'


def psql(args, script):
    command = ['psql', '-X', '-q', '-At', '-v', 'ON_ERROR_STOP=1', '-d', args.db]
    if args.host: command += ['-h', args.host]
    if args.port: command += ['-p', str(args.port)]
    result = subprocess.run(command, input=script, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stderr.strip())
    return result.stdout


def timed(output):
    lines = [l for l in output.splitlines() if l.strip()]
    count = next(l for l in lines if re.fullmatch(r'\d+', l))
    ms = float(re.search(r'Time: ([\d.]+) ms', output)[1])
    return int(count), ms


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('policy', type=pathlib.Path, help='folder with policy_template.txt, policy_binding.txt, query.txt')
    parser.add_argument('--db', required=True); parser.add_argument('--host'); parser.add_argument('--port', type=int)
    parser.add_argument('--run-id', required=True, help='artifact set built for this database')
    parser.add_argument('--files-table', default='memento.files')
    parser.add_argument('--library', type=pathlib.Path, default=LIBRARY)
    parser.add_argument('--check', action='store_true', help='also run correlated.sql in plain PostgreSQL')
    args = parser.parse_args()
    folder = args.policy.resolve()
    target = re.search(r'^target:\s*(\w+)', (folder / 'policy_template.txt').read_text(), re.M)[1]
    script = f"""
SET max_parallel_workers_per_gather = 0;
SET client_min_messages = warning;
LOAD '{args.library}';
SET custom_filter_new.enabled = off;
{SETTINGS.read_text()}
SET custom_filter_new.files_table = '{args.files_table}';
SET custom_filter_new.run_id = '{args.run_id}';
SET custom_filter_new.policy_template_path = '{folder / 'policy_template.txt'}';
SET custom_filter_new.policy_binding_path = '{folder / 'policy_binding.txt'}';
SET custom_filter_new.query_path = '{folder / 'query.txt'}';
SET custom_filter_new.enabled = on;
\\timing on
SELECT count(*) FROM public.{target};
"""
    count, ms = timed(psql(args, script))
    print(f'{folder.name:>12}  Memento     {count:>12,} rows  {ms:10.1f} ms')
    if args.check:
        sql = (folder / 'correlated.sql').read_text()
        plain, plain_ms = timed(psql(args, 'SET max_parallel_workers_per_gather = 0;\n\\timing on\n' + sql))
        print(f'{folder.name:>12}  PostgreSQL  {plain:>12,} rows  {plain_ms:10.1f} ms  '
              + ('same answer' if plain == count else 'DIFFERENT ANSWER'))
        if plain != count:
            sys.exit(1)


if __name__ == '__main__':
    main()
