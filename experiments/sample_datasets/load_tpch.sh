#!/usr/bin/env bash
# Generate TPC-H with the official dbgen and load it in file order.
# Usage: load_tpch.sh <dbgen folder> <scale factor> <database> [psql options]
#   e.g. load_tpch.sh ~/tpch-dbgen 0.1 tpch_sf01
set -euo pipefail
DBGEN=$1; SCALE=$2; DB=$3; shift 3
HERE=$(cd "$(dirname "$0")" && pwd)
DATA=$(mktemp -d)
trap 'rm -rf "$DATA"' EXIT
psql() { command psql -X -q -v ON_ERROR_STOP=1 "$@"; }

echo "generating TPC-H scale factor $SCALE"
(cd "$DBGEN" && DSS_PATH="$DATA" ./dbgen -s "$SCALE" -f -q)
psql "$@" -d postgres -c "CREATE DATABASE $DB"
psql "$@" -d "$DB" -f "$HERE/tpch_tables.sql"
for table in region nation supplier customer part partsupp orders lineitem; do
  sed 's/|$//' "$DATA/$table.tbl" | psql "$@" -d "$DB" -c "\copy $table FROM stdin WITH (FORMAT text, DELIMITER '|')"
  echo "loaded $table"
done
psql "$@" -d "$DB" <<SQL
ALTER TABLE region   ADD PRIMARY KEY (r_regionkey);
ALTER TABLE nation   ADD PRIMARY KEY (n_nationkey);
ALTER TABLE supplier ADD PRIMARY KEY (s_suppkey);
ALTER TABLE customer ADD PRIMARY KEY (c_custkey);
ALTER TABLE part     ADD PRIMARY KEY (p_partkey);
ALTER TABLE partsupp ADD PRIMARY KEY (ps_partkey, ps_suppkey);
ALTER TABLE orders   ADD PRIMARY KEY (o_orderkey);
ALTER TABLE lineitem ADD PRIMARY KEY (l_orderkey, l_linenumber);
VACUUM ANALYZE;
SQL
echo "database $DB ready"
