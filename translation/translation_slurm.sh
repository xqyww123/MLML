#! /bin/bash
./tools/apply_nodes.py &
pid=$!
trap 'kill $pid; ./tools/bc.py' EXIT
./translation/translator.py origin goal isar-SH*
