#! /bin/bash
./tools/alloc_servers.py &
pid=$!
trap 'kill $pid; ./tools/bc.py' EXIT
./translation/translator.py origin goal isar-SH*
