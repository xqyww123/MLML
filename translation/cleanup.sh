#!/bin/bash
./init.sh &&
# Continue even if mv fails (file doesn't exist)
(([ -f ./cache/translation/results.db ] && mv ./cache/translation/results.db ./cache/translation/results.db.bak.$(date +%Y%m%d_%H%M%S)) || true) &&
(([ -f ./cache/translation/declarations.db ] && mv ./cache/translation/declarations.db ./cache/translation/declarations.db.bak.$(date +%Y%m%d_%H%M%S)) || true) &&
echo "Restarting servers..." &&
./tools/restart_all_servers.py &&
./translation/clean_mash.sh &&
echo "Cleaning up finished"

