#!/bin/bash
source ./envir.sh
([ -f $(isabelle getenv -b ISABELLE_HOME_USER)/mash_state ] && mv $(isabelle getenv -b ISABELLE_HOME_USER)/mash_state $(isabelle getenv -b ISABELLE_HOME_USER)/mash_state.bak.$(date +%Y%m%d%H%M%S)) || true