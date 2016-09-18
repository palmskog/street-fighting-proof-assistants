#!/usr/bin/env bash

PPDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IMP="${PPDIR}/../../Imp.native"

if ! [ -f "$IMP" ]; then
  echo "ERROR: could not find $IMP, please build first"
  exit 1
fi

if [ $# -lt 1 ]; then
  echo "Usage: $0 N"
  exit 1
fi

pushd "$PPDIR" > /dev/null
for i in $(seq "$1"); do
  nm="$(printf "r%05d" $(expr $RANDOM % 100000))"
  r="${nm}.imp"
  p="${nm}.p.imp"

  $IMP --rand 1000 > "$r"
  $IMP --pretty "$r" > "$p"

  if cmp -s "$r" "$p"; then
    rm "$r" "$p"
  else
    echo "Discrepency found from $r"
    exit 1
  fi
done
