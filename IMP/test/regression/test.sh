#!/usr/bin/env bash

TDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IMP="${TDIR}/../../Imp.native"

# ANSI color codes
BK=$'\033[1;30m' # black
RD=$'\033[1;31m' # red
GR=$'\033[1;32m' # green
YL=$'\033[1;33m' # yellow
BL=$'\033[1;34m' # blue
MG=$'\033[1;35m' # magenta
CY=$'\033[1;36m' # cyan
WT=$'\033[1;37m' # white
NC=$'\033[0m'    # no color

PASS="PASS"
FAIL="FAIL"

# only output color for ttys
if [ -t 1 ]; then
  PASS="${GR}PASS${NC}"
  FAIL="${RD}FAIL${NC}"
fi

if ! [ -f "$IMP" ]; then
  echo "ERROR: could not find $IMP, please build first"
  exit 1
fi

function rand_bool {
  if [ "$(expr $RANDOM % 2)" -eq 0 ]; then
    echo "True"
  else
    echo "False"
  fi
}

function rand_int {
  if [ "$(expr $RANDOM % 2)" -eq 0 ]; then
    printf "-"
  fi
  expr $RANDOM % 100
}

function get_input {
  case $1 in
    "fact.imp")
      echo $(rand_int)
      ;;
    "fib.imp")
      echo $(rand_int)
      ;;
    "inputs.imp")
      echo $(rand_int)
      echo $(rand_int)
      echo $(rand_bool)
      echo $(rand_bool)
      ;;
    "sort.imp")
      echo $(rand_int)
      ;;
    "swap.imp")
      echo $(rand_int)
      echo $(rand_int)
      ;;
    "sum.imp")
      echo $(rand_int)
      ;;
    "minimal.imp")
      ;;
    *)
      echo "ERROR: do not know how to set up input for $1"
      exit 1
      ;;
  esac
}

function run_test {
  inp="$1.input"
  res="$1.result"
  get_input $(basename "$1") > "$inp"
  cat "$inp" | $IMP --test "$1" > "$res"
}

for p in ${TDIR}/*.imp; do
  printf "%-20s" "$(basename "$p")"
  if run_test "$p"; then
    echo "$PASS"
  else
    echo "$FAIL"
  fi
done
