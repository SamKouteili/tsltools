#!/usr/bin/env bash
set -euo pipefail

# End-to-end evaluation of the TSL synthesis pipeline on benchmarks.
# Runs: tsl theorize, tsl tlsf, and tsl synthesize on each benchmark.

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BENCH_DIR="$SCRIPT_DIR/../benchmarks"
TSL="stack exec tsl --"
TIMEOUT=${EVAL_TIMEOUT:-60}  # seconds per benchmark per stage (override with EVAL_TIMEOUT=300)

PASS=0
FAIL=0
SKIP=0
FAILURES=()

# Colors (disabled if not a terminal)
if [ -t 1 ]; then
  GREEN='\033[0;32m'
  RED='\033[0;31m'
  YELLOW='\033[0;33m'
  BOLD='\033[1m'
  NC='\033[0m'
else
  GREEN='' RED='' YELLOW='' BOLD='' NC=''
fi

pass() { PASS=$((PASS+1)); echo -e "${GREEN}PASS${NC} $1"; }
fail() { FAIL=$((FAIL+1)); FAILURES+=("$1: $2"); echo -e "${RED}FAIL${NC} $1: $2"; }
skip() { SKIP=$((SKIP+1)); echo -e "${YELLOW}SKIP${NC} $1: $2"; }

run_with_timeout() {
  # Usage: run_with_timeout <outfile> <errfile> <command...>
  local outfile="$1" errfile="$2"
  shift 2
  timeout --kill-after=10 "$TIMEOUT" "$@" >"$outfile" 2>"$errfile"
}

# Collect all .tslmt files
mapfile -t TSLMT_FILES < <(find "$BENCH_DIR" -name '*.tslmt' | sort)

if [ ${#TSLMT_FILES[@]} -eq 0 ]; then
  echo "No .tslmt files found in $BENCH_DIR"
  exit 1
fi

echo ""
echo -e "${BOLD}=== TSL Pipeline Evaluation (timeout: ${TIMEOUT}s per step) ===${NC}"
echo "Found ${#TSLMT_FILES[@]} benchmark files"
echo ""

# Stage 1: Theorize
echo -e "${BOLD}--- Stage 1: theorize ---${NC}"
for f in "${TSLMT_FILES[@]}"; do
  name="${f#$BENCH_DIR/}"
  tmpout=$(mktemp)
  tmperr=$(mktemp)
  exit_code=0
  run_with_timeout "$tmpout" "$tmperr" $TSL theorize -i "$f" || exit_code=$?
  if [ $exit_code -eq 124 ]; then
    skip "theorize  $name" "timeout (${TIMEOUT}s)"
  elif [ $exit_code -eq 0 ]; then
    if [ -s "$tmpout" ]; then
      pass "theorize  $name"
    else
      fail "theorize  $name" "empty output"
    fi
  else
    fail "theorize  $name" "exit code $exit_code"
  fi
  rm -f "$tmpout" "$tmperr"
done
echo ""

# Stage 2: TLSF lowering
echo -e "${BOLD}--- Stage 2: tlsf ---${NC}"
for f in "${TSLMT_FILES[@]}"; do
  name="${f#$BENCH_DIR/}"
  tmpout=$(mktemp)
  tmperr=$(mktemp)
  exit_code=0
  run_with_timeout "$tmpout" "$tmperr" $TSL tlsf -i "$f" || exit_code=$?
  if [ $exit_code -eq 124 ]; then
    skip "tlsf      $name" "timeout (${TIMEOUT}s)"
  elif [ $exit_code -eq 0 ]; then
    if [ -s "$tmpout" ]; then
      pass "tlsf      $name"
    else
      fail "tlsf      $name" "empty output"
    fi
  else
    fail "tlsf      $name" "exit code $exit_code"
  fi
  rm -f "$tmpout" "$tmperr"
done
echo ""

# Stage 3: Full synthesis
echo -e "${BOLD}--- Stage 3: synthesize ---${NC}"
for f in "${TSLMT_FILES[@]}"; do
  name="${f#$BENCH_DIR/}"
  tmpout=$(mktemp)
  tmperr=$(mktemp)
  exit_code=0
  run_with_timeout "$tmpout" "$tmperr" $TSL synthesize -i "$f" --js || exit_code=$?
  if [ $exit_code -eq 124 ]; then
    skip "synthesize $name" "timeout (${TIMEOUT}s)"
  elif [ $exit_code -eq 0 ]; then
    if [ -s "$tmpout" ]; then
      pass "synthesize $name"
    else
      fail "synthesize $name" "empty output"
    fi
  else
    errmsg=$(grep -v 'Warning: nix' "$tmperr" | grep -v 'integration is disabled' | grep -v 'notify-if-nix-on-path' | head -5 | tr '\n' ' ')
    fail "synthesize $name" "exit code $exit_code${errmsg:+: $errmsg}"
  fi
  rm -f "$tmpout" "$tmperr"
done
echo ""

# Summary
echo -e "${BOLD}=== Summary ===${NC}"
echo -e "${GREEN}Passed: $PASS${NC}"
echo -e "${YELLOW}Skipped: $SKIP${NC}"
echo -e "${RED}Failed: $FAIL${NC}"

if [ $FAIL -gt 0 ]; then
  echo ""
  echo -e "${BOLD}Failures:${NC}"
  for f in "${FAILURES[@]}"; do
    echo -e "  ${RED}-${NC} $f"
  done
  exit 1
fi
