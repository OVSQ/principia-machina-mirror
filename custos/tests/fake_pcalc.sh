#!/bin/sh
# fake_pcalc.sh: a stand-in for the Calculator's binary, for Custos's harness and for the
# rehearsal when no pcalc has been built. It keeps pcalc's protocol (Main.lean): one JSON
# value on stdin, one line of canonical JSON on stdout, exit 0; a refusal
# {"detail","refused"} with exit 1 or 2; "pcalc version". It answers one canned request the
# way pcalc does, and two faults the harness needs. Its digest is in fake_pcalc.sha256.
case "$*" in
version)
	echo 0.1.0
	exit 0 ;;
"canonical canonical_json")
	request=$(cat)
	if [ "$request" = '{"value":{"b":1,"a":[2,3]}}' ]; then
		printf '%s\n' '"{\"a\":[2,3],\"b\":1}"'
		exit 0
	fi
	printf '%s\n' '{"detail":"the stand-in answers one canned request","refused":"BAD_ARGUMENT"}'
	exit 1 ;;
"fault exit")
	echo "the stand-in fails on purpose" >&2
	exit 3 ;;
"fault lines")
	printf '1\n2\n'
	exit 0 ;;
*)
	printf '%s\n' '{"detail":"call pcalc <family> <function> with one JSON value on stdin, or pcalc version","refused":"USAGE"}'
	exit 2 ;;
esac
