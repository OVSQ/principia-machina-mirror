#!/bin/sh
# fake_checker.sh: a stand-in for an independent kernel checker (ops/t5/README.md), for
# custos/tests/kernel_checker.php. It keeps the checker's call: the configuration file's path
# as the one argument, the export on stdin. It answers by the export's last line: "CASE accept"
# prints the canned statement and the "Checked" line, exit 0; "CASE wrong" prints another
# statement, exit 0; "CASE axiom" refuses an unpermitted axiom, exit 1; "CASE sleep" runs past
# the test's limit, then accepts. Its digest is in fake_checker.sha256.
[ -r "$1" ] || { echo "no configuration" >&2; exit 2; }
last=$(cat | tail -n 1)
case "$last" in
"CASE accept")
	printf '%s\n' 'theorem Fake.t : 1 + 1 = 2' 'Checked 3 declarations with no errors'
	exit 0 ;;
"CASE wrong")
	printf '%s\n' 'theorem Fake.t : 1 + 1 = 3' 'Checked 3 declarations with no errors'
	exit 0 ;;
"CASE axiom")
	echo 'unpermitted axiom "pmaT5Unpermitted"' >&2
	exit 1 ;;
"CASE sleep")
	sleep 2
	printf '%s\n' 'theorem Fake.t : 1 + 1 = 2' 'Checked 3 declarations with no errors'
	exit 0 ;;
*)
	echo "the stand-in answers four canned exports" >&2
	exit 2 ;;
esac
