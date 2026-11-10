#!/usr/bin/env bash
# rehearsal.sh: Custos on a throwaway MediaWiki 1.46.2 (SQLite), without the host.
#
#   bash custos/tests/rehearsal.sh [<MediaWiki folder>]
#   CUSTOS_TAMPER=1 bash custos/tests/rehearsal.sh [<MediaWiki folder>]
#   bash custos/tests/rehearsal.sh --install-residence <account> [<account> ...]   (root, once, on the rehearsal host)
#
# The folder: one that holds LocalSettings.php is used as installed (the test gate installs
# it first, gates.py's MEDIAWIKI block); one that holds MediaWiki's sources is installed; an
# absent or empty one is filled from $MW_TARBALL when that is set (its SHA-256 checked against
# $MW_SHA256, else rehearsal.json's), else by `git clone --depth 1` of MediaWiki's tag and its
# vendor tree's Git branch, each checked against the commit rehearsal.json pins. No folder:
# <scratch>/mediawiki. The scratch folder is $CUSTOS_WORK, else a new temporary folder; the
# database, the Calculator's binary and the logs live there, outside the web root.
#
# Then: Custos linked into extensions/, LocalSettings.php given wfLoadExtension('Custos') and
# $wgJobRunRate = 0, the binary (the built pcalc from .lake/build/bin/pcalc when this clone has
# one, else the stand-in fake_pcalc.sh) and its digest written to LocalSettings.custos.php;
# wiring.php run under maintenance/run.php ("wiring: ALL PASS", "calculator: version <v>, digest
# match"); the wiki served by `php -S 127.0.0.1:$CUSTOS_PORT` (8080) and its ops asked over HTTP by an
# agent account of the group pma-agent ("api: PETITION 202", "api: POLL QUEUED", "api: PUSH 202",
# "api: RELEASE 202", "api: STRUCTURE_TEST 202", then the refusals); then Custos:SeedUwc writes a UWC's seven pages from v1's spring draft
# ("seed: 7 pages", each page the system user Custos's, the INDEX AND BADGE page last) and the agent's direct edit of
# its register is refused by the permission hook ("hook: edit refused custos-governed-page"), and a read of a page in the
# restricted namespace, registered as 7240, by the agent and by an anonymous request ("hook: Restricted read refused"), then the
# restricted routes: a restricted page written as Custos, read around the hook by the agent account by each route, one line each
# ("restricted: transclusion refused", "restricted: search shows nothing", "restricted: export refused", "restricted: raw refused",
# "restricted: API revisions refused", "restricted: history refused", "restricted: recent changes show nothing",
# "restricted: random refused", "restricted: REST search refused", "restricted: moves show nothing",
# "restricted: redirects show nothing", "restricted: redirect to it refused"), and by an account
# of the Declarer's group by its title ("restricted: read admitted", transclusion still refused); before that, update.php makes the table custos_ticket and
# generateSchemaSql must reproduce each table's sql/<type>/<table>.sql from its sql/<table>.json ("schema: current"),
# and a second scratch wiki installed with custos_ticket alone gains custos_seat, custos_certificate, custos_job_run,
# custos_nonce, custos_meter, custos_budget and custos_traffic by update.php ("schema: custos_seat, custos_certificate,
# custos_job_run, custos_nonce, custos_meter, custos_budget and custos_traffic added by update to a wiki that had
# custos_ticket alone"); the agent account and a second account each given a certificate by
# Custos:Certify, their Sponsor a third account ("certify: Rehearsalagent sponsor Rehearsalsponsor"), so admission
# reads a Sponsor for each; then
# the same wiring with a tampered copy of the binary, which must print "DIGEST MISMATCH" and
# fail, and with a group-writable copy, which must print "UNSAFE RESIDENCE" and fail. With
# CUSTOS_TAMPER=1 only the tampered pass runs: its output, then exit 1, or exit 2 when the
# tampered landing was not halted as it must be, so that failure is not read as the pass.
# With the built pcalc, after the seed: the landing job's path over HTTP (PETITION, PUSH of the spring UWC's
# first RESULT and ASSUMPTION, RELEASE), each followed by `runJobs --type custosLand` and POLL ("land: PETITION
# grant", "structure: line <the line> equal to the Calculator's answer" for the holder's STRUCTURE_TEST, compared
# with the rehearsal's own call of pcalc eom eom_register_test over the pages, "land: PUSH CHALLENGE REASONED" for a wrong answer to the challenge, "land: PUSH landed EXECUTED" for the
# Research Client's answer, "land: RELEASE released"), the register page read back over api.php ("land: READ
# 2 records": each with its DIGEST, the RESULT with DERIVATION_CLASS INSPECTION, the ASSUMPTION with none); after the grant, a second account's PETITION while the lock is held, run by Custos:Land, answered LOCK
# HELD with a poll_after between the base and the base plus 10 per cent ("land: LOCK HELD poll_after jittered"); after
# the release, a scratch agent account whose name has a space, an apostrophe and a letter outside ASCII petitions,
# is granted and releases, the LOCK PAGE read back through pcalc naming it exactly ("lock: holder carried exactly"); then the sweep: a ticket written QUEUED with no job by Custos:Ticket --new, with $wgCustosSweepAfter = 0
# POLLed over HTTP, the job runner run, and POLL answering it ("sweep: a QUEUED ticket without its job, re-enqueued
# on POLL, answered"); after the sweep, the batch jobs' frame: Custos:Job --job for each of the three, runJobs, Custos:Job --last ("job: reaudit NOTHING DUE", cluster, recheck), then $wgCustosBatch pressure STRAINED and the re-audit ending DEFERRED ("job: refused DEFERRED"); and in the tampered pass a landing run by Custos:Land with the tampered binary, which must halt
# (DIGEST MISMATCH, the ticket answered INTEGRITY HALT) and leave the register page unchanged.
#
# The residence (no override of the check): the wiki's side runs the live check, under /opt and
# /usr with every property, here as on the host; nothing switches it. So the binary is placed
# under /opt, root's, 0755 throughout, and every PHP process runs as a user other than root (the
# check refuses root, who can write every file). Run as root (the cloud worker's container): the
# rehearsal makes its own folder /opt/pma-rehearsal/run.<x>, places the binaries there and removes
# that folder at its end, and runs PHP as uid and gid 65534 by setpriv, the scratch folder and the
# MediaWiki folder handed to that user. Run as any other user (the rehearsal host's gate account): PHP runs
# as that user, and the binaries are placed in /opt/pma-rehearsal/bin by the root-owned helper
# /usr/local/sbin/pma-rehearsal-residence through its sudo rule; the Operator installs both once,
# as root: `bash custos/tests/rehearsal.sh --install-residence <every local gate account>` (the host
# set-up's act residence, its step hostprep, runs it with every one). Without them
# the rehearsal cannot be set up (exit 2) and says that command. The tampered passes swap the
# tampered bytes in at the residence's pcalc and put the true binary back, in a trap as well.
#
# Exit 0: "rehearsal: ALL PASS". Exit 1: a check failed (or the tampered pass, as asked).
# Exit 2: the rehearsal could not be set up (the sources, the install); with CUSTOS_TAMPER=1, also
# the tampered landing not halted.
set -euo pipefail

helper=/usr/local/sbin/pma-rehearsal-residence

# --install-residence <account> [<account> ...]: the Operator's one act on the rehearsal host, as root
# (the host set-up's act residence runs it). Writes the helper (a binary from standard input into
# /opt/pma-rehearsal/bin/<name>, root's; three names only, each with its mode), one sudo rule file,
# one line per account in name order, letting each account run it with those three arguments alone,
# and /opt/pma-rehearsal/accounts, the accounts named, one per line in name order (mode 0644). The rule
# and the list are each written under a temporary name and renamed whole.
# Every account is checked before anything is written: a name that is not a Linux account's, or an
# account absent here, ends 2 and leaves the files as they were. The same accounts again write the
# same bytes.
if [ "${1:-}" = --install-residence ]; then
	shift
	[ "$(id -u)" = 0 ] || { echo "rehearsal: --install-residence runs as root" >&2; exit 2; }
	[ "$#" -gt 0 ] || { echo "rehearsal: --install-residence names one account or more" >&2; exit 2; }
	for account in "$@"; do
		[[ "$account" =~ ^[a-z_][a-z0-9_-]{0,31}$ ]] || { echo "rehearsal: not an account name: \"$account\"" >&2; exit 2; }
		id -u "$account" > /dev/null 2>&1 || { echo "rehearsal: no account \"$account\"" >&2; exit 2; }
	done
	accounts=$(printf '%s\n' "$@" | LC_ALL=C sort -u)
	umask 022
	rule=$(mktemp)
	for account in $accounts; do
		printf '%s ALL=(root) NOPASSWD: %s pcalc, %s pcalc-tampered, %s pcalc-writable\n' "$account" "$helper" "$helper" "$helper"
	done > "$rule"
	visudo -cqf "$rule" || { rm -f "$rule"; echo "rehearsal: the sudo rule does not parse" >&2; exit 2; }
	tmp=$(mktemp)
	cat > "$tmp" <<'HELPER'
#!/bin/sh
# pma-rehearsal-residence <name>: the Custos rehearsal's binary, read from standard input, placed at
# /opt/pma-rehearsal/bin/<name>, owned by root; written by custos/tests/rehearsal.sh --install-residence.
set -eu
case "${1:-}" in
	pcalc|pcalc-tampered) mode=0755 ;;
	pcalc-writable) mode=0775 ;;
	*) echo "pma-rehearsal-residence: not a name: ${1:-}" >&2; exit 2 ;;
esac
umask 077
dir=/opt/pma-rehearsal/bin
mkdir -p "$dir"
chown 0:0 /opt/pma-rehearsal "$dir"
chmod 0755 /opt/pma-rehearsal "$dir"
tmp=$(mktemp "$dir/.in.XXXXXX")
cat > "$tmp"
chown 0:0 "$tmp"
chmod "$mode" "$tmp"
mv -f "$tmp" "$dir/$1"
HELPER
	install -o 0 -g 0 -m 0755 "$tmp" "$helper"
	# sudo skips a file of sudoers.d whose name holds a dot: the rule goes in under such a name and is
	# renamed whole, so a write cut short never leaves a broken rule that stops sudo for every user
	install -o 0 -g 0 -m 0440 "$rule" /etc/sudoers.d/.pma-rehearsal-residence.tmp
	mv -f /etc/sudoers.d/.pma-rehearsal-residence.tmp /etc/sudoers.d/pma-rehearsal-residence
	rm -f "$rule"
	"$helper" pcalc < /dev/null
	# the accounts installed, one name per line in name order, root's and readable by all, written last
	# and renamed whole: hostmove reads it to refuse a host whose residence misses a local gate account
	printf '%s\n' $accounts > "$tmp"
	install -o 0 -g 0 -m 0644 "$tmp" /opt/pma-rehearsal/.accounts.tmp
	mv -f /opt/pma-rehearsal/.accounts.tmp /opt/pma-rehearsal/accounts
	rm -f "$tmp"
	echo "rehearsal: residence installed: $helper, /etc/sudoers.d/pma-rehearsal-residence, /opt/pma-rehearsal/bin, /opt/pma-rehearsal/accounts for $(echo $accounts)"
	exit 0
fi

here=$(cd "$(dirname "$0")" && pwd)
custos=$(dirname "$here")
root=$(dirname "$custos")
pins="$here/rehearsal.json"
port=${CUSTOS_PORT:-8080}
tamper_only=${CUSTOS_TAMPER:-}

say() { printf '%s\n' "$*"; }
die() { printf 'rehearsal: cannot set up: %s\n' "$*" >&2; exit 2; }
pin() { php -r '$j = json_decode(file_get_contents($argv[1]), true); echo $j[$argv[2]][$argv[3]];' "$pins" "$1" "$2"; }

work=${CUSTOS_WORK:-$(mktemp -d "${TMPDIR:-/tmp}/custos-rehearsal.XXXXXX")}
mkdir -p "$work"
work=$(cd "$work" && pwd)
mw=${1:-$work/mediawiki}
case "$mw" in /*) ;; *) mw="$PWD/$mw" ;; esac

# The user PHP runs as: never root, whom the live residence check refuses (see the header).
phpbin=$(command -v php)
runas=()
if [ "$(id -u)" = 0 ]; then
	[ -x /usr/bin/setpriv ] || die "this runs as root and there is no setpriv to run PHP as another user"
	runas=(/usr/bin/setpriv --reuid=65534 --regid=65534 --clear-groups)
fi
php() { ${runas[@]+"${runas[@]}"} "$phpbin" "$@"; }

# Every ancestor of the scratch folder and of the MediaWiki folder must be searchable by the PHP
# user (as root, PHP runs as uid 65534): else install.php fails on a file it cannot reach.
if [ "${#runas[@]}" -gt 0 ]; then
	for start in "$work" "$mw"; do
		# the scratch folder is handed to that user below, and what lies in it with it
		case "$start" in "$work"/*) continue ;; esac
		d=$(dirname "$start")
		while [ ! -d "$d" ]; do d=$(dirname "$d"); done
		while :; do
			"${runas[@]}" /usr/bin/test -x "$d" || die "$d is not searchable by uid 65534; set CUSTOS_WORK under /tmp"
			[ "$d" = / ] && break
			d=$(dirname "$d")
		done
	done
fi

# What the end undoes: the web server, a swapped binary, the residence this run made.
server=
res=
res_own=
swapped=
cleanup() {
	[ -z "$server" ] || kill "$server" 2>/dev/null || true
	[ -z "$swapped" ] || place "$work/bin/pcalc" pcalc || true
	[ -z "$res_own" ] || rm -rf "$res_own"
}
trap cleanup EXIT

# 1. MediaWiki's sources
if [ -f "$mw/LocalSettings.php" ]; then
	say "mediawiki: installed; used as it is"
elif [ -f "$mw/index.php" ]; then
	say "mediawiki: sources present; installing"
else
	if [ -e "$mw" ] && [ -n "$(ls -A "$mw")" ]; then
		die "the folder given is neither empty nor MediaWiki's"
	fi
	if [ -n "${MW_TARBALL:-}" ]; then
		version=$(pin tarball version)
		want=${MW_SHA256:-$(pin tarball sha256)}
		echo "$want  $MW_TARBALL" | sha256sum -c --quiet - || die "the tarball's digest is not $want"
		rm -rf "$work/unpack" && mkdir -p "$work/unpack"
		tar xzf "$MW_TARBALL" -C "$work/unpack"
		rmdir "$mw" 2>/dev/null || true
		mv "$work/unpack/mediawiki-$version" "$mw"
		say "mediawiki: $version from the cached tarball, its digest checked"
	else
		tag=$(pin mediawiki tag)
		core=$(pin mediawiki commit)
		branch=$(pin vendor branch)
		vendor=$(pin vendor commit)
		git -c advice.detachedHead=false clone -q --depth 1 --branch "$tag" "$(pin mediawiki repository)" "$mw" \
			|| die "git clone of MediaWiki $tag failed"
		[ "$(git -C "$mw" rev-parse HEAD)" = "$core" ] || die "the tag $tag is not the pinned commit $core"
		git -c advice.detachedHead=false clone -q --depth 1 --branch "$branch" "$(pin vendor repository)" "$mw/vendor" \
			|| die "git clone of the vendor tree $branch failed"
		if [ "$(git -C "$mw/vendor" rev-parse HEAD)" != "$vendor" ]; then
			git -C "$mw/vendor" fetch -q --depth 1 origin "$vendor" || die "the pinned vendor commit $vendor cannot be fetched"
			git -C "$mw/vendor" -c advice.detachedHead=false checkout -q "$vendor"
		fi
		[ "$(git -C "$mw/vendor" rev-parse HEAD)" = "$vendor" ] || die "the vendor tree is not the pinned commit $vendor"
		say "mediawiki: $tag at ${core:0:12}, vendor $branch at ${vendor:0:12}, from Git, as pinned"
	fi
fi

# 2. The install, SQLite, its data outside the web root; the folders PHP writes are its user's
mkdir -p "$work/data"
if [ "${#runas[@]}" -gt 0 ]; then
	chown -R 65534:65534 "$work" "$mw"
fi
if [ ! -f "$mw/LocalSettings.php" ]; then
	(cd "$mw" && php maintenance/install.php --dbtype sqlite --dbpath "$work/data" --dbname rehearsal \
		--server "http://127.0.0.1:$port" --scriptpath "" --pass "$(openssl rand -hex 16)Aa1!" \
		"PMA Rehearsal" Rehearsaladmin) > "$work/install.log" 2>&1 \
		|| { tail -n 20 "$work/install.log" >&2; die "install.php failed (log: install.log in the scratch folder)"; }
	say "install: MediaWiki on SQLite, its data in the scratch folder"
fi

# 3. Custos loaded
link="$mw/extensions/Custos"
if [ -L "$link" ] || [ ! -e "$link" ]; then
	ln -sfn "$custos" "$link"
else
	die "extensions/Custos exists and is not this clone's link"
fi
if ! grep -qx '# Custos rehearsal' "$mw/LocalSettings.php"; then
	cat >> "$mw/LocalSettings.php" <<'PHP'

# Custos rehearsal
wfLoadExtension( 'Custos' );
$wgJobRunRate = 0;
require __DIR__ . '/LocalSettings.custos.php';
PHP
fi

# 4. The Calculator's binary, its digest, and a tampered copy: staged in the scratch folder's bin/,
# then placed at the residence under /opt, root's, which the live check accepts
mkdir -p "$work/bin"
if [ -x "$root/.lake/build/bin/pcalc" ]; then
	cp "$root/.lake/build/bin/pcalc" "$work/bin/pcalc"
	expect=$(sed -n 's/^def version : String := "\(.*\)"$/\1/p' "$root/Principia/Basic.lean")
	say "calculator binary: the built pcalc"
else
	cp "$here/fake_pcalc.sh" "$work/bin/pcalc"
	[ "$(sha256sum "$work/bin/pcalc" | cut -c1-64)" = "$(cat "$here/fake_pcalc.sha256")" ] \
		|| die "fake_pcalc.sh does not digest to fake_pcalc.sha256"
	expect=0.1.0
	say "calculator binary: the stand-in fake_pcalc.sh (no pcalc built in this clone)"
fi
chmod 755 "$work/bin" "$work/bin/pcalc"
digest=$(sha256sum "$work/bin/pcalc" | cut -c1-64)
# The D_IS the rehearsal's landings write: a rehearsal value, the digest of a fixed phrase.
dis=$(printf 'PMA rehearsal D_IS' | sha256sum | cut -c1-64)
cp "$work/bin/pcalc" "$work/bin/pcalc-tampered"
printf '\n' >> "$work/bin/pcalc-tampered"
chmod 755 "$work/bin/pcalc-tampered"
cp "$work/bin/pcalc" "$work/bin/pcalc-writable"
chmod 775 "$work/bin/pcalc-writable"

# place <staged file> <name>: the staged file at the residence as <name>, root's; pcalc-writable 0775
place() {
	if [ -n "$res_own" ]; then
		local mode=0755
		[ "$2" != pcalc-writable ] || mode=0775
		install -o 0 -g 0 -m "$mode" "$1" "$res/$2"
	else
		sudo -n "$helper" "$2" < "$1"
	fi
}
if [ "${#runas[@]}" -gt 0 ]; then
	mkdir -p /opt/pma-rehearsal
	chown 0:0 /opt/pma-rehearsal
	chmod 0755 /opt/pma-rehearsal
	res=$(mktemp -d /opt/pma-rehearsal/run.XXXXXX)
	res_own=$res
	chmod 0755 "$res"
else
	res=/opt/pma-rehearsal/bin
	if [ ! -x "$helper" ] || ! sudo -n -l "$helper" pcalc > /dev/null 2>&1; then
		die "the residence under /opt needs root's hand; the Operator runs once on this machine, as root: bash custos/tests/rehearsal.sh --install-residence <every local gate account> (on the service's host, its set-up's step hostprep runs it)"
	fi
	# the shared residence is one per machine: hold a lock on it for the whole run, so two gate
	# runs never place or swap each other's binaries (the descriptor closes when the run ends)
	exec 9< "$res" && flock -w 1800 9 || die "the residence $res is held by another run past 30 minutes"
fi
for name in pcalc pcalc-tampered pcalc-writable; do
	place "$work/bin/$name" "$name" || die "the binary $name could not be placed at the residence $res"
done
[ "$(sha256sum "$res/pcalc" | cut -c1-64)" = "$digest" ] || die "the binary at the residence $res/pcalc is not the staged one"
say "calculator residence: $res/pcalc, root's, under /opt"
# swap / unswap: the tampered bytes in at the residence's pcalc, and the true binary back
swap() { swapped=1; place "$work/bin/pcalc-tampered" pcalc; }
unswap() { place "$work/bin/pcalc" pcalc; swapped=; }

settings() {
	cat > "$mw/LocalSettings.custos.php" <<PHP
<?php
// Written by custos/tests/rehearsal.sh: the Calculator this rehearsal calls and what it expects.
\$wgCustosCalculator = '$1';
\$wgCustosBuild = [ 'version' => '$expect', 'digest' => '$digest' ];
\$wgCustosTps = '0.4.0';
\$wgCustosDIs = '$dis';
PHP
	# a second argument: the sweep age, for the sweep's pass alone
	[ -z "${2:-}" ] || printf '$wgCustosSweepAfter = %d;\n' "$2" >> "$mw/LocalSettings.custos.php"
}
wiring() { php "$mw/maintenance/run.php" "$here/wiring.php" 2>&1; }

# 4b. The tables custos_ticket, custos_seat, custos_certificate, custos_job_run, custos_nonce, custos_meter, custos_budget and custos_traffic, by the hook LoadExtensionSchemaUpdates (LocalSettings.custos.php written first)
settings "$res/pcalc"
(cd "$mw" && php maintenance/run.php update --quick) > "$work/update.log" 2>&1 \
	|| { tail -n 20 "$work/update.log" >&2; die "update.php failed (log: update.log in the scratch folder)"; }
say "update: the tables custos_ticket, custos_seat, custos_certificate, custos_job_run, custos_nonce, custos_meter, custos_budget and custos_traffic made by the schema hook"

# 4c. The schema's SQL current: for each table, generateSchemaSql reproduces sql/<type>/<table>.sql byte for byte
# from that table's own sql/<table>.json (the tables SchemaHooks::TABLES registers, each by its own name).
# Its libraries are MediaWiki's require-dev, absent from the vendor tree: each cloned at the commit
# rehearsal.json pins, into <scratch>/schema-tools (or the folder $CUSTOS_SCHEMA_TOOLS names), loaded by
# schema_tools.php. The JSON is copied into a real folder under extensions/, so the generated "Source:" line
# is the extension-relative sql/<table>.json wherever the clone lives.
custos_tables="custos_ticket custos_seat custos_certificate custos_job_run custos_nonce custos_meter custos_budget custos_traffic"
tools=${CUSTOS_SCHEMA_TOOLS:-$work/schema-tools}
for lib in dbal sql-formatter jsonlint deprecations event-manager; do
	if [ ! -d "$tools/$lib" ]; then
		git -c advice.detachedHead=false clone -q --depth 1 --branch "$(pin "$lib" tag)" "$(pin "$lib" repository)" "$tools/$lib" \
			|| die "git clone of the schema tool $lib failed"
	fi
	[ "$(git -C "$tools/$lib" rev-parse HEAD)" = "$(pin "$lib" commit)" ] || die "the schema tool $lib is not the pinned commit"
done
mkdir -p "$mw/extensions/CustosSchemaCheck/sql"
for table in $custos_tables; do
	cp "$custos/sql/$table.json" "$mw/extensions/CustosSchemaCheck/sql/$table.json"
	for type in sqlite mysql; do
		(cd "$mw" && CUSTOS_SCHEMA_TOOLS="$tools" php -d auto_prepend_file="$here/schema_tools.php" maintenance/run.php generateSchemaSql \
			--json "extensions/CustosSchemaCheck/sql/$table.json" --type "$type" --sql "$work/$table-$type.sql") > "$work/schema.log" 2>&1 \
			|| { tail -n 20 "$work/schema.log" >&2; die "generateSchemaSql failed for $table, $type"; }
		if ! cmp -s "$work/$table-$type.sql" "$custos/sql/$type/$table.sql"; then
			diff "$custos/sql/$type/$table.sql" "$work/$table-$type.sql" || true
			say "schema: sql/$type/$table.sql is not what generateSchemaSql writes from sql/$table.json"
			say "rehearsal: FAIL (schema)"
			exit 1
		fi
	done
done
say "schema: current"

# 4d. A wiki installed before the seat table: a second scratch wiki on the same sources (its own LocalSettings and
# SQLite data in the scratch folder; MW_CONFIG_FILE names that LocalSettings, so MediaWiki never reads the first
# wiki's), given custos_ticket alone, as the earlier schema hook made it (that table's own SQL, by maintenance/run.php
# sql), Custos loaded, one ticket written through the ticket store (Custos:Ticket); then update.php with this head's
# hook. The hook adds custos_seat, custos_certificate, custos_job_run, custos_nonce, custos_meter, custos_budget and
# custos_traffic and only adds: the eight tables present (the catalog read by sql), the ticket kept.
if [ -z "$tamper_only" ]; then
	old="$work/before-seat"
	mkdir -p "$old/data"
	[ "${#runas[@]}" -eq 0 ] || chown -R 65534:65534 "$old"
	oldmw() { (export MW_CONFIG_FILE="$old/LocalSettings.php"; cd "$mw" && php "$@") 2>&1; }
	oldmw maintenance/install.php --dbtype sqlite --dbpath "$old/data" --dbname beforeseat --confpath "$old" \
		--server "http://127.0.0.1:$port" --scriptpath "" --pass "$(openssl rand -hex 16)Aa1!" \
		"PMA Rehearsal Before Seat" Rehearsaladmin > "$work/install-before-seat.log" \
		|| { tail -n 20 "$work/install-before-seat.log" >&2; die "install.php of the second wiki failed"; }
	tables_of() {
		oldmw maintenance/run.php sql --query "SELECT name FROM sqlite_master WHERE type = 'table' AND name LIKE '%custos%' ORDER BY name" \
			| grep -o 'custos_[a-z_]*' | sort -u | tr '\n' ' '
	}
	oldmw maintenance/run.php sql "$custos/sql/sqlite/custos_ticket.sql" > "$work/before-seat.log" \
		|| { cat "$work/before-seat.log" >&2; die "custos_ticket could not be made on the second wiki"; }
	before=$(tables_of)
	[ "$before" = "custos_ticket " ] || die "the second wiki is not custos_ticket alone before its update: $before"
	cat >> "$old/LocalSettings.php" <<'PHP'

# Custos rehearsal: the wiki installed before the seat table
wfLoadExtension( 'Custos' );
$wgJobRunRate = 0;
PHP
	oldmw maintenance/run.php Custos:Ticket --new PETITION --account 'Before seat' --prefix OLD --request '{"prefix":"OLD"}' >> "$work/before-seat.log" \
		|| { cat "$work/before-seat.log" >&2; die "the ticket could not be written on the second wiki"; }
	oldmw maintenance/run.php update --quick > "$work/update-before-seat.log" \
		|| { tail -n 20 "$work/update-before-seat.log" >&2; die "update.php of the second wiki failed"; }
	after=$(tables_of)
	kept=$(oldmw maintenance/run.php Custos:Ticket --count QUEUED | tail -n 1)
	if [ "$after" != "custos_budget custos_certificate custos_job_run custos_meter custos_nonce custos_seat custos_ticket custos_traffic " ] || [ "$kept" != 1 ]; then
		tail -n 20 "$work/update-before-seat.log"
		say "schema: the update of the wiki that had custos_ticket alone left: $after (tickets QUEUED: $kept)"
		say "rehearsal: FAIL (schema)"
		exit 1
	fi
	say "schema: custos_seat, custos_certificate, custos_job_run, custos_nonce, custos_meter, custos_budget and custos_traffic added by update to a wiki that had custos_ticket alone"
fi

# 5. The wiring with the true binary, then the web
if [ -z "$tamper_only" ]; then
	settings "$res/pcalc"
	code=0
	out=$(wiring) || code=$?
	printf '%s\n' "$out"
	if [ "$code" -ne 0 ] || ! grep -qE '^wiring: ALL PASS [0-9]+/[0-9]+$' <<<"$out" \
		|| ! grep -qx "calculator: version $expect, digest match" <<<"$out"; then
		say "rehearsal: FAIL (wiring)"
		exit 1
	fi

	# The agent account: its password drawn from /dev/urandom, kept in the scratch folder, mode 600, never printed.
	umask 077
	if [ ! -s "$work/agent.pass" ]; then
		head -c 24 /dev/urandom | od -An -tx1 | tr -d ' \n' > "$work/agent.pass"
		printf 'Aa1!' >> "$work/agent.pass"
	fi
	chmod 600 "$work/agent.pass"
	umask 022
	(cd "$mw" && php maintenance/run.php createAndPromote --force --custom-groups=pma-agent Rehearsalagent "$(cat "$work/agent.pass")") \
		> "$work/agent.log" 2>&1 || { say "api: the agent account could not be made (log: agent.log in the scratch folder)"; say "rehearsal: FAIL (api)"; exit 1; }

	# The certificates: the agent account and the second account (the LOCK HELD case's) each bound to the
	# Sponsor Rehearsalsponsor by Custos:Certify, the table's only writer; admission refuses an agent with none.
	# The digests are the rehearsal's own stand-ins (not secrets).
	rdis=$(printf 'rehearsal D(IS)' | sha256sum | cut -c1-64)
	rprompt=$(printf 'rehearsal D(PROMPT)' | sha256sum | cut -c1-64)
	for who in Rehearsalagent Rehearsalsecond; do
		cert=$( (cd "$mw" && php maintenance/run.php Custos:Certify --agent "$who" --sponsor Rehearsalsponsor --d-is "$rdis" \
			--d-prompt "$rprompt" --family rehearsal --model rehearsal-model) 2>&1) || { printf '%s\n' "$cert"; say "rehearsal: FAIL (certify)"; exit 1; }
		[ "$(tail -n 1 <<<"$cert")" = "certify: $who sponsor Rehearsalsponsor" ] || { printf '%s\n' "$cert"; say "rehearsal: FAIL (certify)"; exit 1; }
		say "$(tail -n 1 <<<"$cert")"
	done

	# opcache revalidates every request, so a rewritten LocalSettings.custos.php (the sweep's pass) is read at once
	${runas[@]+"${runas[@]}"} "$phpbin" -d opcache.revalidate_freq=0 -S "127.0.0.1:$port" -t "$mw" > "$work/web.log" 2>&1 &
	server=$!
	for _ in $(seq 1 40); do
		curl -s -o /dev/null "http://127.0.0.1:$port/api.php" && break
		sleep 0.25
	done
	api="http://127.0.0.1:$port/api.php"
	jar="$work/cookies"
	: > "$jar"
	chmod 600 "$jar"
	member() { php -r '$j = json_decode($argv[1], true); $v = $j; foreach (array_slice($argv, 2) as $k) { $v = is_array($v) ? ($v[$k] ?? null) : null; } echo is_scalar($v) ? (string)$v : "";' "$@"; }
	fail_api() { say "api: $1"; say "rehearsal: FAIL (api)"; kill "$server" 2>/dev/null || true; exit 1; }
	# post <op> [<name=value> ...]: the op as a POST with the CSRF token; sets $status and $body
	post() {
		local op=$1; shift
		local args=(-s -b "$jar" -c "$jar" -o "$work/answer.json" -w '%{http_code}' --data-urlencode "action=pma" --data-urlencode "format=json"
			--data-urlencode "formatversion=2" --data-urlencode "op=$op" --data-urlencode "token=$csrf")
		local kv
		for kv in "$@"; do args+=(--data-urlencode "$kv"); done
		status=$(curl "${args[@]}" "$api") || status=000
		body=$(cat "$work/answer.json")
	}

	logintoken=$(member "$(curl -s -b "$jar" -c "$jar" "$api?action=query&meta=tokens&type=login&format=json&formatversion=2")" query tokens logintoken)
	login=$(curl -s -b "$jar" -c "$jar" --data-urlencode "action=clientlogin" --data-urlencode "format=json" --data-urlencode "formatversion=2" \
		--data-urlencode "username=Rehearsalagent" --data-urlencode "password@$work/agent.pass" --data-urlencode "logintoken=$logintoken" \
		--data-urlencode "loginreturnurl=http://127.0.0.1:$port/" "$api")
	[ "$(member "$login" clientlogin status)" = "PASS" ] || fail_api "the agent account could not log in: $(member "$login" clientlogin status)"
	csrf=$(member "$(curl -s -b "$jar" -c "$jar" "$api?action=query&meta=tokens&format=json&formatversion=2")" query tokens csrftoken)
	[ -n "$csrf" ] && [ "$csrf" != '+\' ] || fail_api "no CSRF token for the agent account"

	post PETITION prefix=Rehearsal block=b1
	ticket=$(member "$body" pma ticket)
	[ "$status" = 202 ] && [ "$(member "$body" pma state)" = QUEUED ] && [ -n "$ticket" ] \
		&& [ "$(member "$body" pma poll_after)" = 30 ] || fail_api "PETITION answered $status: $body"
	say "api: PETITION $status"
	poll=$(curl -s -b "$jar" -c "$jar" "$api?action=pma&op=POLL&ticket=$ticket&format=json&formatversion=2")
	[ "$(member "$poll" pma state)" = QUEUED ] && [ "$(member "$poll" pma ticket_op)" = PETITION ] || fail_api "POLL answered: $poll"
	say "api: POLL $(member "$poll" pma state)"
	post PUSH prefix=Rehearsal block=b1 'records=[{"kind":"NOTE","text":"not parsed by Custos"}]'
	[ "$status" = 202 ] && [ "$(member "$body" pma state)" = QUEUED ] || fail_api "PUSH answered $status: $body"
	say "api: PUSH $status"
	post RELEASE prefix=Rehearsal block=b1
	[ "$status" = 202 ] && [ "$(member "$body" pma state)" = QUEUED ] || fail_api "RELEASE answered $status: $body"
	say "api: RELEASE $status"
	# The governor's ops: STATUS, a read answered 200 with the build and the level; HEARTBEAT, a write op's 202.
	stcode=$(curl -s -b "$jar" -c "$jar" -o "$work/status.json" -w '%{http_code}' "$api?action=pma&op=STATUS&format=json&formatversion=2") || stcode=000
	st=$(cat "$work/status.json")
	[ "$stcode" = 200 ] && [ -n "$(member "$st" pma governor level)" ] && [ "$(member "$st" pma stage)" = NORMAL ] || fail_api "STATUS answered $stcode: $st"
	say "api: STATUS $stcode"
	post HEARTBEAT prefix=Rehearsal block=b1
	[ "$status" = 202 ] && [ "$(member "$body" pma state)" = QUEUED ] || fail_api "HEARTBEAT answered $status: $body"
	say "api: HEARTBEAT $status"
	post STRUCTURE_TEST prefix=Rehearsal
	[ "$status" = 202 ] && [ "$(member "$body" pma state)" = QUEUED ] || fail_api "STRUCTURE_TEST answered $status: $body"
	say "api: STRUCTURE_TEST $status"
	post STRUCTURE_TEST prefix=Rehearsal block=b1
	[ "$(member "$body" error code)" = custos-unknown-param ] || fail_api "a STRUCTURE_TEST naming a block answered $status: $body"

	# The refusals over HTTP: an account parameter, a prefix in no form, another account's ticket, no token
	post PETITION prefix=Rehearsal account=Rehearsaladmin
	[ "$(member "$body" error code)" = custos-account ] || fail_api "a PETITION naming another account answered $status: $body"
	post PETITION prefix=Re-hearsal
	[ "$(member "$body" error code)" = custos-prefix ] || fail_api "a PETITION of a prefix in no form answered $status: $body"
	anon=$(curl -s "$api?action=pma&op=POLL&ticket=$ticket&format=json&formatversion=2")
	[ "$(member "$anon" error code)" = custos-ticket-not-yours ] || fail_api "an anonymous POLL of the agent's ticket answered: $anon"
	anonpost=$(curl -s --data-urlencode "action=pma" --data-urlencode "format=json" --data-urlencode "formatversion=2" \
		--data-urlencode "op=PETITION" --data-urlencode "prefix=Rehearsal" --data-urlencode 'token=+\' "$api")
	[ "$(member "$anonpost" error code)" = custos-not-agent ] || fail_api "an anonymous PETITION answered: $anonpost"
	notoken=$(curl -s -b "$jar" --data-urlencode "action=pma" --data-urlencode "format=json" --data-urlencode "op=PETITION" \
		--data-urlencode "prefix=Rehearsal" "$api")
	[ -n "$(member "$notoken" error code)" ] && [ -z "$(member "$notoken" pma ticket)" ] || fail_api "a PETITION without its token answered: $notoken"
	say "api: refused: an account parameter, a prefix in no form, another account's ticket, an anonymous PETITION, a PETITION without its token"

	# The seed: a UWC's seven pages in one landing by the system user Custos (the Operator's maintenance script), then
	# the fence: a direct edit of its register by the agent account is refused by the permission hook.
	seedprefix="Spring$(date +%s)"
	seedout=$( (cd "$mw" && php maintenance/run.php Custos:SeedUwc --prefix "$seedprefix" \
		--draft "$root/docs/v1/tpx/TPX/examples/spring_draft.json") 2>&1) || { printf '%s\n' "$seedout"; fail_api "the seed failed"; }
	n=0
	for page in Draft "Research Assembly/Starting Set" "Research Assembly/Correspondence Table" "Research Assembly/Criteria Set" \
		"Register/Volume 1" Lock Index; do
		got=$(curl -s -b "$jar" -G --data-urlencode "action=query" --data-urlencode "format=json" --data-urlencode "formatversion=2" \
			--data-urlencode "prop=revisions" --data-urlencode "rvprop=user" --data-urlencode "titles=Principia Machina/UWC/$seedprefix/$page" "$api")
		[ "$(member "$got" query pages 0 revisions 0 user)" = Custos ] || { printf '%s\n' "$seedout"; fail_api "the seeded page $page is not Custos's: $got"; }
		n=$((n + 1))
	done
	grep -qx "seed: $n pages" <<<"$seedout" || { printf '%s\n' "$seedout"; fail_api "the seed did not write $n pages"; }
	[ "$(grep '^seed: wrote ' <<<"$seedout" | tail -n 1)" = "seed: wrote Principia Machina/UWC/$seedprefix/Index" ] \
		|| { printf '%s\n' "$seedout"; fail_api "the seed did not write the INDEX AND BADGE page last"; }
	say "seed: $n pages"
	# The STRUCTURE TEST LINE until the first run, on the INDEX AND BADGE page (TPS 5.3.47).
	# block_of <title> <name>: the payload of the page's block pma-<name>, read with getText.
	block_of() { (cd "$mw" && php maintenance/run.php getText "$1") 2>/dev/null \
		| php -r '$t = stream_get_contents(STDIN); echo preg_match("#<pre class=\"pma-" . $argv[1] . "\">\n(.*?)\n</pre>#s", $t, $m) ? $m[1] : "";' "$2"; }
	ixtitle="Principia Machina/UWC/$seedprefix/Index"
	[ "$(block_of "$ixtitle" structure)" = "STRUCTURE TEST none" ] || fail_api "the seeded INDEX AND BADGE page does not read STRUCTURE TEST none: $(block_of "$ixtitle" structure)"
	say "seed: STRUCTURE TEST none"
	regtitle="Principia Machina/UWC/$seedprefix/Register/Volume 1"
	edit=$(curl -s -b "$jar" -c "$jar" --data-urlencode "action=edit" --data-urlencode "format=json" --data-urlencode "formatversion=2" \
		--data-urlencode "title=$regtitle" --data-urlencode "text=edited by hand" --data-urlencode "token=$csrf" "$api")
	[ "$(member "$edit" error code)" = custos-governed-page ] || fail_api "a direct edit of the register by the agent answered: $edit"
	after=$(curl -s -b "$jar" -G --data-urlencode "action=query" --data-urlencode "format=json" --data-urlencode "formatversion=2" \
		--data-urlencode "prop=revisions" --data-urlencode "rvprop=user" --data-urlencode "rvlimit=max" --data-urlencode "titles=$regtitle" "$api")
	[ "$(member "$after" query pages 0 revisions 1 user)" = "" ] || fail_api "the register carries a second revision after the refused edit: $after"
	say "hook: edit refused custos-governed-page"

	# The restricted namespace: Restricted: registered under its number with no talk namespace, and a read of a page in it by the agent
	# account and by an anonymous request refused by the permission hook with its own message (the table: neither reads it). The API's
	# query result never names a restricted page (RestrictedRoutes), so the refusal is read from index.php, which answers 403: MediaWiki
	# renders the refusal as an error page answered 200, and Custos answers it 403 (RestrictedRoutes, BeforeInitialize).
	ns=$(curl -s -G --data-urlencode "action=query" --data-urlencode "format=json" --data-urlencode "formatversion=2" \
		--data-urlencode "meta=siteinfo" --data-urlencode "siprop=namespaces" "$api")
	[ "$(member "$ns" query namespaces 7240 name)" = Restricted ] && [ -z "$(member "$ns" query namespaces 7241 id)" ] \
		|| fail_api "the namespace 7240 Restricted is not registered, or a talk namespace 7241 is (none is): $ns"
	[ "$(member "$ns" query namespaces 7240 nonincludable)" = 1 ] || [ "$(member "$ns" query namespaces 7240 nonincludable)" = true ] \
		|| fail_api "the namespace 7240 is includable: $ns"
	index="http://127.0.0.1:$port/index.php"
	restrictedmsg="is restricted: only the Declarer and the Operator read it"
	for who in agent anonymous; do
		if [ "$who" = agent ]; then cj=(-b "$jar"); else cj=(); fi
		code=$(curl -s "${cj[@]}" -o "$work/rd.html" -w '%{http_code}' -G --data-urlencode "title=Restricted:Falcon/Stratum" "$index") || code=000
		[ "$code" = 403 ] && grep -q "$restrictedmsg" "$work/rd.html" \
			|| fail_api "a read of Restricted:Falcon/Stratum by the $who request answered $code without the hook's refusal"
	done
	say "hook: Restricted read refused"

	# The restricted routes (RestrictedRoutes): a restricted page the system user Custos writes (edit.php as Custos, the
	# Operator's maintenance path), carrying a word found nowhere else, a link and a category; an ordinary page transcluding
	# it and reading its revision by the parser's functions; then each route read by the agent account, one line each; then
	# an account in the Declarer's group reads the page by its title, and transclusion stays refused for it too.
	rmark="zqxrestricted$(date +%s)"
	rtitle="Restricted:Falcon/Stratum"
	printf '%s [[Main Page]] [[Category:Rehearsal restricted]]\n' "$rmark" \
		| (cd "$mw" && php maintenance/run.php edit --user Custos --summary "$rmark summary" "$rtitle") > "$work/restricted.log" 2>&1 \
		|| { cat "$work/restricted.log"; fail_api "the restricted page could not be written as Custos"; }
	# The transcluding page is public, and its own text (which the contributions feed carries as a diff) names the
	# restricted title only through the parser ({{ucfirst:}}), so a list naming "Falcon/Stratum" names the restricted page.
	rsrc="Restricted:Falcon/{{ucfirst:stratum}}"
	printf '{{%s}} {{:%s}} {{msgnw:%s}} size {{PAGESIZE:%s|R}} by [{{REVISIONUSER:%s}}] at [{{REVISIONTIMESTAMP:%s}}]\n' \
		"$rsrc" "$rsrc" "$rsrc" "$rsrc" "$rsrc" "$rsrc" \
		| (cd "$mw" && php maintenance/run.php edit --user Custos --summary "transcluding" "Rehearsal transclusion") >> "$work/restricted.log" 2>&1 \
		|| { cat "$work/restricted.log"; fail_api "the transcluding page could not be written"; }
	# login_as <account> <password file> <cookie jar>
	login_as() {
		local lt; lt=$(member "$(curl -s -b "$3" -c "$3" "$api?action=query&meta=tokens&type=login&format=json&formatversion=2")" query tokens logintoken)
		local lg; lg=$(curl -s -b "$3" -c "$3" --data-urlencode "action=clientlogin" --data-urlencode "format=json" --data-urlencode "formatversion=2" \
			--data-urlencode "username=$1" --data-urlencode "password@$2" --data-urlencode "logintoken=$lt" \
			--data-urlencode "loginreturnurl=http://127.0.0.1:$port/" "$api")
		[ "$(member "$lg" clientlogin status)" = "PASS" ] || fail_api "the account $1 could not log in: $(member "$lg" clientlogin status)"
	}
	# The Declarer's group's account: its password drawn as the agent's, kept in the scratch folder, mode 600, never printed.
	umask 077
	[ -s "$work/declarer.pass" ] || { head -c 24 /dev/urandom | od -An -tx1 | tr -d ' \n' > "$work/declarer.pass"; printf 'Aa1!' >> "$work/declarer.pass"; }
	chmod 600 "$work/declarer.pass"
	umask 022
	djar="$work/cookies.declarer"
	: > "$djar"
	chmod 600 "$djar"
	(cd "$mw" && php maintenance/run.php createAndPromote --force --custom-groups=pma-declarer Rehearsaldeclarer "$(cat "$work/declarer.pass")") \
		> "$work/declarer.log" 2>&1 || fail_api "the Declarer's group's account could not be made (log: declarer.log in the scratch folder)"
	login_as Rehearsaldeclarer "$work/declarer.pass" "$djar"
	# The restricted page's revision, read by the Declarer's group's account by its own title (index.php, admitted by the hook).
	code=$(curl -s -b "$djar" -o "$work/rraw.txt" -w '%{http_code}' -G --data-urlencode "title=$rtitle" --data-urlencode "action=raw" "$index") || code=000
	[ "$code" = 200 ] && grep -q "$rmark" "$work/rraw.txt" || fail_api "the Declarer's group's read of $rtitle by its title answered $code"
	code=$(curl -s -b "$djar" -o "$work/rhist.html" -w '%{http_code}' -G --data-urlencode "title=$rtitle" --data-urlencode "action=info" "$index") || code=000
	rrev=$(php -r 'echo preg_match("/oldid=([0-9]+)/", file_get_contents($argv[1]), $m) ? $m[1] : "";' "$work/rhist.html")
	rpid=$(php -r 'echo preg_match("/\"wgArticleId\":([0-9]+)/", file_get_contents($argv[1]), $m) ? $m[1] : "";' "$work/rhist.html")
	[ "$code" = 200 ] && [ -n "$rrev" ] && [ -n "$rpid" ] || fail_api "the restricted page's revision and id could not be read by the Declarer's group ($code)"
	# absent <what> <text> <needle> ...: none of the needles in the text
	absent() {
		local what=$1 text=$2; shift 2
		local n
		for n in "$@"; do
			if grep -qF -- "$n" <<<"$text"; then fail_api "$what carries \"$n\""; fi
		done
	}
	get_as() { local j=$1; shift; curl -s -b "$j" -G "$@"; }
	apiq() { get_as "$jar" --data-urlencode "format=json" --data-urlencode "formatversion=2" "$@" "$api"; }
	page() { get_as "$jar" "$@" "$index"; }
	secret=("$rmark" "Falcon/Stratum")

	# transclusion: {{...}}, {{:...}}, {{msgnw:...}} and the parser's reads of its revision, in a saved page and in action=parse and
	# action=expandtemplates of a text
	p1=$(apiq --data-urlencode "action=parse" --data-urlencode "page=Rehearsal transclusion" --data-urlencode "prop=text")
	[ "$(member "$p1" parse title)" = "Rehearsal transclusion" ] || fail_api "the transcluding page was not parsed: $p1"
	absent "the transcluding page as parsed" "$p1" "$rmark"
	grep -q 'size 0 by \[\] at \[\]' <<<"$p1" || fail_api "the parser read the restricted page's revision: $p1"
	p2=$(apiq --data-urlencode "action=parse" --data-urlencode "title=Sandbox" --data-urlencode "contentmodel=wikitext" \
		--data-urlencode "text={{$rtitle}}{{:$rtitle}}{{PAGESIZE:$rtitle|R}}" --data-urlencode "prop=text")
	p3=$(apiq --data-urlencode "action=expandtemplates" --data-urlencode "title=Sandbox" --data-urlencode "prop=wikitext" \
		--data-urlencode "text={{$rtitle}}{{:$rtitle}}{{msgnw:$rtitle}}")
	absent "action=parse of a text transcluding it" "$p2" "$rmark"
	absent "action=expandtemplates" "$p3" "$rmark"
	say "restricted: transclusion refused"

	# search: list=search by its word, with the prefixes "all:" and "Restricted:", list=prefixsearch, action=opensearch, Special:Search
	for q in "$rmark" "all:$rmark" "Restricted:$rmark" "Restricted:Falcon"; do
		for what in text title; do
			s=$(apiq --data-urlencode "action=query" --data-urlencode "list=search" --data-urlencode "srsearch=$q" --data-urlencode "srwhat=$what" \
				--data-urlencode "srprop=snippet|titlesnippet")
			absent "list=search \"$q\" ($what)" "$s" "Falcon/Stratum" "$rmark summary" "searchmatch\">$rmark"
		done
		h=$(page --data-urlencode "title=Special:Search" --data-urlencode "search=$q" --data-urlencode "fulltext=1" --data-urlencode "profile=all")
		absent "Special:Search \"$q\"" "$h" "Falcon/Stratum"
	done
	s=$(apiq --data-urlencode "action=query" --data-urlencode "list=prefixsearch" --data-urlencode "pssearch=Restricted:Fal")
	absent "list=prefixsearch" "$s" "Falcon/Stratum"
	s=$(apiq --data-urlencode "action=opensearch" --data-urlencode "search=Restricted:Fal")
	absent "action=opensearch" "$s" "Falcon/Stratum"
	s=$(apiq --data-urlencode "action=query" --data-urlencode "list=search" --data-urlencode "srsearch=$rmark" --data-urlencode "srnamespace=7240")
	[ "$(member "$s" error code)" = custos-restricted-route ] || fail_api "list=search in the namespace 7240 answered: $s"
	say "restricted: search shows nothing"

	# export: Special:Export by its title and by a POST of the title, the API's export, exportall where the wiki allows it
	e1=$(page --data-urlencode "title=Special:Export/$rtitle")
	e2=$(curl -s -b "$jar" --data-urlencode "title=Special:Export" --data-urlencode "pages=$rtitle" --data-urlencode "curonly=1" "$index")
	e3=$(apiq --data-urlencode "action=query" --data-urlencode "export=1" --data-urlencode "titles=$rtitle")
	e4=$(curl -s -b "$jar" --data-urlencode "title=Special:Export" --data-urlencode "exportall=1" --data-urlencode "curonly=1" "$index")
	for e in "$e1" "$e2" "$e3" "$e4"; do absent "an export" "$e" "${secret[@]}"; done
	say "restricted: export refused"

	# the view, action=raw and action=render by the agent account and an anonymous request: each answered 403 (Custos's status
	# for the hook's refusal; MediaWiki's own error page answers 200), as the absent page was above
	for a in view raw render; do
		for cjf in "$jar" /dev/null; do
			code=$(curl -s -b "$cjf" -o "$work/rr.txt" -w '%{http_code}' -G --data-urlencode "title=$rtitle" --data-urlencode "action=$a" "$index") || code=000
			[ "$code" = 403 ] || fail_api "action=$a of $rtitle answered $code, not 403"
			absent "action=$a" "$(cat "$work/rr.txt")" "$rmark"
		done
	done
	say "restricted: raw refused"

	# the API's revisions: content, its metadata alone, by revision id, list=allrevisions; action=compare
	r1=$(apiq --data-urlencode "action=query" --data-urlencode "prop=revisions" --data-urlencode "rvprop=content|comment|user|size|sha1" \
		--data-urlencode "rvslots=main" --data-urlencode "titles=$rtitle")
	r2=$(apiq --data-urlencode "action=query" --data-urlencode "prop=revisions" --data-urlencode "rvprop=comment|user|timestamp|size" --data-urlencode "titles=$rtitle")
	r3=$(apiq --data-urlencode "action=query" --data-urlencode "prop=revisions" --data-urlencode "rvprop=comment|user|content" --data-urlencode "rvslots=main" \
		--data-urlencode "revids=$rrev")
	r4=$(apiq --data-urlencode "action=query" --data-urlencode "list=allrevisions" --data-urlencode "arvprop=comment|user|ids" --data-urlencode "arvlimit=max")
	r5=$(apiq --data-urlencode "action=compare" --data-urlencode "fromrev=$rrev" --data-urlencode "totitle=Main Page" --data-urlencode "prop=diff|comment")
	r6=$(apiq --data-urlencode "action=query" --data-urlencode "prop=revisions" --data-urlencode "rvprop=comment" --data-urlencode "generator=allpages" \
		--data-urlencode "gapnamespace=7240")
	# by its title (the asker named it): neither its text nor its summary; by an id: refused, the title never named; the lists: neither
	for r in "$r1" "$r2"; do absent "the API's revisions by the title" "$r" "$rmark"; done
	absent "list=allrevisions" "$r4" "${secret[@]}"
	for r in "$r3" "$r5" "$r6"; do
		[ "$(member "$r" error code)" = custos-restricted-route ] || fail_api "a request naming the restricted page by an id or its namespace answered: $r"
		absent "a request naming the restricted page by an id" "$r" "${secret[@]}"
	done
	o1=$(apiq --data-urlencode "action=parse" --data-urlencode "oldid=$rrev")
	[ "$(member "$o1" error code)" = custos-restricted-route ] || fail_api "action=parse of the restricted page's revision answered: $o1"
	say "restricted: API revisions refused"

	# history and diffs: action=history, action=info, oldid=, diff=, Special:ComparePages, by the agent account and an anonymous request
	for cjf in "$jar" /dev/null; do
		for q in "title=$rtitle&action=history" "title=$rtitle&action=info" "oldid=$rrev" "diff=$rrev" "diff=$rrev&oldid=1" \
			"title=Special:ComparePages&page1=Main_Page&page2=$rtitle"; do
			hb=$(curl -s -b "$cjf" "$index?$q")
			absent "index.php?$q" "$hb" "$rmark"
		done
		# by an id alone the refusal names no title
		for q in "oldid=$rrev" "diff=$rrev" "curid=$rpid"; do
			hb=$(curl -s -b "$cjf" "$index?$q")
			absent "index.php?$q" "$hb" "Falcon/Stratum"
		done
	done
	say "restricted: history refused"

	# the change lists and the title lists: RecentChanges, NewPages, Contributions of Custos, the logs, Watchlist's feed source,
	# the API's lists and their namespace parameters, AllPages and PrefixIndex, the link tables (WhatLinksHere, the category)
	l=()
	l+=("$(page --data-urlencode "title=Special:RecentChanges" --data-urlencode "days=90" --data-urlencode "limit=500" --data-urlencode "enhanced=0")")
	l+=("$(page --data-urlencode "title=Special:RecentChanges" --data-urlencode "days=90" --data-urlencode "limit=500" --data-urlencode "enhanced=1")")
	l+=("$(page --data-urlencode "title=Special:NewPages" --data-urlencode "limit=500")")
	l+=("$(page --data-urlencode "title=Special:NewPages" --data-urlencode "namespace=7240")")
	l+=("$(page --data-urlencode "title=Special:Contributions/Custos" --data-urlencode "limit=500")")
	l+=("$(page --data-urlencode "title=Special:Log" --data-urlencode "limit=500")")
	l+=("$(page --data-urlencode "title=Special:Log/create" --data-urlencode "user=Custos")")
	l+=("$(page --data-urlencode "title=Special:AllPages" --data-urlencode "namespace=7240")")
	l+=("$(page --data-urlencode "title=Special:AllPages" --data-urlencode "from=Restricted:F")")
	l+=("$(page --data-urlencode "title=Special:PrefixIndex/Restricted:F")")
	l+=("$(page --data-urlencode "title=Special:WhatLinksHere/Main_Page" --data-urlencode "limit=500")")
	l+=("$(page --data-urlencode "title=Category:Rehearsal restricted")")
	l+=("$(apiq --data-urlencode "action=query" --data-urlencode "list=recentchanges" --data-urlencode "rcprop=title|comment|ids" --data-urlencode "rclimit=max")")
	l+=("$(apiq --data-urlencode "action=query" --data-urlencode "list=recentchanges" --data-urlencode "rcnamespace=*" --data-urlencode "rcprop=title|comment")")
	l+=("$(apiq --data-urlencode "action=query" --data-urlencode "list=usercontribs" --data-urlencode "ucuser=Custos" --data-urlencode "ucprop=title|comment")")
	l+=("$(apiq --data-urlencode "action=query" --data-urlencode "list=logevents" --data-urlencode "leprop=title|comment|details")")
	l+=("$(apiq --data-urlencode "action=query" --data-urlencode "list=backlinks" --data-urlencode "bltitle=Main Page")")
	l+=("$(apiq --data-urlencode "action=query" --data-urlencode "list=categorymembers" --data-urlencode "cmtitle=Category:Rehearsal restricted")")
	l+=("$(apiq --data-urlencode "action=feedrecentchanges" --data-urlencode "days=90")")
	l+=("$(apiq --data-urlencode "action=feedcontributions" --data-urlencode "user=Custos")")
	for x in "${l[@]}"; do absent "a list" "$x" "Falcon/Stratum" "$rmark summary"; done
	for p in apnamespace rcnamespace ucnamespace lenamespace; do
		mod=list; case $p in ap*) v=allpages ;; rc*) v=recentchanges ;; uc*) v=usercontribs; extra=(--data-urlencode "ucuser=Custos") ;; le*) v=logevents ;; esac
		x=$(apiq --data-urlencode "action=query" --data-urlencode "$mod=$v" --data-urlencode "$p=0|7240" ${extra[@]+"${extra[@]}"})
		extra=()
		[ "$(member "$x" error code)" = custos-restricted-route ] || fail_api "$mod=$v with $p=0|7240 answered: $x"
	done
	say "restricted: recent changes show nothing"

	# the random pages by a subpage naming the namespace: no redirect to a restricted title (core takes any namespace there)
	for sp in Random RandomRedirect RandomRootPage; do
		loc=$(curl -s -b "$jar" -o "$work/rnd.html" -w '%{redirect_url}' "$index?title=Special:$sp/Restricted") || loc=""
		absent "Special:$sp/Restricted's redirect" "$loc" "Restricted:" "Restricted%3A"
		absent "Special:$sp/Restricted" "$(cat "$work/rnd.html")" "Falcon/Stratum"
	done
	say "restricted: random refused"

	# the REST API's search by the prefixes "Restricted:" and "all:", and its sitemap with the namespace included
	rest="http://127.0.0.1:$port/rest.php"
	for q in "Restricted:Fal" "Restricted:$rmark" "all:$rmark" "all:Falcon"; do
		for route in v1/search/title v1/search/page; do
			x=$(curl -s -b "$jar" -G --data-urlencode "q=$q" "$rest/$route")
			absent "rest.php/$route?q=$q" "$x" "Falcon/Stratum" "Falcon/Shortcut" "$rmark summary"
		done
	done
	x=$(curl -s -b "$jar" -G --data-urlencode "include_namespace=7240" "$rest/site/v1/sitemap/0/page/0")
	absent "the REST sitemap" "$x" "Falcon/Stratum"
	say "restricted: REST search refused"

	# a move into the namespace (moveBatch, the Operator's command line): its row carries the source's namespace; the change
	# lists, their feeds and the API's list=recentchanges never name the target
	printf 'to be moved\n' | (cd "$mw" && php maintenance/run.php edit --user Custos --summary "move source" "Rehearsal move source") \
		>> "$work/restricted.log" 2>&1 || { cat "$work/restricted.log"; fail_api "the move source could not be written"; }
	printf 'Rehearsal move source|Restricted:Falcon/Moved\n' > "$work/moves.txt"
	(cd "$mw" && php maintenance/run.php moveBatch --r "rehearsal move" --noredirects "$work/moves.txt") >> "$work/restricted.log" 2>&1 \
		|| { cat "$work/restricted.log"; fail_api "the move into the namespace could not be made"; }
	m=()
	m+=("$(page --data-urlencode "title=Special:RecentChanges" --data-urlencode "days=90" --data-urlencode "limit=500" --data-urlencode "enhanced=0")")
	m+=("$(page --data-urlencode "title=Special:RecentChanges" --data-urlencode "days=90" --data-urlencode "limit=500" --data-urlencode "enhanced=1")")
	m+=("$(page --data-urlencode "title=Special:Log/move")")
	m+=("$(apiq --data-urlencode "action=query" --data-urlencode "list=recentchanges" --data-urlencode "rcprop=title|comment|loginfo" --data-urlencode "rclimit=max")")
	m+=("$(apiq --data-urlencode "action=feedrecentchanges" --data-urlencode "days=90")")
	for x in "${m[@]}"; do absent "a change list after the move" "$x" "Falcon/Moved" "Falcon%2FMoved"; done
	say "restricted: moves show nothing"

	# a restricted redirect to a public page: the redirect lists refused, WhatLinksHere's redirects without it
	printf '#REDIRECT [[Main Page]]\n' | (cd "$mw" && php maintenance/run.php edit --user Custos --summary "shortcut" "Restricted:Falcon/Shortcut") \
		>> "$work/restricted.log" 2>&1 || { cat "$work/restricted.log"; fail_api "the restricted redirect could not be written"; }
	r=()
	for sp in ListRedirects BrokenRedirects DoubleRedirects UnwatchedPages ProtectedPages ProtectedTitles; do
		r+=("$(page --data-urlencode "title=Special:$sp" --data-urlencode "limit=500")")
	done
	r+=("$(page --data-urlencode "title=Special:WhatLinksHere/Main_Page" --data-urlencode "limit=500")")
	r+=("$(get_as "$djar" --data-urlencode "title=Special:ListRedirects" "$index")")
	r+=("$(apiq --data-urlencode "action=query" --data-urlencode "prop=redirects" --data-urlencode "titles=Main Page")")
	for x in "${r[@]}"; do absent "a redirect list" "$x" "Falcon/Shortcut"; done
	say "restricted: redirects show nothing"

	# a public redirect to a restricted page, existing or absent (written after the lists, whose needles its text carries): its
	# view by the agent and an anonymous request answers 403 for both, never the target's text; and a saved page transcluding
	# the restricted page by its literal title, parsed, carries none of its text
	printf '#REDIRECT [[%s]]\n' "$rtitle" | (cd "$mw" && php maintenance/run.php edit --user Custos --summary "public redirect" "Rehearsal_redirect_in") \
		>> "$work/restricted.log" 2>&1 || { cat "$work/restricted.log"; fail_api "the public redirect could not be written"; }
	printf '#REDIRECT [[Restricted:Falcon/Absent]]\n' | (cd "$mw" && php maintenance/run.php edit --user Custos --summary "public redirect" "Rehearsal_redirect_absent") \
		>> "$work/restricted.log" 2>&1 || { cat "$work/restricted.log"; fail_api "the public redirect could not be written"; }
	for rp in Rehearsal_redirect_in Rehearsal_redirect_absent; do
		for cjf in "$jar" /dev/null; do
			code=$(curl -s -b "$cjf" -o "$work/rrd.html" -w '%{http_code}' -G --data-urlencode "title=$rp" "$index") || code=000
			[ "$code" = 403 ] || fail_api "the view of $rp answered $code, not 403"
			absent "the view of $rp" "$(cat "$work/rrd.html")" "$rmark"
		done
	done
	printf '{{%s}} {{:%s}} size {{PAGESIZE:%s|R}}\n' "$rtitle" "$rtitle" "$rtitle" \
		| (cd "$mw" && php maintenance/run.php edit --user Custos --summary "transcluding" "Rehearsal transclusion literal") >> "$work/restricted.log" 2>&1 \
		|| { cat "$work/restricted.log"; fail_api "the literal transcluding page could not be written"; }
	p4=$(apiq --data-urlencode "action=parse" --data-urlencode "page=Rehearsal transclusion literal" --data-urlencode "prop=text")
	[ "$(member "$p4" parse title)" = "Rehearsal transclusion literal" ] || fail_api "the literal transcluding page was not parsed: $p4"
	absent "the literal transcluding page as parsed" "$p4" "$rmark"
	grep -q 'size 0' <<<"$p4" || fail_api "the parser read the restricted page's revision by its literal title: $p4"
	say "restricted: redirect to it refused"

	# The Declarer's group: the page read by its title (action=raw above, and its view), the transclusion still refused for it
	code=$(curl -s -b "$djar" -o "$work/rview.html" -w '%{http_code}' -G --data-urlencode "title=$rtitle" "$index") || code=000
	[ "$code" = 200 ] && grep -q "$rmark" "$work/rview.html" || fail_api "the Declarer's group's view of $rtitle answered $code"
	d1=$(get_as "$djar" --data-urlencode "format=json" --data-urlencode "formatversion=2" --data-urlencode "action=parse" \
		--data-urlencode "page=Rehearsal transclusion" --data-urlencode "prop=text" "$api")
	d2=$(get_as "$djar" --data-urlencode "format=json" --data-urlencode "formatversion=2" --data-urlencode "action=parse" \
		--data-urlencode "title=Sandbox" --data-urlencode "text={{$rtitle}}{{PAGESIZE:$rtitle|R}}" --data-urlencode "prop=text" "$api")
	[ "$(member "$d1" parse title)" = "Rehearsal transclusion" ] || fail_api "the transcluding page was not parsed for the Declarer's group: $d1"
	absent "the transcluding page parsed for the Declarer's group" "$d1" "$rmark"
	absent "a text transcluding it parsed for the Declarer's group" "$d2" "$rmark"
	say "restricted: read admitted"

	tickets=$( (cd "$mw" && php maintenance/run.php Custos:Ticket --count QUEUED) 2>/dev/null || echo "")
	say "api: the tickets QUEUED, no job run in a web request${tickets:+ ($tickets in the table)}"

	# The landing job on the seeded UWC: each op over HTTP, the job runner run once, the ticket polled; the
	# register read back over api.php. The built pcalc only: the stand-in answers no record function.
	if [ -x "$root/.lake/build/bin/pcalc" ]; then
		runjobs() { (cd "$mw" && php maintenance/run.php runJobs --type custosLand) > "$work/jobs.log" 2>&1 \
			|| { tail -n 20 "$work/jobs.log"; fail_api "runJobs failed"; }; }
		# land <op> [<name=value> ...]: the op, runJobs, POLL; prints "land: <op> <the answer's first member>"
		land() {
			local op=$1; shift
			post "$op" "prefix=$seedprefix" "$@"
			local t; t=$(member "$body" pma ticket)
			[ "$status" = 202 ] && [ -n "$t" ] || fail_api "$op answered $status: $body"
			runjobs
			local p; p=$(curl -s -b "$jar" -c "$jar" "$api?action=pma&op=POLL&ticket=$t&format=json&formatversion=2")
			[ "$(member "$p" pma state)" = DONE ] || { cat "$work/jobs.log"; fail_api "the $op ticket is not DONE after runJobs: $p"; }
			answer=$(member "$p" pma answer)
			first=$(php -r '$j = json_decode($argv[1], true); echo is_array($j) && $j !== [] ? array_key_first($j) : "";' "$answer")
		}
		# challenge_of <answer>: the answer's nonce of the execution challenge; respond <nonce>: the Research Client's
		# answer to it, by the client's own call of the Calculator (research_client.challenge, pcalc digest digest_fields)
		challenge_of() { php -r '$j = json_decode($argv[1], true); echo is_array($j) && is_string($j["challenge"] ?? null) ? $j["challenge"] : "";' "$1"; }
		respond() {
			python3 -I -c 'import sys; sys.path.insert(0, sys.argv[1]); from research_client.calculator import Calculator
from research_client.challenge import challenge_response
c = Calculator(sys.argv[2], Calculator.digest_of(sys.argv[2])); r = challenge_response(c, sys.argv[3])
print(r[1] if r[0] == "OK" else "")' "$root/client" "$res/pcalc" "$1"
		}
		# The api section's tickets (on the unseeded UWC Rehearsal) run first, and the agent's seat buckets are then
		# emptied, so the landing path's admissions start from a fresh account whatever those tickets charged.
		runjobs
		printf '$s = new Custos\\DbSeatStore(); $s->put("Rehearsalagent", "agent", 0, time()); $s->put("Rehearsalagent", "sponsor", 0, time());\n' \
			| (cd "$mw" && php maintenance/run.php eval) > "$work/fresh.log" 2>&1 || { cat "$work/fresh.log"; fail_api "the seat table could not be emptied"; }
		land PETITION block=b1
		[ "$first" = grant ] || fail_api "the PETITION was not granted: $answer"
		say "land: PETITION $first"
		nonce=$(challenge_of "$answer")
		[[ "$nonce" =~ ^[0-9a-f]{32}$ ]] || fail_api "the PETITION's grant carries no nonce of the execution challenge: $answer"
		# The structure test with register: the holder's STRUCTURE_TEST run by the job and answered with the line,
		# which the rehearsal compares with its own call of pcalc eom eom_register_test over the same Research
		# Assembly and register, read back from the pages. expected_says: what the line says beside its date,
		# composed here from pcalc's answer (REFUSED when pcalc refuses the test).
		expected_says() {
			local tfk recs
			tfk=$(block_of "Principia Machina/UWC/$seedprefix/Research Assembly/Starting Set" assembly)
			recs=$(block_of "$regtitle" register)
			printf '{"tfk":%s,"records":%s}' "$tfk" "$recs" | "$res/pcalc" eom eom_register_test \
				| php -r '$a = json_decode(trim(stream_get_contents(STDIN)), true);
					if (!is_array($a) || ($a[0] ?? "") !== "OK") { echo "REFUSED"; exit; }
					$f = $a[2]; $u = $a[3][1];
					echo ($f === [] ? "structurally regular with register" : "FINDINGS " . implode(" ", array_map(fn ($x) => json_encode($x, JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE), $f)))
						. " WITH " . ($u === [] ? "-" : implode(", ", $u));'
		}
		land STRUCTURE_TEST
		line=$(php -r '$j = json_decode($argv[1], true); echo is_array($j) ? (string)($j["structure_test"] ?? "") : "";' "$answer")
		[ "$first" = structure_test ] && [ "$line" = "$(block_of "$ixtitle" structure)" ] || fail_api "the holder's STRUCTURE_TEST was not answered with the line on the INDEX AND BADGE page: $answer"
		want=$(expected_says)
		[ "${line#STRUCTURE TEST ????-??-?? }" = "$want" ] || fail_api "the line \"$line\" is not the Calculator's answer \"$want\""
		say "structure: line $line equal to the Calculator's answer"
		# The job's wait: a second account's PETITION while the lock is held, run by Custos:Land, answered
		# LOCK HELD with a poll_after of the base (CustosPollAfter, 30) plus the governor's jitter, at most 10 per cent.
		hid=$(cd "$mw" && php maintenance/run.php Custos:Ticket --new PETITION --account Rehearsalsecond --prefix "$seedprefix" \
			--request "$(printf '{"block":"b3","prefix":"%s"}' "$seedprefix")") || fail_api "the second account's ticket could not be written"
		(cd "$mw" && php maintenance/run.php Custos:Land --ticket "$hid") > "$work/held.log" 2>&1 || { cat "$work/held.log"; fail_api "Custos:Land failed"; }
		held=$(cd "$mw" && php maintenance/run.php Custos:Ticket --answer "$hid") || fail_api "the second account's ticket is not answered"
		[ "$(php -r '$j = json_decode($argv[1], true); $p = $j["poll_after"] ?? null;
			echo is_array($j) && ($j["refused"] ?? "") === "LOCK HELD" && is_int($p) && $p >= 30 && $p <= 33 ? "ok" : "";' "$held")" = ok ] \
			|| fail_api "the second account's PETITION was not answered LOCK HELD with a jittered wait: $held"
		say "land: LOCK HELD poll_after jittered"
		records='[{"ASSUMPTIONS":[],"CITES":[],"CLASS":"RESULT","DERIVATION":{"STEPS":2,"TEXT":"The force law and the definition of v."},"EQUATION":"m * D(v, t) = -k_s * x","FALSIFIER":"A trajectory off the law.","FALSIFIER_CLASS":"F2","ID":"'"$seedprefix"'-1","REFS":["m","v","t","k_s","x"],"REGIME":"L","STATEMENT":"The equation of motion on the spring axis."},{"ASSUMPTIONS":[],"CITES":[],"CLASS":"ASSUMPTION","ID":"'"$seedprefix"'-2","PROPOSITION":"The mass is constant.","REFS":["m"]}]'
		land PUSH block=b1 "records=$records" "challenge_response=$(printf '0%.0s' {1..64})"
		[ "$(php -r '$j = json_decode($argv[1], true); echo ($j["refused"] ?? "") . " " . ($j["execution"] ?? "");' "$answer")" = "CHALLENGE REASONED" ] \
			|| fail_api "a wrong answer to the challenge was not refused REASONED: $answer"
		say "land: PUSH CHALLENGE REASONED"
		nonce=$(challenge_of "$answer")
		response=$(respond "$nonce")
		[[ "$response" =~ ^[0-9a-f]{64}$ ]] || fail_api "the Research Client did not answer the challenge"
		land PUSH block=b1 "records=$records" "challenge_response=$response"
		[ "$first" = landed ] && [ "$(php -r '$j = json_decode($argv[1], true); echo $j["execution"] ?? "";' "$answer")" = EXECUTED ] && [ "$(php -r '$j = json_decode($argv[1], true); echo implode(",", array_column($j["landed"] ?? [], "id"));' "$answer")" = "$seedprefix-1,$seedprefix-2" ] \
			|| fail_api "the PUSH did not land $seedprefix-1 and $seedprefix-2 (the records under the UWC's own prefix): $answer"
		say "land: PUSH $first EXECUTED"
		# The landing pushed one structure-test job for the UWC; the job runner runs it. The register as this
		# Custos lands it carries STATUS UNMARKED, which the Calculator's test refuses (a later corner): the
		# job writes nothing, and the rehearsal's own call of pcalc over the same pages refuses it too.
		queued=$( (cd "$mw" && php maintenance/run.php showJobs --type custosStructureTest) 2>/dev/null | tr -d '[:space:]')
		[ "$queued" = 1 ] || fail_api "the landing did not leave one structure-test job queued: ${queued:-none}"
		(cd "$mw" && php maintenance/run.php runJobs --type custosStructureTest) > "$work/structure.log" 2>&1 \
			|| { tail -n 20 "$work/structure.log"; fail_api "runJobs --type custosStructureTest failed"; }
		after=$(block_of "$ixtitle" structure)
		want=$(expected_says)
		if [ "$want" = REFUSED ]; then
			[ "$after" = "$line" ] || fail_api "the job wrote a line over a register the Calculator refuses: $after"
			say "structure: job after the landing, the Calculator refuses the landed register, line unchanged"
		else
			[ "${after#STRUCTURE TEST ????-??-?? }" = "$want" ] || fail_api "the job's line \"$after\" is not the Calculator's answer \"$want\""
			say "structure: job after the landing, line $after equal to the Calculator's answer"
		fi
		got=$(curl -s -b "$jar" -G --data-urlencode "action=query" --data-urlencode "format=json" --data-urlencode "formatversion=2" \
			--data-urlencode "prop=revisions" --data-urlencode "rvprop=content|user" --data-urlencode "rvslots=main" --data-urlencode "titles=$regtitle" "$api")
		read=$(php -r '$j = json_decode($argv[1], true); $r = $j["query"]["pages"][0]["revisions"][0] ?? [];
			$t = $r["slots"]["main"]["content"] ?? ""; $u = $r["user"] ?? "";
			if ($u !== "Custos" || !preg_match("#<pre class=\"pma-register\">\n(.*)\n</pre>#s", $t, $m)) { echo "0"; exit; }
			$recs = json_decode($m[1], true); echo is_array($recs) ? count(array_filter($recs, fn($x) => isset($x["DIGEST"])
				&& (($x["ID"] ?? "") === $argv[2] . "-1" && ($x["DERIVATION_CLASS"] ?? "") === "INSPECTION"
					|| ($x["ID"] ?? "") === $argv[2] . "-2" && !array_key_exists("DERIVATION_CLASS", $x)))) : 0;' "$got" "$seedprefix")
		[ "$read" = 2 ] || fail_api "the register page does not hold the two records with their digests, the first with DERIVATION_CLASS INSPECTION, the second with none: $got"
		say "land: READ $read records"
		land RELEASE block=b1
		[ "$first" = released ] || fail_api "the RELEASE was not answered released: $answer"
		say "land: RELEASE $first"

		# The lock's holder carried exactly: a scratch agent account whose name has a space, an apostrophe and a
		# letter outside ASCII (its password drawn as the agent's, kept in the scratch folder, mode 600, never
		# printed) petitions over HTTP and is granted; the LOCK PAGE's payload, read back through the Calculator
		# (pcalc canonical canonical_json), names it exactly; then it releases the lock.
		oddname="Rehearsal O'Brien $(printf '\303\211')lodie"
		umask 077
		if [ ! -s "$work/odd.pass" ]; then
			head -c 24 /dev/urandom | od -An -tx1 | tr -d ' \n' > "$work/odd.pass"
			printf 'Aa1!' >> "$work/odd.pass"
		fi
		chmod 600 "$work/odd.pass"
		umask 022
		(cd "$mw" && php maintenance/run.php createAndPromote --force --custom-groups=pma-agent "$oddname" "$(cat "$work/odd.pass")") \
			> "$work/odd.log" 2>&1 || fail_api "the scratch account could not be made (log: odd.log in the scratch folder)"
		# Its certificate, bound to a Sponsor of its own (a fresh bucket, as the account's own was before certificates): admission refuses an agent with none.
		ocert=$( (cd "$mw" && php maintenance/run.php Custos:Certify --agent "$oddname" --sponsor Rehearsaloddsponsor --d-is "$rdis" \
			--d-prompt "$rprompt" --family rehearsal --model rehearsal-model) 2>&1) || { printf '%s\n' "$ocert"; fail_api "Custos:Certify of the scratch account failed"; }
		[ "$(tail -n 1 <<<"$ocert")" = "certify: $oddname sponsor Rehearsaloddsponsor" ] \
			|| { printf '%s\n' "$ocert"; fail_api "Custos:Certify of the scratch account did not answer its line"; }
		ojar="$work/odd.cookies"
		: > "$ojar"
		chmod 600 "$ojar"
		login_as "$oddname" "$work/odd.pass" "$ojar"
		ocsrf=$(member "$(curl -s -b "$ojar" -c "$ojar" "$api?action=query&meta=tokens&format=json&formatversion=2")" query tokens csrftoken)
		[ -n "$ocsrf" ] && [ "$ocsrf" != '+\' ] || fail_api "no CSRF token for the scratch account"
		ajar=$jar
		acsrf=$csrf
		jar=$ojar
		csrf=$ocsrf
		land PETITION block=b5
		[ "$first" = grant ] || fail_api "the scratch account's PETITION was not granted: $answer"
		lockload=$(block_of "Principia Machina/UWC/$seedprefix/Lock" lock)
		lockread=$(printf '{"value":%s}' "$lockload" | "$res/pcalc" canonical canonical_json) || lockread=""
		[ "$(php -r '$c = json_decode($argv[1], true); $j = is_string($c) ? json_decode($c, true) : null;
			echo is_array($j) && $c === $argv[3] && ($j["holder"] ?? null) === $argv[2] && ($j["block"] ?? null) === "b5" ? "ok" : "";' \
			"$lockread" "$oddname" "$lockload")" = ok ] \
			|| fail_api "the LOCK PAGE read back through the Calculator does not name the scratch account exactly: $lockload"
		land RELEASE block=b5
		[ "$first" = released ] || fail_api "the scratch account's RELEASE was not answered released: $answer"
		jar=$ajar
		csrf=$acsrf
		say "lock: holder carried exactly"

		# The governor's refusal over HTTP: the agent's seat bucket primed past its burst (the seat store), a
		# PETITION run by the job and refused RATE; POLL answers the decision's 429 with its Retry-After.
		printf '(new Custos\\DbSeatStore())->put("Rehearsalagent", "agent", 200000, time());\n' \
			| (cd "$mw" && php maintenance/run.php eval) > "$work/prime.log" 2>&1 || { cat "$work/prime.log"; fail_api "the seat table could not be primed"; }
		post PETITION "prefix=$seedprefix" block=b4
		gt=$(member "$body" pma ticket)
		[ "$status" = 202 ] && [ -n "$gt" ] || fail_api "the primed PETITION answered $status: $body"
		runjobs
		gcode=$(curl -s -b "$jar" -c "$jar" -D "$work/govern.head" -o "$work/govern.json" -w '%{http_code}' \
			"$api?action=pma&op=POLL&ticket=$gt&format=json&formatversion=2") || gcode=000
		gafter=$(tr -d '\r' < "$work/govern.head" | sed -n 's/^[Rr]etry-[Aa]fter: *\([0-9][0-9]*\)$/\1/p' | head -n 1)
		[ "$gcode" = 429 ] && [ -n "$gafter" ] && [ "$gafter" = "$(member "$(cat "$work/govern.json")" pma retry_after)" ] \
			|| { cat "$work/govern.head" "$work/govern.json"; fail_api "the primed PETITION's POLL answered $gcode, Retry-After ${gafter:-none}"; }
		say "govern: POLL 429 retry-after"

		# The sweep: a ticket written QUEUED with no job (Custos:Ticket --new), the job runner finding nothing to
		# run; with the sweep age 0, POLL over HTTP pushes its job, and the job runner answers it.
		settings "$res/pcalc" 0
		sid=$(cd "$mw" && php maintenance/run.php Custos:Ticket --new PETITION --account Rehearsalagent --prefix "$seedprefix" \
			--request "$(printf '{"block":"b2","prefix":"%s"}' "$seedprefix")") || fail_api "the sweep's ticket could not be written"
		[[ "$sid" =~ ^[1-9][0-9]*$ ]] || fail_api "the sweep's ticket is not a number: $sid"
		pollof() { curl -s -b "$jar" -c "$jar" "$api?action=pma&op=POLL&ticket=$1&format=json&formatversion=2"; }
		runjobs
		[ "$(member "$(pollof "$sid")" pma state)" = QUEUED ] || fail_api "the sweep's ticket was run with no job: $(pollof "$sid")"
		runjobs
		sp=$(pollof "$sid")
		[ "$(member "$sp" pma state)" = DONE ] || { cat "$work/jobs.log"; fail_api "the sweep's ticket is not DONE after POLL and runJobs: $sp"; }
		answer=$(member "$sp" pma answer)
		# answered by the job: a grant, or the governor's refusal of an account that has just landed (RATE:
		# {"refused": "ADMISSION", "decision": {"refusal": "RATE", ...}}); any other refusal (a JOB FAULT, a
		# CALCULATOR FAULT) fails the line
		[ "$(php -r '$j = json_decode($argv[1], true); echo is_array($j) && (isset($j["grant"]) || (($j["refused"] ?? null) === "ADMISSION" && ($j["decision"]["refusal"] ?? null) === "RATE")) ? "answered" : "";' "$answer")" = answered ] \
			|| fail_api "the sweep's PETITION was not answered by the job with a grant or the RATE refusal: $answer"
		settings "$res/pcalc"
		say "sweep: a QUEUED ticket without its job, re-enqueued on POLL, answered"

		# The batch jobs' frame: each of the three enqueued by Custos:Job, run by the job runner, its last run read back
		# (the bodies answer NOT BUILT until their units); then lane 5 refused at the level STRAINED ($wgCustosBatch), the
		# run ending DEFERRED with the job's body not run.
		batch() { # batch <name> <type>: enqueue, run, print the last run's outcome (its first line)
			(cd "$mw" && php maintenance/run.php Custos:Job --job "$1") > "$work/batch.log" 2>&1 || { cat "$work/batch.log"; fail_api "Custos:Job --job $1 failed"; }
			(cd "$mw" && php maintenance/run.php runJobs --type "$2") > "$work/batch.log" 2>&1 || { cat "$work/batch.log"; fail_api "runJobs of $2 failed"; }
			(cd "$mw" && php maintenance/run.php Custos:Job --last "$1" | head -n 1)
		}
		for pair in "reaudit custosReaudit" "cluster custosCluster" "recheck custosRecheck"; do
			read -r jn jt <<<"$pair"
			[ "$(batch "$jn" "$jt")" = "NOTHING DUE" ] || fail_api "the job $jn did not end NOTHING DUE (NOT BUILT)"
			say "job: $jn NOTHING DUE"
		done
		printf '$wgCustosBatch = [ "pressure" => "STRAINED" ];\n' >> "$mw/LocalSettings.custos.php"
		[ "$(batch reaudit custosReaudit)" = DEFERRED ] || fail_api "the job reaudit was not DEFERRED at the level STRAINED"
		settings "$res/pcalc"
		say "job: refused DEFERRED"
	else
		say "land: not run (the stand-in fake_pcalc.sh answers no record function)"
	fi
	kill "$server" 2>/dev/null || true
	server=
fi

# 6. The same wiring with the tampered binary swapped in at the residence's pcalc: refused before it is
# started; and a landing run by hand (Custos:Land) with the tampered binary swapped in, on a seeded UWC: the ticket answered INTEGRITY HALT, its
# register page unchanged. The ticket is written and its answer read through the extension's ticket
# store (Custos:Ticket), never by a path to the wiki's database: an installed wiki keeps it where its
# LocalSettings.php says.
land_tamper() {
	local px="Tamper$(date +%s)" reg before after id lout lcode=0
	settings "$res/pcalc"
	(cd "$mw" && php maintenance/run.php Custos:SeedUwc --prefix "$px" \
		--draft "$root/docs/v1/tpx/TPX/examples/spring_draft.json") > "$work/tamper-seed.log" 2>&1 || { cat "$work/tamper-seed.log"; return 1; }
	reg="Principia Machina/UWC/$px/Register/Volume 1"
	before=$(cd "$mw" && php maintenance/run.php getText "$reg")
	id=$(cd "$mw" && php maintenance/run.php Custos:Ticket --new PUSH --account Rehearsalagent --prefix "$px" \
		--request "$(printf '{"block":"b1","prefix":"%s","records":"[]"}' "$px")") || { say "tamper: the ticket could not be written"; return 1; }
	swap
	lout=$(cd "$mw" && php maintenance/run.php Custos:Land --ticket "$id" 2>&1) || lcode=$?
	unswap
	after=$(cd "$mw" && php maintenance/run.php getText "$reg")
	printf '%s\n' "$lout"
	answer=$(cd "$mw" && php maintenance/run.php Custos:Ticket --answer "$id") || answer=""
	if [ "$lcode" -ne 0 ] && grep -q '^DIGEST MISMATCH: ' <<<"$lout" && [ "$before" = "$after" ] && grep -q '"refused":"INTEGRITY HALT"' <<<"$answer"; then
		say "tamper: land DIGEST MISMATCH, the ticket answered INTEGRITY HALT, the register page unchanged"
		return 0
	fi
	say "tamper: the landing with the tampered binary was not halted (exit $lcode), or the register page changed"
	return 1
}
land_ok=1
if [ -x "$root/.lake/build/bin/pcalc" ]; then
	land_tamper || land_ok=0
fi
swap
code=0
out=$(wiring) || code=$?
unswap
if [ -n "$tamper_only" ]; then
	printf '%s\n' "$out"
	if [ "$land_ok" -ne 1 ]; then
		say "rehearsal: FAIL (the tampered landing)"
		exit 2
	fi
	exit 1
fi
if [ "$land_ok" -ne 1 ]; then
	say "rehearsal: FAIL (the tampered landing)"
	exit 1
fi
if [ "$code" -eq 1 ] && grep -q '^DIGEST MISMATCH: ' <<<"$out"; then
	say "tamper: DIGEST MISMATCH, the tampered binary refused and not started"
else
	printf '%s\n' "$out"
	say "rehearsal: FAIL (the tampered binary was not refused)"
	exit 1
fi

# 7. The same wiring with a group-writable binary of the right digest: refused before the digest check
settings "$res/pcalc-writable"
code=0
out=$(wiring) || code=$?
settings "$res/pcalc"
if [ "$code" -eq 1 ] && grep -q '^UNSAFE RESIDENCE: ' <<<"$out" && ! grep -q '^DIGEST MISMATCH: ' <<<"$out"; then
	say "residence: UNSAFE RESIDENCE, the group-writable binary refused and not started"
else
	printf '%s\n' "$out"
	say "rehearsal: FAIL (the group-writable binary was not refused)"
	exit 1
fi
say "rehearsal: ALL PASS"
