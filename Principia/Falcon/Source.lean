import Principia.Falcon.Canon

/-!
# The source match and its hops

v1's `tpc_falcon` 0.2.0 (FM-15; SERVED from 0.1.1, RD-17):
`source_match(cited_url, source_list)`, the FALCON SOURCE LIST entry a citation falls
under and the URL TPX fetches; and `source_hop(hop_url, matched, source_list)`, a
redirect hop matched again at entry level (SM1 to SM10 in v1's text).

* `checkSources`: the list's validation, CODE HOST marks first (v1's two passes), then
  each entry in order: its canonical URL (`canonUrl`) must be https with a host name, no
  userinfo, no fragment, a port only as `:` and digits, a path SM2 does not refuse (not
  for SERVED) and no query on a PREFIX; SM1's PUBLISHER TEST on every PREFIX.
* `pathBad` (SM2): the path as written, percent-decoded until it settles, over its bytes;
  `utf8Ok` is RFC 3629's well-formed UTF-8, as Python's decoder reads it.
* `matchCited` (SM3 to SM8, SM10): EXACT first, then SERVED (not for a hop), then the
  longest PREFIX, the first in list order among equals.

No decision is open here: every case is judged.
-/

namespace Principia.Falcon.Source

open Principia.Canonical (Value)
open Principia.Falcon

/-! ## A canonical URL's parts -/

/-- v1's `_url_parts` of a URL in `canon_url`'s form. -/
structure Parts where
  scheme : Option (List Char)
  userinfo : Option (List Char)
  host : Option (List Char)
  port : List Char
  path : List Char
  query : Option (List Char)
  fragment : Option (List Char)

/-- v1's `_url_parts(c)`. -/
def urlParts (c : List Char) : Parts :=
  let p := splitReference c
  let (ui, host, port) : Option (List Char) × Option (List Char) × List Char :=
    match p.authority with
    | none => (none, none, [])
    | some auth =>
      let (ui, hp) : Option (List Char) × List Char :=
        if auth.contains '@' then
          (some (auth.takeWhile (· ≠ '@')), (auth.dropWhile (· ≠ '@')).drop 1)
        else (none, auth)
      match hp with
      | '[' :: _ =>
        match hp.findIdx? (· == ']') with
        | some k => (ui, some (hp.take (k + 1)), hp.drop (k + 1))
        | none => (ui, some [], hp)
      | _ => (ui, some (hp.takeWhile (· ≠ ':')), hp.dropWhile (· ≠ ':'))
  { scheme := p.scheme, userinfo := ui, host, port, path := p.path, query := p.query,
    fragment := p.fragment }

/-- A string of ASCII digits and dots, at least one (`[0-9.]+`). -/
def digitsAndDots (cs : List Char) : Bool := !cs.isEmpty && cs.all fun c => c.isDigit || c == '.'

/-- v1's `_host_ok`: a host name, not empty, not an IP literal, not digits and dots, and
no `%`. -/
def hostOk : Option (List Char) → Bool
  | some h => !h.isEmpty && h.head? != some '[' && !digitsAndDots h && !h.contains '%'
  | none => false

/-! ## SM2: the path rules -/

/-- RFC 3629's well-formed UTF-8 (v1's `_utf8_ok`, Python's decoder): no overlong form,
no surrogate, no code point past U+10FFFF, no truncated sequence. -/
def utf8Ok : List Nat → Bool
  | [] => true
  | b :: rest =>
    let cont (x : Nat) : Bool := 0x80 ≤ x && x ≤ 0xBF
    if b ≤ 0x7F then utf8Ok rest
    else if 0xC2 ≤ b && b ≤ 0xDF then
      match rest with
      | x :: r => cont x && utf8Ok r
      | [] => false
    else if 0xE0 ≤ b && b ≤ 0xEF then
      match rest with
      | x :: y :: r =>
        (if b == 0xE0 then 0xA0 ≤ x && x ≤ 0xBF
          else if b == 0xED then 0x80 ≤ x && x ≤ 0x9F
          else cont x) && cont y && utf8Ok r
      | _ => false
    else if 0xF0 ≤ b && b ≤ 0xF4 then
      match rest with
      | x :: y :: z :: r =>
        (if b == 0xF0 then 0x90 ≤ x && x ≤ 0xBF
          else if b == 0xF4 then 0x80 ≤ x && x ≤ 0x8F
          else cont x) && cont y && cont z && utf8Ok r
      | _ => false
    else false

/-- A byte that is an ASCII hexadecimal digit, either case. -/
def hexByte (b : Nat) : Bool :=
  (0x30 ≤ b && b ≤ 0x39) || (0x41 ≤ b && b ≤ 0x46) || (0x61 ≤ b && b ≤ 0x66)

/-- An ASCII hexadecimal digit's value. -/
def hexByteValue (b : Nat) : Nat :=
  if b ≤ 0x39 then b - 0x30 else if b ≤ 0x46 then b - 0x41 + 10 else b - 0x61 + 10

/-- v1's `_ENC_SEP.search`: an encoded `/` or backslash, `%2F` or `%5C` in either case. -/
def encodedSeparator : List Nat → Bool
  | 0x25 :: a :: b :: rest =>
    (a == 0x32 && (b == 0x46 || b == 0x66)) || (a == 0x35 && (b == 0x43 || b == 0x63)) ||
      encodedSeparator (a :: b :: rest)
  | _ :: rest => encodedSeparator rest
  | [] => false

/-- v1's `_PCT_ANY.sub(chr(int(XX, 16)))`: from left to right, each `%XX` becomes its
byte. -/
def percentDecode : List Nat → List Nat
  | 0x25 :: rest@(a :: b :: r) =>
    if hexByte a && hexByte b then (hexByteValue a * 16 + hexByteValue b) :: percentDecode r
    else 0x25 :: percentDecode rest
  | x :: rest => x :: percentDecode rest
  | [] => []

/-- The decoding stages of SM2, at most `fuel` decodings: the settled path, or `none`
when a stage holds an encoded separator, a backslash or bytes that are not UTF-8, or
when the decodings do not settle. -/
def settle : Nat → List Nat → Option (List Nat)
  | 0, _ => none
  | f + 1, cur =>
    if encodedSeparator cur || cur.contains 0x5C || !utf8Ok cur then none
    else
      let nxt := percentDecode cur
      if nxt == cur then some cur else settle f nxt

/-- v1's `_path_bad` (SM2) of a path as written: refused when it does not settle within
seven decodings, or a stage is refused, or the settled path holds a `;` or a `.` or `..`
segment. -/
def pathBad (path : List Char) : Bool :=
  match settle 8 (path.map Char.toNat) with
  | none => true
  | some cur =>
    cur.contains 0x3B || (cur.splitOn 0x2F).any fun s => s == [0x2E] || s == [0x2E, 0x2E]

/-! ## The list -/

/-- v1's `_HOSTNAME`: `[a-z0-9]`, optionally `[a-z0-9.-]*` and `[a-z0-9]`. -/
def hostNameOk (h : List Char) : Bool :=
  let end_ (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || c.isDigit
  match h.head?, h.getLast? with
  | some f, some l => end_ f && end_ l && h.all fun c => end_ c || c == '.' || c == '-'
  | _, _ => false

/-- A template segment's character (v1's `_TEMPLATE` class). -/
def templateChar (c : Char) : Bool := c.isAlphanum || "._~!$&'()*+,=:@-".toList.contains c

/-- v1's `_TEMPLATE`: segments `/` and one or more template characters, then `/`. -/
def templateOk (t : List Char) : Bool :=
  match t with
  | '/' :: rest =>
    rest.getLast? == some '/' &&
      (rest.dropLast.splitOn '/').all fun s => !s.isEmpty && s.all templateChar
  | _ => false

/-- Python's `s.strip("/")`. -/
def stripSlashes (cs : List Char) : List Char :=
  ((cs.dropWhile (· == '/')).reverse.dropWhile (· == '/')).reverse

/-- `s.strip("/").split("/")`. -/
def segments (cs : List Char) : List (List Char) := (stripSlashes cs).splitOn '/'

/-- v1's `_tmpl_ok(segs, tmpl)`: the segments reach the template, and its last `*`, the
name or revision slot, is not `refs` in any ASCII case. -/
def tmplOk (segs tmpl : List (List Char)) : Bool :=
  decide (tmpl.length ≤ segs.length) &&
    (tmpl.zip segs).all (fun (t, s) => (t == ['*'] && !s.isEmpty) || t == s) &&
    (match ((tmpl.zip segs).filter (·.1 == ['*'])).getLast? with
      | none => true
      | some (_, s) =>
        !(s.all (fun c => c.toNat ≤ 127) && (s.map Char.toLower) == "refs".toList))

/-- An entry's kind. -/
inductive Kind where
  | exact
  | pfx
  | served
  deriving DecidableEq, Repr

/-- v1's word for a kind. -/
def Kind.word : Kind → String
  | .exact => "EXACT"
  | .pfx => "PREFIX"
  | .served => "SERVED"

/-- An entry of the list as v1's `_check_sources` keeps it. -/
structure Entry where
  kind : Kind
  host : List Char
  port : List Char
  path : List Char
  query : Option (List Char)
  url : List Char

/-- A CODE HOST mark: its host and templates, each as segments. -/
def codeHostOf (e : Value) : Option (Except String (String × List (List (List Char)))) :=
  match e with
  | .arr (.str "CODE HOST" :: h :: tps) =>
    some <| match h with
      | .str hs =>
        if !hostNameOk hs.toList || digitsAndDots hs.toList then .error "sources"
        else
          match tps.mapM (fun tp => match tp with
              | .str t => if templateOk t.toList then some (segments t.toList) else none
              | _ => none) with
          | some tl => .ok (hs, tl)
          | none => .error "sources"
      | _ => .error "sources"
  | _ => none

/-- The CODE HOST marks in order, a host named twice refused (v1's first pass). -/
def codeHosts (es : List Value) : Except String (List (String × List (List (List Char)))) :=
  es.foldlM (fun acc e =>
    match codeHostOf e with
    | none => .ok acc
    | some (.error w) => .error w
    | some (.ok (h, tl)) =>
      if acc.any (·.1 == h) then .error "sources" else .ok (acc ++ [(h, tl)])) []

/-- A port as v1's entries take it: none, or `:` and one digit or more. -/
def entryPortOk (port : List Char) : Bool :=
  match port with
  | [] => true
  | ':' :: ds => !ds.isEmpty && ds.all Char.isDigit
  | _ => false

/-- One entry of the list, not a CODE HOST mark (v1's second pass). -/
def entryOf (code : List (String × List (List (List Char)))) (e : Value) :
    Except String (Option Entry) :=
  match e with
  | .arr (.str "CODE HOST" :: _ :: _) => .ok none
  | .arr [k, u] =>
    let kind? : Option Kind := match k with
      | .str "EXACT" => some .exact
      | .str "PREFIX" => some .pfx
      | .str "SERVED" => some .served
      | _ => none
    match kind?, u with
    | some kind, .str us =>
      match canonUrlChars us.toList with
      | none => .error "sources"
      | some c =>
        let p := urlParts c
        let raw := (splitReference us.toList).path
        if p.scheme != some "https".toList || p.host.isNone || p.userinfo.isSome ||
            !hostOk p.host || p.fragment.isSome || !entryPortOk p.port ||
            (kind != .served && pathBad raw) || (kind == .pfx && p.query.isSome) then
          .error "sources"
        else
          let host := p.host.getD []
          let path := if p.path.isEmpty then ['/'] else p.path
          let url := "https://".toList ++ host ++ p.port ++ path ++
            (match p.query with | some q => '?' :: q | none => [])
          let entry : Entry :=
            { kind := kind, host := host, port := p.port, path := path, query := p.query,
              url := url }
          if kind == .pfx then
            if path == ['/'] then .error "publisher"
            else
              match code.find? (·.1.toList == host) with
              | some (_, tl) =>
                if tl.any (tmplOk (segments path)) then .ok (some entry) else .error "publisher"
              | none => .ok (some entry)
          else .ok (some entry)
    | _, _ => .error "sources"
  | _ => .error "sources"

/-- v1's `_check_sources`: the entries in order, `none` for a CODE HOST mark; or the
refusal (`sources`, `publisher`). -/
def checkSources (sourceList : Value) : Result (List (Option Entry)) :=
  match sourceList with
  | .arr es =>
    match codeHosts es with
    | .error w => refuse w
    | .ok code =>
      match es.mapM (entryOf code) with
      | .ok out => .ok out
      | .error w => refuse w
  | _ => refuse "sources"

/-! ## The match -/

/-- A citation's match: an entry, or UNKNOWN with the reason. -/
inductive Matched where
  | entry (index : Nat) (kind : Kind) (declared : List Char) (fetch : List Char)
  | unknown (reason : String)
  deriving DecidableEq, Repr

/-- The first entry, in list order, a test picks, with its index. -/
def firstEntry (entries : List (Option Entry)) (p : Entry → Bool) : Option (Nat × Entry) :=
  ((List.range entries.length).zip entries).findSome? fun (i, e) =>
    match e with
    | some e => if p e then some (i, e) else none
    | none => none

/-- The longest PREFIX entry covering the path, the first in list order among equals. -/
def longestPrefix (entries : List (Option Entry)) (host port path : List Char) :
    Option (Nat × Entry) :=
  ((List.range entries.length).zip entries).foldl (fun best (i, e) =>
    match e with
    | some e =>
      if e.kind == .pfx && e.host == host && e.port == port then
        let p := e.path
        let under := p.isPrefixOf path &&
          (p.getLast? == some '/' || (path.drop p.length).head? == some '/')
        if path == p || under then
          match best with
          | some (_, b) => if b.path.length < p.length then some (i, e) else best
          | none => some (i, e)
        else best
      else best
    | none => best) none

/-- v1's `_match(cited_url, entries, hop)` (SM3 to SM8, SM10). -/
def matchCited (cited : Value) (entries : List (Option Entry)) (hop : Bool) : Matched :=
  match cited with
  | .str cs =>
    match canonUrlChars cs.toList with
    | none => .unknown "url"
    | some c =>
      let p := urlParts c
      match p.host with
      | none => .unknown "url"
      | some host =>
        if p.scheme != some "https".toList then .unknown "scheme"
        else if p.userinfo.isSome then .unknown "userinfo"
        else if !hostOk p.host then .unknown "host"
        else
          let bad := pathBad (splitReference cs.toList).path
          let path := if p.path.isEmpty then ['/'] else p.path
          let exact := if bad then none else firstEntry entries fun e =>
            e.kind == .exact && e.host == host && e.port == p.port && e.path == path &&
              (e.query.isNone || e.query == p.query)
          match exact with
          | some (i, e) => .entry i .exact e.url e.url
          | none =>
            let served := if hop then none else firstEntry entries fun e =>
              e.kind == .served && e.host == host && e.port == p.port && e.path == path &&
                e.query == p.query
            match served with
            | some (i, e) => .entry i .served e.url "STORE".toList
            | none =>
              if bad then .unknown "path"
              else
                match longestPrefix entries host p.port path with
                | some (i, e) => .entry i .pfx e.url ("https://".toList ++ host ++ p.port ++ path)
                | none => .unknown "none"
  | _ => .unknown "url"

/-- v1's `source_match(cited_url, source_list)`. -/
def sourceMatch (cited sourceList : Value) : Result Matched := do
  let entries ← checkSources sourceList
  return matchCited cited entries false

/-- v1's `source_hop(hop_url, matched, source_list)`: the hop's match, and whether it
stays in the entry the citation matched. -/
def sourceHop (hopUrl matched sourceList : Value) : Result (Matched × Bool) := do
  let entries ← checkSources sourceList
  let i ← match matched with
    | .int i =>
      if 0 ≤ i && i < entries.length then
        match entries[i.toNat]? with
        | some (some e) => if e.kind == .served then refuse "matched" else pure i.toNat
        | _ => refuse "matched"
      else refuse "matched"
    | _ => refuse "matched"
  let d := matchCited hopUrl entries true
  let stays := match d with
    | .entry j _ _ _ => j == i
    | .unknown _ => false
  return (d, stays)

/-! ## The renders -/

/-- v1's `render_source`. -/
def renderSource : Matched → String
  | .unknown r => "source|UNKNOWN|" ++ r
  | .entry i k declared fetch =>
    s!"source|ENTRY|{i}|{k.word}|{esc (String.ofList declared)}\nfetch|{esc (String.ofList fetch)}"

/-- v1's `render_hop`. -/
def renderHop : Matched × Bool → String
  | (d, stays) =>
    renderSource d ++ "\n" ++
      match d with
      | .unknown _ => "hop|END"
      | .entry .. => if stays then "hop|SAME" else "hop|OTHER"

end Principia.Falcon.Source
