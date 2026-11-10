import Principia.Sha256

/-!
# Digests and their preimages

The digest convention (carried unchanged from version 1): a digest is
SHA-256 over the netstring encoding of an ordered field list. Each field is
its byte length in decimal, a colon, then its bytes; a string as UTF-8. The
digest is written as 64 lowercase hexadecimal characters (TPS 2.5.10).

This file holds the encoding, the preimage of every digest, and the digests
over it; SHA-256 itself is `Principia.Sha256` (the Declarer's choice of SHA-256).
-/

namespace Principia.Digest

/-- Netstring encoding of one field: `<len>:<bytes>`. -/
def netstring (s : String) : String :=
  s!"{s.utf8ByteSize}:{s}"

/-- Netstring encoding of an ordered field list: the fields' netstrings
concatenated. This is the preimage of every PMA digest. -/
def preimage (fields : List String) : String :=
  String.join (fields.map netstring)

theorem netstring_empty : netstring "" = "0:" := by decide

theorem preimage_nil : preimage [] = "" := by decide

/-- A worked example from the digest convention. -/
theorem preimage_example :
    preimage ["TPC-EXECUTION-CHALLENGE", "1", "ab"] =
      "23:TPC-EXECUTION-CHALLENGE1:12:ab" := by decide

/-! ## Fields and digests (v1 tpc_digest `digest_fields`, `combine_digests`, `d_tfk`) -/

/-- A digest field (v1 `_as_bytes`): a text, as its UTF-8 bytes, or an integer, as
its base-10 ASCII digits. A boolean is not a field; a field list names a token
instead. -/
inductive Field where
  | text (s : String)
  | int (n : Int)
  deriving Repr, DecidableEq

/-- The bytes a field contributes to a preimage. -/
def Field.bytes : Field → String
  | .text s => s
  | .int n => toString n

/-- The preimage of an ordered field list (v1 `preimage_fields`). -/
def preimageFields (fields : List Field) : String :=
  preimage (fields.map Field.bytes)

/-- A digest as text: 64 lowercase hexadecimal characters. -/
def isHex64 (s : String) : Bool :=
  s.length == 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The preimage of an ordered list of digests (v1 `preimage_digests`, the combination
rule of TPS 2.5.3), or `none` when one of them is not 64 lowercase hexadecimal
characters. -/
def preimageDigests (digests : List String) : Option String :=
  if digests.all isHex64 then some (preimage digests) else none

/-- The preimage of the Research Assembly's digest D(RAS) (v1 `d_tfk`): its three
zones' digests combined in the fixed order Starting Set, Correspondence Table,
Criteria Set. -/
def preimageResearchAssembly (startingSet correspondence criteria : String) :
    Option String :=
  preimageDigests [startingSet, correspondence, criteria]

/-- An integer field and its decimal text have one preimage: a field list names its
fields' kinds by position, never by the bytes (v1's vector `int-and-str-collide`). -/
theorem preimageFields_int_text :
    preimageFields [.text "10", .int 10] = "2:102:10" := by decide

theorem preimageDigests_refuses :
    preimageDigests ["0123"] = none := by decide

/-! ## The digests (v1 tpc_digest `digest_fields`, `combine_digests`, `d_tfk`) -/

/-- The digest of a preimage: SHA-256 of its UTF-8 bytes, in lowercase hexadecimal. -/
def ofPreimage (preimage : String) : String :=
  Sha256.digestText preimage

/-- The digest of an ordered field list (v1 `digest_fields`). -/
def digestFields (fields : List Field) : String :=
  ofPreimage (preimageFields fields)

/-- The digest of an ordered list of digests (v1 `combine_digests`), or `none` when one of
them is not 64 lowercase hexadecimal characters. -/
def combineDigests (digests : List String) : Option String :=
  (preimageDigests digests).map ofPreimage

/-- The Research Assembly's digest D(RAS) (v1 `d_tfk`): its three zones' digests combined
in the fixed order Starting Set, Correspondence Table, Criteria Set. -/
def digestResearchAssembly (startingSet correspondence criteria : String) : Option String :=
  (preimageResearchAssembly startingSet correspondence criteria).map ofPreimage

/-- Every digest is 64 characters. -/
theorem ofPreimage_length (preimage : String) : (ofPreimage preimage).length = 64 :=
  Sha256.digestText_length preimage

/-! ## The tree encoding (v1 tpc_zone `_node`)

A zone's preimage is a tree of texts, integers and lists, written as a type-tagged
recursive netstring: a text `s` then its bytes, an integer `i` then its base-10
digits, a list `l` then the netstrings of its children. The tags keep a text apart
from an integer and a leaf apart from a list. v1 normalized each text first (line
endings to LF, Unicode NFC); here a text is written as given, its normalization being
the zone serializer's (`Principia.Zone.node`, at Unicode 15.1.0). Which zone fields
enter the tree, in which order, is the zones' port (`Principia.Zone.Preimage`). -/

/-- A tree of a zone's preimage. -/
inductive Tree where
  | text (s : String)
  | int (n : Int)
  | list (children : List Tree)
  deriving Repr, Inhabited, BEq

mutual
/-- The tree encoding of a zone's preimage. -/
def Tree.preimage : Tree → String
  | .text s => "s" ++ s
  | .int n => "i" ++ toString n
  | .list xs => "l" ++ Tree.childrenPreimage xs

/-- A list's children, each as the netstring of its own encoding. -/
def Tree.childrenPreimage : List Tree → String
  | [] => ""
  | x :: xs => netstring x.preimage ++ Tree.childrenPreimage xs
end

/-- The empty list, the empty text and zero, each tagged. -/
theorem Tree.preimage_leaves :
    (Tree.list [.text "", .int 0, .list []]).preimage = "l1:s2:i01:l" := by decide

/-- The children's encoding of two lists joined is the two encodings joined. -/
theorem Tree.childrenPreimage_append (xs ys : List Tree) :
    Tree.childrenPreimage (xs ++ ys) = Tree.childrenPreimage xs ++ Tree.childrenPreimage ys := by
  induction xs with
  | nil => simp only [List.nil_append, Tree.childrenPreimage, String.empty_append]
  | cons x xs ih =>
    simp only [List.cons_append, Tree.childrenPreimage, ih, String.append_assoc]

/-- A tree's encoding is never empty: it opens with its tag. -/
theorem Tree.preimage_ne_empty (t : Tree) : t.preimage ≠ "" := fun h => by
  have := congrArg String.toList h
  cases t <;> simp [Tree.preimage, String.toList_append] at this

end Principia.Digest
