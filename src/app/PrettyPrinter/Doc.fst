module Doc

open FStar.String
open FStar.List.Tot
module R = FStar.Reflection.Builtins
module RD = FStar.Reflection.Data

type position = | Position: col:nat -> line:nat -> position
type range_info = | RangeInfo: file:string -> startp: position -> endp: position -> range_info

let string_of_position (Position c l) = "(" ^ string_of_int (1 + l) ^ ":" ^ string_of_int c ^ ")"
let string_of_range_info (RangeInfo file s e) = file ^ ":" ^ string_of_position s ^ ":" ^ string_of_position e
 
// let range_to_range_info (r: range)
//   = let max (x y: int) = if x > y then x else y in
//     let h (t: int*int) = Position (max (snd t) 0) (max (fst t - 1) 0) in
//     let r = R.inspect_range r in
//     RangeInfo r.RD.file_name (h r.RD.start_pos) (h r.RD.end_pos)

type doc (a: Type) =
  | DAnnotated: doc a -> a -> doc a
  | DString: string -> doc a
  | DIndent: d: doc a -> doc a
  | DConcat: doc a -> doc a -> doc a
  | DNewLine | DEmpty

let annote #a: doc a -> a -> doc a = DAnnotated
let str #a: string -> doc a = DString
let (<+>) #a: doc a -> doc a -> doc a = DConcat
let nl #a: doc a = DNewLine
let empty #a: doc a = DEmpty
let indent #a: doc a -> doc a = DIndent
let concat #a: list (doc a) -> doc a = function
  | [] -> empty
  | hd::tl -> fold_left (<+>) hd tl
let space = str " "

let lparen = str "("
let rparen = str ")"
let lbrace = str "{"
let rbrace = str "}"

let semicolon = str ";"
let klet      = str "let"
let kequal    = str "="
let comma     = str ","
let dot       = str "."

let rec prependToAll sep
  = function | [] -> [] | hd::tl -> sep::hd::prependToAll sep tl
 
let intersperse sep
  = function | [] -> [] | a::tl -> a::prependToAll sep tl
  
let concatSep #a (sep:doc a) (l:list (doc a)): doc a
  = concat (intersperse sep l)

type atom = | AStr: string -> atom | ANewLine
type flat_annot a = | Annot : pstart:nat -> pend:nat {pend >= pstart} -> body:a -> flat_annot a
type flat_doc' a = list atom * list (flat_annot a)
let wf_flat_doc' (atoms: list atom) (annots: list (flat_annot 'a))
    = forall a. memP a annots ==> Annot?.pend a < length atoms
let flat_doc a = fd: flat_doc' a {wf_flat_doc' (fst fd) (snd fd)}

let rec lemma_concat_annots (atoms: list atom) (annots0 annots1: list (flat_annot 'a))
    : Lemma (requires (wf_flat_doc' atoms annots0 /\ wf_flat_doc' atoms annots1))
      	    (ensures  wf_flat_doc' atoms (annots0@annots1) )
	    [SMTPat (wf_flat_doc' atoms (annots0@annots1))]
    = match annots0 with | [] -> ()
    | hd::tl -> lemma_concat_annots atoms tl annots1

let max x y = if x > y then x else y
let max_offset_list (l: list 'a) = max 0 (length l - 1)
let offset (n: nat) (Annot s e a) = Annot (n+s) (n+e) a

let rec insert_after (#a: eqtype) (x: a) (insert: a) (l: list a): (r: list a {length r == length l + count x l})
    = match l with | [] -> []
    | hd::tl -> if hd <> x then hd::insert_after x insert tl
      	      else hd::insert::insert_after x insert tl

let rec prefix_of (#a: Type) (l1 l2: list a)
= match l1, l2 with | [], _ -> True
  | hd::tl, hd'::tl' -> hd==hd' /\ prefix_of tl tl' | _ -> False
let rec take (#a: eqtype) (l: list a) (n: nat {n <= length l}): r: list a {length r = n /\ (forall x. count x r <= count x l) }
    = if n=0 then [] else 
      let hd::tl = l in hd::take tl (n-1)

let rec lemma_count_take (#a: eqtype) (x: a) (l: list a) n m
    : Lemma (requires n <= m) (ensures count x (take l n) <= count x (take l m) )
      	    [SMTPat (count x (take l n)); SMTPat (count x (take l m))]
    = match l with
    | [] -> ()
    | hd::tl -> if n=0 || m=0 then ()
      	      else lemma_count_take x tl (n-1) (m-1)


let rec map' (#p: 'a -> Type0) (#q: 'b -> Type0) ($f: (x: 'a{p x}) -> (x: 'b{q x})) (l: list 'a {forall x. memP x l ==> p x})
	   : (l: list 'b {forall x. memP x l ==> q x}) =
    match l with
    | [] -> []
    | hd::tl -> f hd::map' f tl


val count: #a:eqtype -> a -> list a -> Tot nat
let rec count #a x = function
  | [] -> 0
  | hd::tl -> if x=hd then 1 + count x tl else count x tl

let rec flatten_doc #a (d: doc a): flat_doc a
  = match d with
  | DAnnotated doc annot -> let l, ann = flatten_doc doc in
    	       	   	   ( match l with
			   | [] -> l, ann
			   | _  -> let na = Annot 0 (max_offset_list l) annot in
                             	  l, na::ann)
  | DString str -> [AStr str], []
  | DIndent idoc ->  
           let ident = "   " in
           let fdoc, fan = flatten_doc idoc in
           let fdoc' = insert_after ANewLine (AStr ident) fdoc in
	   let map_pos (p: nat {p < length fdoc}) = p + count ANewLine (take fdoc p) in
	   let f (x: flat_annot a {memP x fan}): (r: flat_annot a {Annot?.pend r < length fdoc'}) = 
	       let Annot s e a = x in Annot (map_pos s) (admit (); map_pos e) a
	   in fdoc', map' f fan
  | DConcat d1 d2 -> 
    let fd1, a1 = flatten_doc d1 in
    let fd2, a2 = flatten_doc d2 in
    let len = length fd1 in
    let tlen = len + length fd2 in
    let h (x:_{Annot?.pend x < length fd2}): r:_{Annot?.pend r < tlen} = let Annot s e a = x in Annot (s+len) (e+len) a in
    fd1 @ fd2, a1 @ map' h a2
  | DNewLine -> [ANewLine], []
  | DEmpty -> [], []

let flat_doc_to_string (fd: flat_doc _): string
  = String.concat "" (map (function | AStr s -> s | ANewLine -> "\n") (fst fd))

let rec zip (a: list 'a) (b: list 'b): r:_{length r = min (length a) (length b)} =
  match a, b with
  | a_hd::a_tl, b_hd::b_tl -> (a_hd,b_hd)::zip a_tl b_tl
  | _ -> []

let rec mapi' (f: nat -> 'a -> 'b) (l: list 'a) (i: nat)
    : list 'b
    = match l with
    | [] -> []
    | hd::tl -> f i hd::mapi' f tl (i+1)

let mapi f l = mapi' f l 0

let rec mapState (f: 's -> 'a -> 'b & 's) (s0: 's) (l: list 'a): Tot (r: list 'b {length l == length r} * 's) (decreases l)
    = match l with
    | [] -> [], s0
    | hd::tl -> let b, s1 = f s0 hd in 
      	      let tl, sEnd = mapState f s1 tl in b::tl, sEnd

let rec list_cons_tail_lemma l x: Lemma (length l == length (tail (l@[x])))
  = match l with | [] -> () | hd::tl -> list_cons_tail_lemma tl x

let flat_doc_to_annotations (fd: flat_doc 'a): list (position * position * 'a)
  = let fdoc, ann = fd in
    let l, last = mapState (fun (Position c l) -> function
                              | ANewLine -> (Position c l, Position 0 (l+1))
                              | AStr s -> (Position c l, Position (c + String.length s) l)
                           ) (Position 0 0) fdoc in
    let lookup_table_starts = l in
    let lookup_table_ends = tail (l@[last]) in
    list_cons_tail_lemma lookup_table_starts last;
    let h: (i:_{ Annot?.pend i < length lookup_table_starts}) -> _ = fun (Annot s e a) -> (lookup_table_starts `index` s, lookup_table_ends `index` e, a) in
    map' h ann

let doc_to_string (d: doc 'a): string = flat_doc_to_string (flatten_doc d)
let doc_to_annotations #a (d: doc a): list (position * position * a)
  = flat_doc_to_annotations (flatten_doc d)

