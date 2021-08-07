module Fixpoint

open Order
open Prop

/// However, even if the function from which we want to get a
/// prefixpoint is decreasing, this is not a guarantee for
/// termination.

/// The type \fcode{measure} below associates an order to a measure
/// that ensures termination.

/// Such a measure cannot be implemented for a lattice that has
/// infinite decreasing or increasing chains.

/// We also require a maximum for this measure, so that we can reverse
/// the measure easily in the context of postfixpoints iteration.

//@replace=noeq |
noeq type measure #a (ord: a -> a -> bool) 
  = { f: f: (a -> nat) {forall x y. x `ord` y ==> x =!= y ==> f x < f y}
    ; max: (max: nat {forall x. f x < max}) }

//@hide
private let trans ((⊕):'a->'a->prop) = forall x y z. (x ⊕ y /\ y ⊕ z) ==> x ⊕ z

/// Let us focus on \fcode{prefixpoint}: given an order \fcode{⊑} with
/// its measure \fcode{m}, it iterates a decreasing function \fcode{f},
/// starting from a value \fcode{x}.

/// The argument \fcode{r} is a binary relation which is required to
/// hold for every couple \fcode{(x, f x)}.

/// \fcode{r} is also required to be transitive, so that morally

/// \fcode{r x (fⁿ x)} holds.

/// \fcode{prefixpoint} is specified to return a prefixpoint
/// \fcode{y}, that is, with \fcode{r x y} holding.

//@regexp'=`o`-->>⊑
//@regexp=\bo\b|(⊑)
let rec prefixpoint (o: order 'a) (m: measure o)
  (r: 'a->'a->prop {trans r}) (f: 'a->'a {∀e. f e `o` e /\ r e (f e)}) (x:'a) 
  : Tot (y: 'a{r x y /\ f y == y /\ y `o` x}) (decreases (m.f x))
  = let x' = f x in if x `o` x' then x else prefixpoint o m r f x'

//@regexp'=`o`-->>⊑
//@regexp=\bo\b|(⊑)
//@hide-because-shown-at-module=AbstractSemantic
let rec postfixpoint (o: order 'a) (m: measure o)
  (f: 'a -> 'a {forall x. x `o` f x}) (x: 'a)
  : Tot (y: 'a{f y == y /\ o x y}) (decreases (m.max - m.f x))
  = let x' = f x in if x' `o` x then x else postfixpoint o m f x'

