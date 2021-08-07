module MinMaxLemma
//Since these lemmas take time to be discharged by Z3, we define them
//in a separate module, so that we can cache them, and avoid spending a minute or so waiting for these each time we typecheck Intervals.
open FStar.Mul

//@hide=but shown as comment // not important
let _ = 0

#push-options "--z3rlimit 8 --z3rlimit_factor 64"
let lemma_min (a b c d: int) (x: int{a <= x /\ x <= b}) (y: int{c <= y /\ y <= d})
  : Lemma (x*y >= a*c \/ x*y >= a*d \/ x*y >= b*c \/ x*y >= b*d) = ()
#pop-options

unfold let in_btw (x: int) (l u: int) = l <= u /\ x >= l /\ x <= u

//TODO=explain requires / ensures
open MachineIntegers
#push-options "--z3rlimit 8"
let lemma_mul (a b c d x y: int)
  : Lemma (requires in_btw x a b /\ in_btw y c d)
    (ensures x*y >= (a*c) `min` (a*d) `min` (b*c) `min` (b*d)
           /\ x*y <= (a*c) `max` (a*d) `max` (b*c) `max` (b*d))
    [SMTPat (x*y); SMTPat (a*c); SMTPat (b * d)]
  = lemma_min a b c d x y; lemma_min (-b) (-a) c d (-x) y
#pop-options


