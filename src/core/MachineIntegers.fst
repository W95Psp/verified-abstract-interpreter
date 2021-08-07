module MachineIntegers

open FStar.Mul
module L = FStar.List.Tot

//!open NumTC

//@hide
unfold let size_int_m = 256
//@hide
unfold let max_int_m = 127
//@hide
unfold let min_int_m = -max_int_m

// unfold let dsize_int_m = 128
// let _ = assert (dsize_int_m = size_int_m/2 /\ max_int_m = dsize_int_m - 1)

//@hide
unfold let inbounds x = x >= min_int_m && x <= max_int_m
//@hide
type int_m = x: int {inbounds x}

//@hide
let as_int_m (v: int): int_m = (v+max_int_m)%(size_int_m-1)-max_int_m

//@hide
let div_m (x: int_m) (y: int_m{y <> 0}): int_m = as_int_m (x / y)

//@hide
let min x y = if x <= y then x else y
//@hide
let max x y = if x <= y then y else x

open NumTC

//@hide
instance int_m_arith: num int_m = let h f = fun x y -> as_int_m (f x y) in
  { n_add = h Prims.op_Addition; n_sub = h Prims.op_Subtraction
  ; n_mul = h Mul.op_Star; n_eq = h int_arith.n_eq; n_lt = h int_arith.n_lt
  ; n_and = h int_arith.n_and; n_or = h int_arith.n_or }

//@hide
let add_m_comm (a b:int_m): Lemma (a+b == b+a) [SMTPat (a+b)] = ()
//@hide
let v (v: int_m): int_m = v

