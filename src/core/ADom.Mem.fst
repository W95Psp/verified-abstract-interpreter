module ADom.Mem

open Set
open MachineIntegers
open LangDef
open OperationalSemantic
open ADom
open FStar.Tactics.Typeclasses
open ADom.Num

/// From the perspective of $\AbIntImp{}$ statements, an abstract domain
/// for abstract memories is fairly simple.

/// An abstract memory should be equipped with two operations:
/// assignment and assumption.

/// Those are directly related to their syntactic counterpart
/// \fcode{Assume} and \fcode{Assign}.

/// Thus, \fcode{mem_adom} has a field \fcode{assume_} and a field
/// \fcode{assign}.

/// The correctness of these operations are elegantly encoded as
/// refinement types.

///
/// Let us explain the refinement of \fcode{assume_}: let \fcode{mⵌ0}
/// an abstract memory, and \fcode{e} an expression.

/// For every concrete memory \fcode{m0} abstracted by \fcode{mⵌ0},
/// the set of acceptable final memories \fcode{osem_stmt (Assume e)
/// m0} should be abstracted by \fcode{assume_ mⵌ0 e}.

//@replace=[@@@tcinstance] |
class mem_adom 'm = { [@@@tcinstance] ma_adom: adom 'm; ma_mem: squash (ma_adom.c == mem);
  assume_: mⵌ0:'m -> e:expr -> mⵌ1:'m
    {forall (m0: mem{m0 ∈ gamma mⵌ0}). osem_stmt (Assume   e) m0 ⊆ gamma mⵌ1};
  assign: mⵌ0:'m -> v:varname -> e:expr -> mⵌ1:'m
    {forall (m0: mem{m0 ∈ gamma mⵌ0}). osem_stmt (Assign v e) m0 ⊆ gamma mⵌ1}}



