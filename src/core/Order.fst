module Order
open Prop

/// A partial order is a relation that obeys some laws: in
/// \gls{fstar}, such constraints are trivially encoded as
/// \emph{refinements}.

/// Refinements filters the inhabitants of a type: below, the type
/// \fcode{order} is inhabited by binary predicates that are
/// reflexive, transitive and antisymetric.

/// A value \fcode{v} of type \fcode{order int} witness the proof that
/// \fcode{v} is reflective, transitive and antisymetric.

//@regexp=⊑(?!\))|!\twocharwidth{\scalebox{0.8}[0.95]{$\sqsubseteq$}}!
let refl    ((⊑):'a->'a->bool): prop = forall   x. x⊑x
//@regexp=⊑(?!\))|!\twocharwidth{\scalebox{0.8}[0.95]{$\sqsubseteq$}}!
let antisym ((⊑):'a->'a->bool): prop = forall x y. (x⊑y /\ y⊑x) ==> x==y
//@regexp=⊑(?!\))|!\twocharwidth{\scalebox{0.8}[0.95]{$\sqsubseteq$}}!
let trans ((⊑):'a->'a->bool): prop = forall x y z. (x⊑y /\ y⊑z) ==> x⊑z

type order 'a = f:('a->'a->bool)  {refl f /\ trans f /\ antisym f}
