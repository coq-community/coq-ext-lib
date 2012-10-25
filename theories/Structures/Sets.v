

Section Sets.
  Variable S : Type.
  Context {T : Type}.

  Class DSet (R : T -> T -> Prop) : Type :=
  { contains   : T -> S -> bool
  ; empty      : S
  ; singleton  : T -> S 
  ; union      : S -> S -> S
  ; intersect  : S -> S -> S
  ; difference : S -> S -> S
  ; subset     : S -> S -> bool
    (** point-wise **)
  ; add        : T -> S -> S
  ; remove     : T -> S -> S
  }.

  Variable R : T -> T -> Prop.
  Variable DS : DSet R.

  Class CSep_Laws : Type :=
  { empty_not_contains : forall t, contains t empty = false
  ; singleton_contains : forall t u, contains t (singleton u) = true <-> R t u
  ; union_contains     : forall s s',
    forall x, orb (contains x s) (contains x s') = contains x (union s s')
  ; intersect_contains : forall s s',
    forall x, andb (contains x s) (contains x s') = contains x (intersect s s')
  ; difference_contains : forall s s',
    forall x, andb (contains x s) (negb (contains x s')) = contains x (difference s s')
  ; subset_contains    : forall s s', subset s s' = true <-> 
    (forall x, contains x s = true -> contains x s' = true)
  ; add_contains       : forall s x, contains x (add x s) = true
  ; add_contains_not   : forall s x y, ~R x y -> contains x (add y s) = contains x s 
  ; remove_contains    : forall s x, contains x (remove x s) = false
  ; remove_contains_not : forall s x y, ~R x y -> contains x (remove y s) = contains x s
  }.

End Sets.
