

Section lazy_list.
  Variable T : Type.

  Inductive llist : Type :=
  | lnil : llist
  | lcons : T -> (unit -> llist) -> llist.

End lazy_list.