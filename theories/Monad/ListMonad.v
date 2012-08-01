Require Import Monad.
Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Instance Monad_list : Monad list :=
{ ret := fun _ v => v :: nil
; bind := fix recur _ c1 _ c2 :=
  match c1 with 
    | nil => nil
    | a :: b => c2 a ++ recur _ b _ c2
  end
}.

Instance Zero_list : Zero list :=
{ zero := @nil }.

Definition listT (m : Type -> Type) : Type -> Type := 
  fun x => m (list x).

Instance Monad_listT m (M : Monad m) : Monad (listT m) :=
{ ret := fun _ x => @ret m M _ (x :: nil)
; bind := fun _ c1 _ c2 =>
  @bind _ M _ c1 _ (fix recur vs :=
    match vs with
      | nil => @ret _ M _ nil
      | v :: vs => Monad.liftM2 M (@app _) (c2 v) (recur vs)
    end)
}.

Instance Zero_optionT m (M : Monad m) : Zero (listT m) :=
{ zero := fun _ => @ret _ M _ nil }.
