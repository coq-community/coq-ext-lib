Require Import Monad.
Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance Monad_list : Monad list :=
{ ret := fun _ v => v :: nil
; bind := fix recur _ c1 _ c2 :=
  match c1 with 
    | nil => nil
    | a :: b => c2 a ++ recur _ b _ c2
  end
}.

Global Instance Zero_list : Zero list :=
{ zero := @nil }.

Section trans.
  Variable m : Type -> Type.
  
  Definition listT : Type -> Type := 
    fun x => m (list x).

  Context {M : Monad m}.
  
  Global Instance Monad_listT : Monad listT :=
  { ret := fun _ x => @ret m M _ (x :: nil)
  ; bind := fun _ c1 _ c2 =>
    @bind _ M _ c1 _ (fix recur vs :=
      match vs with
        | nil => @ret _ M _ nil
        | v :: vs => Monad.liftM2 (@app _) (c2 v) (recur vs)
      end)
  }.
  
  Global Instance MonadT_listT : MonadT listT m :=
  { lift := fun _ cmd => bind cmd (fun x => ret (x :: nil)) }.

  Global Instance Zero_listT : Zero listT :=
  { zero := fun _ => @ret _ M _ nil }.

  Global Instance State_listT {T} (SM : State T m) : State T listT :=
  { get := lift get
  ; put := fun v => lift (put v)
  }.

  Global Instance Reader_listT {T} (RM : Reader T m) : Reader T listT :=
  { ask   := lift ask
  ; local := fun v _ cmd => local (Reader := RM) v cmd
  }.
End trans.