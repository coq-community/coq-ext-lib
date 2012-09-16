Require Import Monad.

Global Instance Monad_option : Monad option :=
{ ret  := @Some 
; bind := fun _ c1 _ c2 => match c1 with 
                             | None => None
                             | Some v => c2 v
                           end 
}.

Global Instance Zero_option : Zero option :=
{ zero := @None }.

Section Trans.
  Variable m : Type -> Type.

  Definition optionT : Type -> Type := 
    fun x => m (option x).

  Variable M : Monad m.

  Global Instance Monad_optionT : Monad optionT :=
  { ret := fun _ x => @ret m M _ (Some x)
  ; bind := fun _ c1 _ c2 =>
    @bind _ M _ c1 _ (fun c1 =>
      match c1 with
        | None => @ret _ M _ None
        | Some v => c2 v
      end)
  }.

  Global Instance Zero_optionT : Zero optionT :=
  { zero := fun _ => @ret _ M _ None }.

  Global Instance MonadT_optionT : MonadT optionT m :=
  { lift := fun _ c => bind c (fun x => ret (ret x)) }.

  Global Instance State_optionT {T} (SM : State T m) : State T optionT :=
  { get := lift get 
  ; put := fun v => lift (put v)
  }.

  Global Instance Reader_optionT {T} (SM : Reader T m) : Reader T optionT :=
  { ask := lift ask
  ; local := fun v T cmd => local (Reader := SM) v cmd 
  }.

End Trans.
