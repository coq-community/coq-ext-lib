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
  { lift := fun _ c => bind c (fun x => ret (ret x))
  }.
End Trans.

