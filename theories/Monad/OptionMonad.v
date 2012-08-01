Require Import Monad.

Instance Monad_option : Monad option :=
{ ret  := @Some 
; bind := fun _ c1 _ c2 => match c1 with 
                             | None => None
                             | Some v => c2 v
                           end 
}.

Instance Zero_option : Zero option :=
{ zero := @None }.

Definition optionT (m : Type -> Type) : Type -> Type := 
  fun x => m (option x).

Instance Monad_optionT m (M : Monad m) : Monad (optionT m) :=
{ ret := fun _ x => @ret m M _ (Some x)
; bind := fun _ c1 _ c2 =>
  @bind _ M _ c1 _ (fun c1 =>
    match c1 with
      | None => @ret _ M _ None
      | Some v => c2 v
    end)
}.

Instance Zero_optionT m (M : Monad m) : Zero (optionT m) :=
{ zero := fun _ => @ret _ M _ None }.


