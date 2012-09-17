Require Import Monad.

Section except.
  Variable T : Type.
  
  Global Instance Monad_either : Monad (sum T) :=
  { ret  := fun _ v => inr v
  ; bind := fun _ c1 _ c2 => match c1 with 
                               | inl v => inl v
                               | inr v => c2 v
                             end 
  }.

  Global Instance Exception_either : MonadExc T (sum T) :=
  { raise := fun v _ => inl v
  ; catch := fun _ c h => match c with
                            | inl v => h v
                            | x => x
                          end
  }.

  Variable m : Type -> Type.

  Definition eitherT : Type -> Type := 
    fun x => m (sum T x).

  Variable M : Monad m.

  Global Instance Monad_eitherT : Monad eitherT :=
  { ret := fun _ x => @ret m M _ (inr x)
  ; bind := fun _ c1 _ c2 =>
    @bind _ M _ c1 _ (fun c1 =>
      match c1 with
        | inl x => @ret _ M _ (inl x)
        | inr v => c2 v
      end)
  }.

  Global Instance Exception_eitherT : MonadExc T eitherT :=
  { raise := fun v _ => @ret _ M _ (inl v)
  ; catch := fun _ c h =>
    bind (Monad := M) c (fun e_v =>
      match e_v with
        | inl x => h x
        | inr x => ret (inr x)
      end)
  }.

  Global Instance MonadT_eitherT : MonadT eitherT m :=
  { lift := fun _ c => bind c (fun x => ret (ret x)) }.

  Global Instance State_eitherT {T} (SM : State T m) : State T eitherT :=
  { get := lift get 
  ; put := fun v => lift (put v)
  }.

  Global Instance Reader_eitherT {T} (SM : Reader T m) : Reader T eitherT :=
  { ask := lift ask
  ; local := fun v T cmd => local (Reader := SM) v cmd 
  }.

End except.
