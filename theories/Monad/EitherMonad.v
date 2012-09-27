Require Import Monad.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Open Local Scope monad_scope.

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
  { raise := fun _ v => inl v
  ; catch := fun _ c h => match c with
                            | inl v => h v
                            | x => x
                          end
  }.

  Variable m : Type -> Type.

  Inductive eitherT A := mkEitherT { unEitherT : m (sum T A) }.

  Variable M : Monad m.

  Global Instance Monad_eitherT : Monad eitherT :=
  { ret := fun _ x => mkEitherT (ret (inr x))
  ; bind := fun _ c _ f => mkEitherT (
      xM <- unEitherT c ;;
      match xM with
      | inl x => ret (inl x)
      | inr x => unEitherT (f x)
      end
    )
  }.

  Global Instance Exception_eitherT : MonadExc T eitherT :=
  { raise := fun _ v => mkEitherT (ret (inl v))
  ; catch := fun _ c h => mkEitherT (
      xM <- unEitherT c ;;
      match xM with
        | inl x => unEitherT (h x)
        | inr x => ret (inr x)
      end
    )
  }.

  Global Instance MonadT_eitherT : MonadT eitherT m :=
  { lift := fun _ c => mkEitherT (liftM ret c) }.

  Global Instance State_eitherT {T} (SM : State T m) : State T eitherT :=
  { get := lift get
  ; put := fun v => lift (put v)
  }.

  Global Instance Reader_eitherT {T} (SM : Reader T m) : Reader T eitherT :=
  { ask := lift ask
  ; local := fun f T cmd => mkEitherT (local f (unEitherT cmd))
  }.

  Global Instance MonadPlus_eitherT : MonadPlus eitherT :=
  { mplus _A _B mA mB := mkEitherT (
      x <- unEitherT mA ;;
      match x with
      | inl _ =>
          y <- unEitherT mB ;;
          match y with
          | inl t => ret (inl t)
          | inr b => ret (inr (inr b))
          end
      | inr a => ret (inr (inl a))
      end
    )
  }.

End except.
