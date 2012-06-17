Class Monad (m : Type -> Type) : Type :=
{ ret  : forall t, t -> m t
; bind : forall t u, m t -> (t -> m u) -> m u
; Bind_Ret : forall t (v : t) cmd, bind (ret t) cmd = cmd t
; Ret_Bind : 
; Bind_assoc : 
}.