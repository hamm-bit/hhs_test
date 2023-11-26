module MinHS.Subst ( Subst
                   , SubstSem
                   , substFlex
                   , substRigid
                   , fromList
                   , (=:)
                   ) where

import MinHS.Syntax
newtype Subst = Subst [(Id, Type)]

instance Semigroup Subst where
  Subst a <> Subst b = Subst $ a ++ b

instance Monoid Subst where
  mempty = Subst []
  mappend = (<>)

class SubstSem a where
  -- | Perform substitution on rigid type variables.
  substRigid :: Subst -> a -> a
  -- | Perform substitution on flexible type variables.
  substFlex  :: Subst -> a -> a

-- | A substitution semantics for types.
instance SubstSem Type where
  -- | Used for specialisation
  substRigid s (Sum a b)   = Sum (substRigid s a) (substRigid s b)
  substRigid s (Prod a b)  = Prod (substRigid s a) (substRigid s b)
  substRigid s (Arrow a b) = Arrow (substRigid s a) (substRigid s b)
  substRigid (Subst s) (RigidVar x) | Just t <- lookup x s = substRigid (Subst s) t
                                  | otherwise            = RigidVar x
  substRigid _         t   = t

  -- | Used for unification.
  substFlex s (Sum a b)   = Sum (substFlex s a) (substFlex s b)
  substFlex s (Prod a b)  = Prod (substFlex s a) (substFlex s b)
  substFlex s (Arrow a b) = Arrow (substFlex s a) (substFlex s b)
  -- substFlex (Subst s) (FlexVar x) = 
  --   case (lookup x s) of
  --     Just t -> substFlex (Subst s) t
  --     _ -> FlexVar x
  -- substFlex (Subst s) (FlexVar x) | Just t <- lookup x s = substFlex (Subst s) t
  --                               | otherwise            = FlexVar x
  substFlex (Subst s) (FlexVar x) = 
                                    
    case (lookup x s) of
      Just t -> 
        if (x == "'f1" && (substId (Subst s)) == "'g1")
          then 
              error (substIdent (Subst s))
              -- error (fst $ tyIdent (t))
          else substFlex (Subst s) t
      _ -> FlexVar x
  substFlex _         t   = t

-- | A substitution semantics for expressions
instance SubstSem Exp where
  substRigid _ e = e
  -- substRigid _ e@(Var _) = e
  -- substRigid _ e@(Prim _) = e
  -- substRigid _ e@(Con _) = e
  -- substRigid _ e@(Num _) = e
  -- substRigid s (App e1 e2) = App (substRigid e1) (substRigid e2)
  substFlex _ e = e

(=:) :: Id -> Type -> Subst
x =: t = Subst [(x,t)]

fromList :: [(Id,Type)] -> Subst
fromList = Subst

-- Debug Function for type identification
tyIdent :: Type -> (String, Type)
tyIdent ty =
  case ty of
    Arrow t1 t2 ->
      let (str1, ty1) = tyIdent t1
          (str2, ty2) = tyIdent t2
      in ("tyIdent: Arrow: (\n\t" ++ str1 ++ "\n\t" ++ str2 ++ "\n)", ty)
    Prod t1 t2 ->
      let (str1, ty1) = tyIdent t1
          (str2, ty2) = tyIdent t2
      in ("tyIdent: Prod: (\n\t" ++ str1 ++ "\n\t" ++ str2 ++ "\n)", ty)
      -- error "tyIdent: Prod"
      -- tyIdent t2
    Sum _ _ ->
      error "tyIdent: Sum"
    Base ty1 ->
      if (ty1 == Unit)
        then ("tyIdent: Base Unit", ty)
        else if (ty1 == Bool)
            then ("tyIdent: Base Bool", ty)
            else ("tyIdent: Base Int", ty)
    FlexVar id ->
      (("tyIdent: FlexVar " ++ id), ty)
      -- error ("tyIdent: FlexVar " ++ id)
    RigidVar id ->
      (("tyIdent: FlexVar " ++ id), ty)
      -- error ("tyIdent: RigidVar " ++ id)
    _ ->
      error ("tyIdent: CRITICAL TYPE FAILURE")


substId :: Subst -> Id
substId (Subst [(id, ty)]) = id

substIdent :: Subst -> String
-- substIdent (Subst []) = "_substEnd"
substIdent (Subst [(id, ty)]) =
  ("\n (id: " ++ id ++ " ; ty: " ++ (fst $ tyIdent ty) ++ " ) || " {-++ substIdent s-})