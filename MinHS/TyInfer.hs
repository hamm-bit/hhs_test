module MinHS.TyInfer where

import MinHS.Bwd
import MinHS.Syntax
import qualified MinHS.Subst as S (Subst, SubstSem, substFlex, substRigid, fromList)
import MinHS.TCMonad

import Control.Monad (foldM)
import Data.List (delete)
import Data.Set (Set, notMember, fromList, difference, member, toList)
import Data.Bifunctor (Bifunctor(..), second)
import MinHS.Subst ((=:))

-- | A monomorphic type injected into a type scheme with no quantified
-- type variables.
mono :: Type -> Scheme
mono t = Forall [] t

primOpType :: Op -> Scheme
primOpType Gt   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = mono $ Base Int `Arrow` Base Int
primOpType Fst  = Forall ["a","b"] $ (RigidVar "a" `Prod` RigidVar "b") `Arrow` RigidVar "a"
primOpType Snd  = Forall ["a","b"] $ (RigidVar "a" `Prod` RigidVar "b") `Arrow` RigidVar "b"
primOpType _    = mono $ Base Int `Arrow` (Base Int `Arrow` Base Int)

conType :: Id -> Maybe Scheme
conType "True"  = Just $ mono $ Base Bool
conType "False" = Just $ mono $ Base Bool
conType "()"    = Just $ mono $ Base Unit
conType "Pair"  = Just
                  $ Forall ["a","b"]
                  $ RigidVar "a" `Arrow` (RigidVar "b" `Arrow` (RigidVar "a" `Prod` RigidVar "b"))
conType "Inl"   = Just
                  $ Forall ["a","b"]
                  $ RigidVar "a" `Arrow` (RigidVar "a" `Sum` RigidVar "b")
conType "Inr"   = Just
                  $ Forall ["a","b"]
                  $ RigidVar "b" `Arrow` (RigidVar "a" `Sum` RigidVar "b")
conType _       = Nothing

freshForall :: [Id] -> TC [(Id,Id)]
freshForall xs = mapM (\x -> (,) <$> pure x <*> freshId) xs

-- | Produce fresh flexible variables for a type scheme
specialise :: Scheme -> TC (Type, Suffix)
specialise (Forall xs t) =
  do ids <- freshForall xs
     return (S.substRigid (S.fromList (map (second FlexVar) ids)) t
            , map (flip (,) HOLE . snd) ids)

-- | Extend a typing context with a collection of flexible declarations
extend :: Gamma -> Suffix -> Gamma
extend g [] = g
extend g ((v,d) : ds) = extend (g :< v := d) ds

infer :: Program -> Either TypeError (Program, Gamma)
infer program = runTC $ inferProgram BEmpty program

-- | Perform unification of the given types
unify :: Gamma -> Type -> Type -> TC Gamma

-- Inductivity
unify g (Arrow t1 t2) (Arrow t1' t2') =
  -- NOTE: UNFINISHED
  do
    g' <- unify g t1 t1'
    g'' <- unify g' t2 t2'
    return g''

-- Substitution
unify ( gs :< ((:=) rho (Defn t))) (FlexVar alpha) (FlexVar beta) =
  do 
    gs' <- unify ( gs) (S.substFlex ((=:) rho t) (FlexVar alpha)) (S.substFlex ((=:) rho t) (FlexVar beta))
    return (gs' :< ((:=) rho $Defn t))

-- Skip type declaration
-- Added Definition and Reflexivity
unify ( gs :< ((:=) rho HOLE)) (FlexVar alpha) (FlexVar beta) =
  if (rho == alpha)
    then if (alpha /= beta)
      -- Definition
      then 
        return (extend ( gs) [(alpha, Defn (FlexVar beta))])
      -- Reflexivity
      else
        return ( gs :< ((:=) rho HOLE))
    -- Skip type declaration
    else if (rho /= beta)
      then do 
        g' <- unify ( gs) (FlexVar alpha) (FlexVar beta)
        return (extend g' [(rho, HOLE)])
      else
        -- Fix: added symmetricity
        unify (gs :< ((:=) rho HOLE)) (FlexVar beta) (FlexVar alpha)

-- Skip directional marker
unify ( gs :< Mark) (FlexVar alpha) (FlexVar beta) =
  do
    gs' <- unify ( gs) (FlexVar alpha) (FlexVar beta)
    return (gs' :< Mark)

-- Skip term variable
unify ( gs :< (TermVar x sigma)) (FlexVar alpha) (FlexVar beta) =
  do 
    gs' <- unify ( gs) (FlexVar alpha) (FlexVar beta)
    return (gs' :< (TermVar x sigma))

-- Instantiation
-- symmetricity
unify g ty (FlexVar alpha) = 
  unify g (FlexVar alpha) ty

-- main
unify g (FlexVar alpha) ty =
  do
    g' <- inst g [] alpha ty
    return g'


unify g (Prod t1 t2) (Prod t1' t2') =
  do
    g' <- unify g t1 t1'
    g'' <- unify g' t2 t2'
    return g''

unify g (Sum t1 t2) (Sum t1' t2') =
  do
    g' <- unify g t1 t1'
    g'' <- unify g' t2 t2'
    return g''

-- i.e. Sum Prod Arrow etc..
unify g t1 t2 =
  do
    g' <- unifySingular g t1
    case t2 of
      (Base bt) -> return g'
      (FlexVar id) ->
        error "Unify: GENERAL - flexvar in general should not happen" 
      (RigidVar id) ->
        error "Unify: GENERAL - rigidvar in general should not happen" 
      _ ->
        unifySingular g' t2

-- Product type
unifySingular :: Gamma -> Type -> TC Gamma
unifySingular g t = 
  do
    case t of
      (Base bt) -> return g
      (Arrow ty1 ty2) ->
        -- error "UnifySingular: INTENDED - arrow"
        unify g ty1 ty2
      (Sum ty1 ty2) ->
        unify g ty1 ty2
      (Prod ty1 ty2) ->
        unify g ty1 ty2
      (FlexVar id1) -> 
        error "UnifySingular: GENERAL - flexvar in general should not happen" 
      (RigidVar id) -> 
        error "UnifySingular: GENERAL - rigidvar in general should not happen"
      _ ->
        error "UnifySingular: CRITICAL - type input corrupted"


-- An example of function is actually prim ops
-- i.e. 
--    (+) Int -> Int -> Int , \Gamma \sat (App (App (+) (Num 1)) (Num 1))
--    (Sum) 
-- unify g t1 t2 = 


-- | Instantiation the type variable a with the type t
inst :: Gamma -> Suffix -> Id -> Type -> TC Gamma

-- Dependencies or Skip type declaration
-- Added definition
inst ( gs :< ((:=) beta HOLE)) delta alpha ty =
  do
    if (beta /= alpha) 
      -- Dependencies
      then do
        if (member beta (ffv ty))
        then do
          inst ( gs) ((beta, HOLE) : delta) alpha ty
        else do
          g' <- inst ( gs) delta alpha ty
          return (g' :< ((:=) beta (HOLE)))
      -- Definition
      else if (member alpha (ffv ty))
        then 
          return (gs :< ((:=) beta (HOLE)))
        else do
          gs' <- return (extend ( gs) delta)
          return (gs' :< ((:=) alpha (Defn ty)))

-- Substitution
inst ( gs :< ((:=) beta (Defn ty'))) delta alpha ty =
  do
    gs' <- unify (extend ( gs) delta) (S.substFlex ((=:) beta ty') (FlexVar alpha)) (S.substFlex ((=:) beta ty') ty)
    return (extend gs' [(beta, Defn ty')])

-- Skip directional marker
inst ( gs :< Mark) delta alpha ty =
  do
    gs' <- inst ( gs) delta alpha ty
    return (gs' :< Mark)

-- Skip term variable
inst ( gs :< (TermVar x sigma)) delta alpha ty =
  do 
    gs' <- inst ( gs) delta alpha ty
    return (gs' :< (TermVar x sigma))

inst g zs a t = 
  error ("out-of-bound expression: \n gamma: \n" ++ (gammaIdent g) ++ "\n\n =================== \n\n delta: \n" ++ (suffIdent zs) ++ "\n\n =================== \n\n to-be-instantiated alpha: \n" ++ a ++ "\n\n =================== \n\n to-be-substituted type: \n" ++ (fst $ tyIdent t))


gen :: Gamma -> Exp -> TC (Scheme, Gamma)
gen g e =
  do
    (ty, g2') <- inferExp (g :< Mark) e
    (g2, delta) <- return (dropWithDelim g2' Mark [])
    sigma <- return (genScheme (reverse delta) ty [])
    return (sigma, g2)

-- Helper for scheme generation
genScheme :: [Entry] -> Type -> [Id] -> Scheme

-- Base case
genScheme [] ty betas = Forall betas ty

-- Defn case
genScheme (((:=) alpha d') : xs) ty betas =
  case d' of
    (Defn ty') ->
      let tyNew = S.substFlex ((=:) alpha ty') ty
        in genScheme ( xs) tyNew betas
    _ ->
      let tyNew = S.substFlex ((=:) alpha (RigidVar alpha)) ty
        in genScheme ( xs) tyNew (alpha:betas)

-- Calm-the-compiler-down case
genScheme entries ty betas =
  error "genScheme: [Entries] includes TermVars"

-- Helper for collecting a list of variables off a backward list
-- With respect until a delimiter (Entry)
dropWithDelim :: Gamma -> Entry -> [Entry] -> (Gamma, [Entry])

-- Calm-the-compiler-down case
dropWithDelim BEmpty delim delta =
  error "dropWithDelim: empty Gamma input"

-- Recursive case
dropWithDelim (gs :< g) delim delta =
  if (g == delim)
    then (gs, delta)
    else dropWithDelim gs delim (g : delta)

inferProgram :: Gamma -> Program -> TC (Program, Gamma)
inferProgram g (SBind x _ e) =
  do
    (sigma_out, g') <- gen g e
    return (SBind x (Just sigma_out) e, g')

inferExp :: Gamma -> Exp -> TC (Type, Gamma)

-- =================== Type cases: 
-- Variable
inferExp g (Var x) =
  do
    result <- lookupIdList g x
    -- error (gammaIdent g)
    case result of
      (Just alpha_sch) -> do
        -- Valid variable
        (ty', suff) <- specialise alpha_sch
        return (ty', (extend g suff))
      _ ->
        error "InferExp: Variable - variable not in scope"

-- Integer
inferExp g (Num n) = return (Base Int, g)

-- Constructor Type
inferExp g (Con k) =
  do
    alpha_sch <- return (conType k)
    case alpha_sch of
      Just alpha_val_sch -> do
        (ty, suff) <- specialise alpha_val_sch 
        return (ty, (extend g suff))
      _ ->
        error "InferExp: ConType - invalid constructor type k"

-- Primop Type
inferExp g (Prim o) =
  do
    alpha_sch <- return (primOpType o)
    (ty, suff) <- specialise alpha_sch
    return (ty, (extend g suff))

-- Apply operator
inferExp g1 (App e1 e2) =
  do
    alpha <- freshId
    (ty1, g2) <- inferExp g1 e1
    (ty2, g3) <- inferExp g2 e2
    g4 <- unify (g3 :< ((:=) alpha HOLE)) ty1 (Arrow ty2 (FlexVar alpha))
    return ((FlexVar alpha), g4)

-- If then else expression
inferExp g1 (If e e1 e2) =
  do
    (ty, g2) <- inferExp g1 e
    g3 <- unify g2 ty (Base Bool)
    (ty1, g4) <- inferExp g3 e1
    (ty2, g5) <- inferExp g4 e2
    g6 <- unify g5 ty1 ty2 
    return (ty1, g6)

-- Case expression
inferExp g1 (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) =
  -- NOTE: UNFINISHED
  -- TODO: generate fresh alpha and beta for free var decl
  --       then handle sum expression
  do
    (ty, g2) <- inferExp g1 e
    alpha <- freshId
    beta <- freshId
    alpha_sch <- return (mono (FlexVar alpha))
    beta_sch <- return (mono (FlexVar beta))
    g3 <- 
      unify ((g2 :< ((:=) alpha HOLE)) :< ((:=) beta HOLE)) ty (Sum (FlexVar alpha) (FlexVar beta))

    (ty1, g4') <-
      inferExp (g3 :< (TermVar x alpha_sch)) e1
    (g4, delta) <- return (dropWithDelim g4' (TermVar x alpha_sch) [])

    (ty2, g5') <-
      inferExp ((g4 <>< delta) :< (TermVar y beta_sch)) e2
    (g5, delta') <- return (dropWithDelim g5' (TermVar y beta_sch) [])

    g6 <- unify (g5 <>< delta') ty1 ty2
    return (ty1, g6)

inferExp g1 (Case e _) = typeError MalformedAlternatives

-- Recfun
inferExp g1 (Recfun (MBind f x e)) =
  do
    alpha <- freshId
    beta <- freshId
    alpha_sch <- return (mono (FlexVar alpha))
    beta_sch <- return (mono (FlexVar beta))
    g1' <- return (extend g1 [(alpha, HOLE), (beta, HOLE)])

    (ty, g2') <-
      inferExp ((g1' :< (TermVar x alpha_sch)) :< (TermVar f beta_sch)) e
    (g2'', delta) <- 
      return (dropWithDelim g2' (TermVar f beta_sch) [])
    (g2, _) <-
      return (dropWithDelim g2'' (TermVar x alpha_sch) [])

    g3 <- unify (g2 <>< delta) (FlexVar beta) (Arrow (FlexVar alpha) ty) 
    return ((FlexVar beta), g3)

-- Let expression
inferExp g1 (Let [(SBind x sigma e1)] e2) =
  -- NOTE: UNFINISHED
  do
    (sigma', g2) <- gen g1 e1
    (ty, g3') <-
      inferExp (g2 :< (TermVar x sigma')) e2
    (g3, delta) <- return (dropWithDelim g3' (TermVar x sigma') [])
    return (ty, g3 <>< delta)

inferExp g e = error "implement me!"

-- Helper function starts

-- lookup entries
lookupType :: Gamma -> Id -> Type
lookupType ( gs :< g) a =
    case g of
      TermVar id1 (Forall _ t) ->
        t
      (:=) id2 (Defn t') ->
        t'
      _ ->
        if (gs == BEmpty)
          then (FlexVar a)
          else lookupType ( gs) a      

-- scheme only, dedicated helper for Infer: VAR
lookupIdList :: Gamma -> Id -> TC (Maybe Scheme)
lookupIdList ( gs :< g) x =
  do
    case g of
      TermVar id1 (Forall ids ty') ->
        if (id1 == x)
          then return (Just (Forall ids ty'))
          else if gs == BEmpty
            then return $ Nothing
            else lookupIdList gs x
      _ ->
        if (gs == BEmpty)
          then return $ Nothing
          else lookupIdList gs x

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


-- Debug function for suffix unwrapping
suffIdent :: Suffix -> String
suffIdent [] = "_suffEnd"
suffIdent ((id, (Defn ty)) : []) = 
  ("(id: " ++ id ++ " ; ty: " ++ (fst (tyIdent ty)) ++ " ) || _suffEnd")

suffIdent ((id, HOLE) : []) =
  ("(id: " ++ id ++ " ; ty: HOLE" {- ++ (fst (tyIdent ty))-} ++ " ) || _suffEnd")

suffIdent ((id, (Defn ty)) : suffs) =
  ("(id: " ++ id ++ " ; ty: " ++ (fst (tyIdent ty)) ++ " ) || " ++ suffIdent (suffs))

suffIdent ((id, HOLE) : suffs) =
  ("(id: " ++ id ++ " ; ty: HOLE" {- ++ (fst (tyIdent ty))-} ++ " ) || " ++ suffIdent (suffs))


-- Debug function for delta unwrapping
deltaIdent :: [Entry] -> String
deltaIdent [] = "_DeltaEnd"
deltaIdent (((:=) id (Defn ty)) : deltas) = 
  ("(id: " ++ id ++ " ; ty: " ++ (fst (tyIdent ty)) ++ ") || \n" ++ (deltaIdent deltas))

deltaIdent (((:=) id HOLE) : deltas) =
  ("(id: " ++ id ++ " ; ty: HOLE) || \n" ++ (deltaIdent deltas))

deltaIdent ((TermVar id (Forall ids ty)) : deltas) =
  ("(id: " ++ id ++ " ; scheme: " ++ "[" ++ (unwords ids) ++ "] ; ty: " ++ (fst (tyIdent ty)) ++ " ) || \n" ++ (deltaIdent deltas))

deltaIdent (Mark : deltas) =
  ("(Mark ) || \n" ++ (deltaIdent deltas))


-- Debug function for gamma debugging
gammaIdent :: Gamma -> String
gammaIdent (BEmpty) = ("NOTE: backward list printing starts from the end\n_GEnd")
gammaIdent (gs :< ((:=) id (Defn ty))) = 
  ((gammaIdent gs) ++ "\n (id: " ++ id ++ " ; ty: " ++ (fst (tyIdent ty)) ++ " ) || ")

gammaIdent (gs :< ((:=) id HOLE)) = 
  ((gammaIdent gs) ++ "\n (id: " ++ id ++ " ; ty: HOLE" {- ++ (fst (tyIdent ty))-} ++ " ) || ")

gammaIdent (gs :< (TermVar id (Forall ids ty))) = 
  ((gammaIdent gs) ++ "\n (id: " ++ id ++ " ; scheme: " ++ "[" ++ (unwords ids) ++ "] ; ty: " ++ (fst (tyIdent ty)) ++ " ) || ")

gammaIdent (gs :< Mark) = 
  ((gammaIdent gs) ++ "\n (Mark" {- ++ (fst (tyIdent ty))-} ++ " ) || ")


-- Debug function for scheme debugging
sigmaIdent :: Scheme -> String
sigmaIdent (Forall ids ty) =
  ("ids: [" ++ (unwords ids) ++ "] || ty: " ++ (fst $ tyIdent ty))

