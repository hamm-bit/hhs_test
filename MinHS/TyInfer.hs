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

-- Reflexitivity
-- unify g (FlexVar a) (FlexVar a) = return g

-- Inductivity
unify g (Arrow t1 t2) (Arrow t1' t2') =
  -- NOTE: UNFINISHED
  do
    g' <- unify g t1 t1'
    g'' <- unify g' t2 t2'
    return g''


-- Definition
-- And Reflexivity
{-
unify ( gs :< ((:=) alpha HOLE)) (FlexVar alpha) (FlexVar beta) =
  -- NOTE: UNFINISHED
  do
    if (alpha /= beta)
      then return extend ( gs) [(alpha, Defn (FlexVar beta))]
      else return g
    -- g' <- extend g [alpha]
-}

-- Substitution
unify ( gs :< ((:=) rho (Defn t))) (FlexVar alpha) (FlexVar beta) =
  do unify ( gs) (S.substFlex ((=:) rho t) (FlexVar alpha)) (S.substFlex ((=:) rho t) (FlexVar beta))

-- Skip type declaration
-- Added Definition and Reflexivity
unify ( gs :< ((:=) rho HOLE)) (FlexVar alpha) (FlexVar beta) =
  if (rho == alpha)
    then if (alpha /= beta)
      -- Definition
      then 
        return (extend ( gs) [(alpha, Defn (FlexVar beta))])
        -- return (gs :< ((:=) alpha (Defn (FlexVar beta))))
        -- return gs'
      -- Reflexivity
      else
        return ( gs :< ((:=) rho HOLE))
    -- Skip type declaration
    else if (rho /= beta)
      then do 
        g' <- unify ( gs) (FlexVar alpha) (FlexVar beta)
        return (extend g' [(rho, HOLE)])
      else 
        error "Unify: SkipTy - extended rho overlaps with one of substituting alpha/beta"
        -- return UnifyFailed ( gs :< ((:=) rho HOLE)) (FlexVar alpha) (FlexVar beta)

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
unify g (FlexVar alpha) ty =
  -- NOTE: IMPLEMENT INSTANTIATION
  do
    g' <- inst g [] alpha ty
    return g'

unify g t1 t2 = error "implement me!"

-- An example of function is actually prim ops
-- i.e. 
--    (+) Int -> Int -> Int , \Gamma \sat (App (App (+) (Num 1)) (Num 1))
--    (Sum) 
-- unify g t1 t2 = 



-- | Instantiation the type variable a with the type t
inst :: Gamma -> Suffix -> Id -> Type -> TC Gamma

-- Definition
{-
inst ( gs :< ((:=) alpha HOLE)) delta alpha ty =
  do
    idSet <- ffv ty
    if (member alpha idSet)
      then error "Inst: DEFN - redefining an already instantiated element"
      else do
        gs' <- extend ( gs) delta
        return (gs' :< ((:=) alpha HOLE))
-}

-- Dependencies or Skip type declaration
-- Added definition
inst ( gs :< ((:=) beta HOLE)) delta alpha ty =
  -- idSet = ffv ty
  if (beta /= alpha) 
    -- Dependencies
    then if (member beta (ffv ty))
      then inst ( gs) ((beta, HOLE) : delta) alpha ty
      else do
        g' <- inst ( gs) delta alpha ty
        return (extend g' [(beta, HOLE)])
    -- Definition
    else if (member alpha (ffv ty))
      then 
        error "Inst: DEFN - redefining an already instantiated element"
        -- return InstFailed delta alpha ty
      else do
        gs' <- return (extend ( gs) delta)
        return (gs' :< ((:=) alpha HOLE))

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

inst g zs a t = error "implement me!"

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

-- Delimiter hit, delimiter is rejected
-- dropWithDelim (gs :< ent) ent delta = (gs, delta)

-- Calm-the-compiler-down case
dropWithDelim BEmpty ent delta =
  error "dropWithDelim: empty Gamma input"

-- Recursive case
dropWithDelim (gs :< g) ent delta =
  case g of
    ent ->
      (gs, delta)
    _ ->
      dropWithDelim gs ent (g : delta)

inferProgram :: Gamma -> Program -> TC (Program, Gamma)
inferProgram g (SBind x _ e) =
  do 
    (t, g') <- inferExp g e
    return (SBind x (Just $ Forall [] t) e, g')
-- error "implement me!"

inferExp :: Gamma -> Exp -> TC (Type, Gamma)

-- =================== Type cases: 
-- Variable
inferExp g (Var x) =
  -- NOTE: UNFINISHED
  -- ADDITIONAL NOTE: I DONT KNOW WHAT I AM DOING
  do
    ty <- return (lookupType g x)
    if (ty /= (FlexVar x))
    then do alpha_sch <- lookupIdList g ty
            (ty', suff) <- specialise alpha_sch
            return (ty', (extend g suff))
    else error "InferExp: Variable - variable not in scope"

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
  -- NOTE: UNFINISHED
  -- TODO: generate fresh alpha for free var decl
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
    (g5, delta') <- return (dropWithDelim g5' (TermVar x beta_sch) [])

    g6 <- unify (g5 <>< delta') ty1 ty2
    return (ty1, g6)

inferExp g1 (Case e _) = typeError MalformedAlternatives

-- Recfun
inferExp g1 (Recfun (MBind f x e)) =
  -- NOTE: UNFINISHED
  -- TODO: generate fresh alpha and beta for free var decl
  --       additionally term var (x.alpha), (f.beta) for
  --       substitution
  -- ADDITIONAL NOTE: I DONT KNOW WHAT THE FELLTHROUGH IM DOING
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
      return (dropWithDelim g2'' (TermVar f alpha_sch) [])

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

-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives


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

lookupIdList :: Gamma -> Type -> TC Scheme
lookupIdList ( gs :< g) ty =
  do
    case g of
      TermVar id1 (Forall ids ty') ->
        if (ty' == ty)
          then return (Forall ids ty')
          else if (gs == BEmpty)
            then return (Forall [] ty)
            else lookupIdList ( gs) ty
      _ ->
        if (gs == BEmpty)
          then return (Forall [] ty)
          else lookupIdList ( gs) ty
