module Main where

import Debug.Trace
import Text.Pretty.Simple (pPrint)

-- Variable identifier is a string name for the variable
newtype Ident = Ident String deriving (Eq, Show)

-- | Defining syntactic constructs
data Value
  = VVar Ident -- variable identifier with haskell string
  | VBool Bool -- boolean value with haskell boolean value
  | VInt Int -- integer value with haskell int value
  -- function definition from one SValue to SValue
  -- Note: that the function is only the definition and
  -- is not a value itself
  | VFunc Ident Expr
  deriving (Eq, Show)

-- | Defining grammar for expression
data Expr
  = EVal Value -- a value is the smallest indivisible expression
  | EParen Expr -- a parenthesized expression
  | EAnd Expr Expr
  | EOr Expr Expr
  | ENot Expr -- logical operations
  | EPlus Expr Expr
  | ESub Expr Expr
  | EEqual Expr Expr -- numerical operations and comparison
  -- applying one expression to another e.g. applying an argument to a function to evaluate it
  | EApp Expr Expr
  | -- if expr then expr else expr
    EIfThenElse Expr Expr Expr
  | -- let x = expr1 in expr2
    ELetIn Ident Expr Expr
  | -- recursive function definition
    -- let rec f x = expr1 in expr2
    ELetRecIn Ident Ident Expr Expr
  deriving (Eq, Show)

-- sub function substitutes a variable with a different expression
-- in a given expression. It is useful in implementing
-- function application, let in, let rec in. Any expression
-- that passes on context has use for this function.
sub :: Ident -> Expr -> Expr -> Expr
sub var@(Ident x) new e =
  case e of
      EVal va -> case va of
        VVar vn -> if vn == var then new else EVal va
        -- this is different from function application
        -- the function parameter is not substituted
        -- only any free variables inside function body
        -- are replaced with the new expression
        -- this means that if the a variable is the same
        -- as the function parameter it should not be replaced
        -- because it's bound to the function parameter and hence
        -- not free
        VFunc vn ex ->
          if vn == var
            then e
            else EVal $ VFunc vn (sub var new ex)
        _ -> EVal $ va
      EParen ex -> EParen (sub var new ex)
      EAnd ex ex' -> EAnd (sub var new ex) (sub var new ex')
      EOr ex ex' -> EOr (sub var new ex) (sub var new ex')
      ENot ex -> ENot (sub var new ex)
      EPlus ex ex' -> EPlus (sub var new ex) (sub var new ex')
      ESub ex ex' -> ESub (sub var new ex) (sub var new ex')
      EEqual ex ex' -> EEqual (sub var new ex) (sub var new ex')
      EApp ex ex' -> case ex of
        (EVal (VFunc x ex)) ->
          if x == var
            then -- if the function parameter is substituted
            -- the function body is now a closed expression
            -- and the function call can replaced by it's body
              sub var new ex
            else -- substitute variables in the function body and the
            -- expression being applied to the function
              EApp (EVal $ VFunc x (sub var new ex)) (sub var new ex')
        -- substitute variables in both expressions
        -- except double check if the first expression
        -- is replaced with a function then variables
        -- bound to the parameter should not be substituted
        -- in the second expression
        _ -> EApp (sub var new ex) (sub var new ex')
      EIfThenElse ex ex' ex2 -> EIfThenElse (sub var new ex) (sub var new ex') (sub var new ex2)
      ELetIn v ex ex' ->
        if v == var
          then e
          else ELetIn v (sub var new ex) (sub var new ex')
      ELetRecIn f x ex ex' ->
        if x == var
          then -- if variable is same as variable of let rec in
          -- then do not substitute it in expression body
          -- because they are bound to the parameter and
          -- are not free variables
            ELetRecIn f x ex (sub var new ex')
          else ELetRecIn f x (sub var new ex) (sub var new ex')

-- eval function relates an expression with it's value
-- however not all expression are well defined so eval
-- can throw an error as well
eval :: Expr -> Value
eval ex = case ex of
  EVal v -> v
  EParen ex -> eval ex
  EAnd ex ex' ->
    let v1 = eval ex
        v2 = eval ex'
     in case (v1, v2) of
          (VBool b1, VBool b2) -> VBool (b1 && b2)
          _ -> error "And expression expects boolean values"
  EOr ex ex' ->
    let v1 = eval ex
        v2 = eval ex'
     in case (v1, v2) of
          (VBool b1, VBool b2) -> VBool (b1 || b2)
          _ -> error "Or expression expects boolean values"
  ENot ex ->
    let v = eval ex
     in case v of
          (VBool b) -> VBool (not b)
          _ -> error "Not expression expects boolean values"
  EPlus ex ex' ->
    let v1 = eval ex
        v2 = eval ex'
     in case (v1, v2) of
          (VInt n1, VInt n2) -> VInt (n1 + n2)
          _ -> error "Plus expression expects integer values"
  ESub ex ex' ->
    let v1 = eval ex
        v2 = eval ex'
     in case (v1, v2) of
          (VInt n1, VInt n2) -> VInt (n1 - n2)
          _ -> error "Sub expression expects integer values"
  EEqual ex ex' ->
    let v1 = eval ex
        v2 = eval ex'
     in case (v1, v2) of
          (VInt n1, VInt n2) -> VBool (n1 == n2)
          _ -> error "Equal expression expects integer values"
  EApp func ex' -> case func of
    (EVal (VFunc x ex)) ->
      let v = eval ex'
          ex'' = sub x (EVal v) ex -- replace all occurrences off function parameter with value
       in eval ex''
    _ -> error "Application expression expects a function"
  EIfThenElse ex ex' ex2 ->
    let v = eval ex
     in case v of
          (VBool b) -> if b then eval ex' else eval ex2
          _ -> error "If then else expression expect boolean value in condition"
  ELetIn x ex ex' ->
    let v = eval ex
     in eval (sub x (EVal v) ex') -- substitute and evaluate
  ELetRecIn f x ex ex' ->
    let unroll = sub f (EVal $ VFunc x (ELetRecIn f x ex (EApp (EVal $ VVar f) (EVal $ VVar x)))) ex
        newFunc = EVal $ VFunc x unroll
        nextCall = sub f newFunc ex'
     in eval nextCall

helper :: Expr -> Expr
helper ex = case ex of
  ELetRecIn f x ex ex' ->
    let unroll = sub f (EVal $ VFunc x (ELetRecIn f x ex (EApp (EVal $ VVar f) (EVal $ VVar x)))) ex
        newFunc = EVal $ VFunc x unroll
        nextCall = sub f newFunc ex'
     in nextCall
  EApp func ex' -> case func of
    (EVal (VFunc x ex)) ->
      let v = eval ex'
          ex'' = sub x (EVal v) ex -- replace all occurrences off function parameter with value
       in ex''
    _ -> error "Application expression expects a function"
  EIfThenElse ex ex' ex2 ->
    let v = eval ex
     in case v of
          (VBool b) -> if b then ex' else ex2
          _ -> error "If then else expression expect boolean value in condition"
  EVal v -> ex
  _ -> ex

stepHelper :: Int -> Expr -> IO ()
stepHelper steps expr =
  let nextExpr = helper expr
      remaining = steps - 1
   in if remaining /= 0
        then do
          _ <- pPrint nextExpr
          stepHelper remaining nextExpr
        else do
          pPrint nextExpr

main :: IO ()
main = putStrLn "Hello, Haskell!"

addExample = EPlus (EVal $ VInt 1) (EVal $ VInt 2)

addTwoVariablesExample =
  EApp
    ( EApp
        (EVal $ VFunc (Ident "x") (EVal $ VFunc (Ident "y") (EPlus (EVal $ VVar $ Ident "x") (EVal $ VVar $ Ident "y"))))
        (EVal $ VInt 5)
    )
    (EVal $ VInt 10)

sumToNExample =
  ELetRecIn
    (Ident "func")
    (Ident "x")
    body
    (EApp (EVal $ VVar $ Ident "func") (EVal $ VInt 2))
  where
    body =
      EIfThenElse
        (EEqual (EVal $ VVar $ Ident "x") (EVal $ VInt 1))
        (EVal $ VInt 1)
        ( EPlus
            (EVal $ VVar $ Ident "x")
            (EApp (EVal $ VVar $ Ident "func") (ESub (EVal $ VVar $ Ident "x") (EVal $ VInt 1)))
        )
