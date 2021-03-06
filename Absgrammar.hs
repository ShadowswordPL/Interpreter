module Absgrammar where

-- Haskell module generated by the BNF converter


newtype Ident = Ident String deriving (Eq,Ord,Show)
data Program =
   Prog InstrSet
  deriving (Eq,Ord,Show)

data InstrSet =
   ISetOne Instr
 | ISetMore Instr InstrSet
  deriving (Eq,Ord,Show)

data Instr =
   IDeclr Declr
 | IInstrM InstrM
 | IInstrU StmtUnmatch
  deriving (Eq,Ord,Show)

data InstrM =
   IInstrSemico StmtSemico
 | IInstrNoSemico StmtNoSemico
 | ICurlyBracket InstrSet
  deriving (Eq,Ord,Show)

data Type =
   TInt
 | TBool
  deriving (Eq,Ord,Show)

data Declr =
   DVar Type Ident Exp
 | DFun Type Ident Args Instr
  deriving (Eq,Ord,Show)

data Args =
   Args0
 | Args1 Arg
 | Args Arg Args
  deriving (Eq,Ord,Show)

data Arg =
   Arg Type Ident
 | ArgRef Type Ident
  deriving (Eq,Ord,Show)

data StmtUnmatch =
   SIf Exp Instr
 | SIfEU Exp InstrM StmtUnmatch
 | SWhileU Exp StmtUnmatch
 | SForStmtU StmtSemico Exp StmtSemico StmtUnmatch
 | SForU Declr Exp StmtSemico StmtUnmatch
  deriving (Eq,Ord,Show)

data StmtNoSemico =
   SIfE Exp InstrM InstrM
 | SWhile Exp InstrM
 | SForStmt StmtSemico Exp StmtSemico InstrM
 | SFor Declr Exp StmtSemico InstrM
  deriving (Eq,Ord,Show)

data StmtSemico =
   SSkip
 | SAssign Ident Exp
 | SPrint Exp
 | SReturn Exp
 | SExp Exp
  deriving (Eq,Ord,Show)

data Exp =
   EAdd Exp Exp
 | ESub Exp Exp
 | EMul Exp Exp
 | EDiv Exp Exp
 | EInt Integer
 | BOr Exp Exp
 | BAnd Exp Exp
 | BNeg Exp
 | BTrue
 | BFalse
 | ELess Exp Exp
 | EMore Exp Exp
 | EEq Exp Exp
 | ENeq Exp Exp
 | EVar Ident
 | EFunc Ident CallArgs
  deriving (Eq,Ord,Show)

data CallArgs =
   CallArgs0
 | CallArgs1 CallArg
 | CallArgs CallArg CallArgs
  deriving (Eq,Ord,Show)

data CallArg =
   CallArg Exp
  deriving (Eq,Ord,Show)

