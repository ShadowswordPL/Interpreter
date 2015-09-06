{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Printgrammar where

-- pretty-printer generated by the BNF converter

import Absgrammar
import Data.Char


-- the top-level printing method
printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : "," :ts -> showString t . space "," . rend i ts
    t  : ")" :ts -> showString t . showChar ')' . rend i ts
    t  : "]" :ts -> showString t . showChar ']' . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else (' ':s))

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- the printer class does the job
class Print a where
  prt :: Int -> a -> Doc
  prtList :: [a] -> Doc
  prtList = concatD . map (prt 0)

instance Print a => Print [a] where
  prt _ = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j<i then parenth else id


instance Print Integer where
  prt _ x = doc (shows x)


instance Print Double where
  prt _ x = doc (shows x)


instance Print Ident where
  prt _ (Ident i) = doc (showString ( i))



instance Print Program where
  prt i e = case e of
   Prog instrset -> prPrec i 0 (concatD [prt 0 instrset])


instance Print InstrSet where
  prt i e = case e of
   ISetOne instr -> prPrec i 0 (concatD [prt 0 instr])
   ISetMore instr instrset -> prPrec i 0 (concatD [prt 0 instr , prt 0 instrset])


instance Print Instr where
  prt i e = case e of
   IDeclr declr -> prPrec i 0 (concatD [prt 0 declr])
   IInstrM instrm -> prPrec i 0 (concatD [prt 0 instrm])
   IInstrU stmtunmatch -> prPrec i 0 (concatD [prt 0 stmtunmatch])


instance Print InstrM where
  prt i e = case e of
   IInstrSemico stmtsemico -> prPrec i 0 (concatD [prt 0 stmtsemico , doc (showString ";")])
   IInstrNoSemico stmtnosemico -> prPrec i 0 (concatD [prt 0 stmtnosemico])
   ICurlyBracket instrset -> prPrec i 0 (concatD [doc (showString "{") , prt 0 instrset , doc (showString "}")])


instance Print Type where
  prt i e = case e of
   TInt  -> prPrec i 0 (concatD [doc (showString "int")])
   TBool  -> prPrec i 0 (concatD [doc (showString "bool")])


instance Print Declr where
  prt i e = case e of
   DVar type' id exp -> prPrec i 0 (concatD [prt 0 type' , prt 0 id , doc (showString "=") , prt 0 exp , doc (showString ";")])
   DFun type' id args instr -> prPrec i 0 (concatD [prt 0 type' , prt 0 id , doc (showString "(") , prt 0 args , doc (showString ")") , prt 0 instr])


instance Print Args where
  prt i e = case e of
   Args0  -> prPrec i 0 (concatD [])
   Args1 arg -> prPrec i 0 (concatD [prt 0 arg])
   Args arg args -> prPrec i 0 (concatD [prt 0 arg , doc (showString ",") , prt 0 args])


instance Print Arg where
  prt i e = case e of
   Arg type' id -> prPrec i 0 (concatD [prt 0 type' , prt 0 id])
   ArgRef type' id -> prPrec i 0 (concatD [prt 0 type' , doc (showString "ref") , prt 0 id])


instance Print StmtUnmatch where
  prt i e = case e of
   SIf exp instr -> prPrec i 0 (concatD [doc (showString "if") , doc (showString "(") , prt 0 exp , doc (showString ")") , prt 0 instr])
   SIfEU exp instrm stmtunmatch -> prPrec i 0 (concatD [doc (showString "if") , doc (showString "(") , prt 0 exp , doc (showString ")") , prt 0 instrm , doc (showString "else") , prt 0 stmtunmatch])
   SWhileU exp stmtunmatch -> prPrec i 0 (concatD [doc (showString "while") , doc (showString "(") , prt 0 exp , doc (showString ")") , prt 0 stmtunmatch])
   SForStmtU stmtsemico0 exp stmtsemico stmtunmatch -> prPrec i 0 (concatD [doc (showString "for") , doc (showString "(") , prt 0 stmtsemico0 , doc (showString ";") , prt 0 exp , doc (showString ";") , prt 0 stmtsemico , doc (showString ")") , prt 0 stmtunmatch])
   SForU declr exp stmtsemico stmtunmatch -> prPrec i 0 (concatD [doc (showString "for") , doc (showString "(") , prt 0 declr , prt 0 exp , doc (showString ";") , prt 0 stmtsemico , doc (showString ")") , prt 0 stmtunmatch])


instance Print StmtNoSemico where
  prt i e = case e of
   SIfE exp instrm0 instrm -> prPrec i 0 (concatD [doc (showString "if") , doc (showString "(") , prt 0 exp , doc (showString ")") , prt 0 instrm0 , doc (showString "else") , prt 0 instrm])
   SWhile exp instrm -> prPrec i 0 (concatD [doc (showString "while") , doc (showString "(") , prt 0 exp , doc (showString ")") , prt 0 instrm])
   SForStmt stmtsemico0 exp stmtsemico instrm -> prPrec i 0 (concatD [doc (showString "for") , doc (showString "(") , prt 0 stmtsemico0 , doc (showString ";") , prt 0 exp , doc (showString ";") , prt 0 stmtsemico , doc (showString ")") , prt 0 instrm])
   SFor declr exp stmtsemico instrm -> prPrec i 0 (concatD [doc (showString "for") , doc (showString "(") , prt 0 declr , prt 0 exp , doc (showString ";") , prt 0 stmtsemico , doc (showString ")") , prt 0 instrm])


instance Print StmtSemico where
  prt i e = case e of
   SSkip  -> prPrec i 0 (concatD [doc (showString "skip")])
   SAssign id exp -> prPrec i 0 (concatD [prt 0 id , doc (showString "=") , prt 0 exp])
   SPrint exp -> prPrec i 0 (concatD [doc (showString "print") , prt 0 exp])
   SReturn exp -> prPrec i 0 (concatD [doc (showString "return") , prt 0 exp])
   SExp exp -> prPrec i 0 (concatD [prt 0 exp])


instance Print Exp where
  prt i e = case e of
   EAdd exp0 exp -> prPrec i 4 (concatD [prt 4 exp0 , doc (showString "+") , prt 5 exp])
   ESub exp0 exp -> prPrec i 4 (concatD [prt 4 exp0 , doc (showString "-") , prt 5 exp])
   EMul exp0 exp -> prPrec i 5 (concatD [prt 5 exp0 , doc (showString "*") , prt 6 exp])
   EDiv exp0 exp -> prPrec i 5 (concatD [prt 5 exp0 , doc (showString "/") , prt 6 exp])
   EInt n -> prPrec i 6 (concatD [prt 0 n])
   BOr exp0 exp -> prPrec i 0 (concatD [prt 0 exp0 , doc (showString "||") , prt 1 exp])
   BAnd exp0 exp -> prPrec i 1 (concatD [prt 1 exp0 , doc (showString "&&") , prt 2 exp])
   BNeg exp -> prPrec i 2 (concatD [doc (showString "!") , prt 2 exp])
   BTrue  -> prPrec i 3 (concatD [doc (showString "true")])
   BFalse  -> prPrec i 3 (concatD [doc (showString "false")])
   ELess exp0 exp -> prPrec i 3 (concatD [prt 3 exp0 , doc (showString "<") , prt 4 exp])
   EMore exp0 exp -> prPrec i 3 (concatD [prt 3 exp0 , doc (showString ">") , prt 4 exp])
   EEq exp0 exp -> prPrec i 3 (concatD [prt 3 exp0 , doc (showString "==") , prt 4 exp])
   ENeq exp0 exp -> prPrec i 3 (concatD [prt 3 exp0 , doc (showString "!=") , prt 4 exp])
   EVar id -> prPrec i 6 (concatD [prt 0 id])
   EFunc id callargs -> prPrec i 6 (concatD [prt 0 id , doc (showString "(") , prt 0 callargs , doc (showString ")")])


instance Print CallArgs where
  prt i e = case e of
   CallArgs0  -> prPrec i 0 (concatD [])
   CallArgs1 callarg -> prPrec i 0 (concatD [prt 0 callarg])
   CallArgs callarg callargs -> prPrec i 0 (concatD [prt 0 callarg , doc (showString ",") , prt 0 callargs])


instance Print CallArg where
  prt i e = case e of
   CallArg exp -> prPrec i 0 (concatD [prt 0 exp])


