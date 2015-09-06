module TypeChecker where

import Lexgrammar
import Pargrammar
import Skelgrammar
import Printgrammar
import Absgrammar
import ErrM

import Interpreter

typeInt = MyInt 0
typeBool = MyBool False

isBool :: Exp -> String -> Err ()
isBool exp msg = let
  isBoolHelper (MyBool x) msg = Ok ()
  isBoolHelper x msg = Bad msg
  in do
    resultType <- checkTypeExp exp
    isBoolHelper resultType msg 

isInt:: Exp -> String -> Err ()
isInt exp msg = let
  isIntHelper (MyInt x) msg = Ok ()
  isIntHelper x msg = Bad msg
  in do
    resultType <- checkTypeExp exp
    isIntHelper resultType msg 

arithmeticType :: Exp -> Exp -> String -> Err MyType
arithmeticType exp1 exp2 opName = do
  let msg = "Expressions in " ++ opName ++ " must be Int"
  isInt exp1 msg
  isInt exp2 msg
  return $ typeInt

checkTypeExp :: Exp -> Err MyType
checkTypeExp (EInt x) = do
  return $ typeInt
  
checkTypeExp (EAdd exp1 exp2) = do
  arithmeticType exp1 exp2 "sum"

-- checkTypeExp (ESub exp1 exp2) = do
 
-- checkTypeExp (EMul exp1 exp2) = do
 
-- checkTypeExp (EDiv exp1 exp2) = do
 
-- checkTypeExp (BNeg exp) = do
 
-- checkTypeExp (BAnd exp1 exp2) = do
 
-- checkTypeExp (BOr exp1 exp2) = do
 
checkTypeExp BTrue = do
  return $ typeBool
 
checkTypeExp BFalse = do
  return $ typeBool 

-- checkTypeExp (ELess exp1 exp2) = do
 
-- checkTypeExp (EMore exp1 exp2) = do
 
-- checkTypeExp (EEq exp1 exp2) = do
 
-- checkTypeExp (ENeq exp1 exp2) = do
 
checkTypeExp (EVar ident) = do
  
 
-- checkTypeExp (EFunc ident callArgs) = let
checkTypeExp exp = do
  return $ typeInt

checkTypeInstr :: Instr -> Err ()

-- checkTypeInstr (IInstrM (IInstrSemico SSkip)) = do
    
-- checkTypeInstr (IInstrM (IInstrSemico (SReturn exp))) = do
    
-- checkTypeInstr (IInstrM (IInstrSemico (SExp exp))) = do
    
-- checkTypeInstr (IInstrM (IInstrSemico (SPrint exp))) = do
    
-- checkTypeInstr (IInstrM (IInstrSemico (SAssign ident exp))) = do
    
checkTypeInstr (IDeclr (DVar expType ident exp)) = 
  if expType == TBool then
    isBool exp "Cannot assign Int to Bool variable"
  else
    isInt exp "Cannot assign Bool to Int variable"

-- checkTypeInstr (IDeclr (DFun funType ident args instr)) = do
    
-- checkTypeInstr (IInstrU (SIf exp instr)) = do
    
-- checkTypeInstr (IInstrU (SIfEU exp instr1 instr2)) = do
    
-- checkTypeInstr (IInstrM (IInstrNoSemico (SIfE exp instr1 instr2))) = do
    
-- checkTypeInstr (IInstrU (SWhileU exp instr)) = do
    
-- checkTypeInstr (IInstrM (IInstrNoSemico (SWhile exp instr))) = do
    
-- checkTypeInstr (IInstrM (IInstrNoSemico (SForStmt instrFirst exp instrAfter instr))) = do
    
-- checkTypeInstr (IInstrU (SForStmtU instrFirst exp instrAfter instr)) = do
    
-- checkTypeInstr (IInstrM (IInstrNoSemico (SFor declr exp instrAfter instr))) = do
  
-- checkTypeInstr (IInstrU (SForU declr exp instrAfter instr)) = do
  
-- checkTypeInstr (IInstrM (ICurlyBracket instrSet)) = do


checkTypeInstr instr = do
  return ()

checkTypeSet :: InstrSet -> Err ()
checkTypeSet (ISetOne instr) = do
  checkTypeInstr instr

checkTypeSet (ISetMore instr1 instr2) = do
  checkTypeSet (ISetOne instr1)
  checkTypeSet instr2

checkType :: Program -> Err ()
checkType (Prog instrSet) = do
  checkTypeSet instrSet 


