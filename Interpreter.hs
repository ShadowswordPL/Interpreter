module Interpreter where

import Control.Monad.State.Lazy
import qualified Data.Map.Strict as Map
import Data.Maybe

import Lexgrammar
import Pargrammar
import Skelgrammar
import Printgrammar
import Absgrammar
import ErrM

type EnvMap = Map.Map Ident Location
type FunEnvMap = Map.Map Ident FunType
type StateMap = Map.Map Location MyType

data StateAndEnv = MyStateAndEnv EnvMap StateMap FunEnvMap deriving (Show, Ord, Eq)
type StateMonadType = StateT StateAndEnv Err 

data Location = LocationId Integer
              | Output String
              | ReturnValue MyType
              deriving (Show, Ord, Eq)

data MyType = MyInt Integer
            | MyBool Bool
            deriving (Show, Ord, Eq)

data FunType = MyFun Instr Args Type deriving (Show, Ord, Eq)

variableTypeErr = "Old and new variable type don't match" 
cannotInterpretTypeErr = "Cannot interpret "

outputElement = Ident "_output"
newLocationId = Ident "_newLocationId"
returnValue = Ident "_toReturn"

initialEnv :: EnvMap
initialEnv = Map.insert newLocationId (LocationId 0) $ Map.insert outputElement (Output "") Map.empty

getState :: StateAndEnv -> StateMap
getState (MyStateAndEnv env state funEnv) = state

getEnv :: StateAndEnv -> EnvMap
getEnv (MyStateAndEnv env state funEnv) = env

getFunEnv :: StateAndEnv -> FunEnvMap
getFunEnv (MyStateAndEnv env state funEnv) = funEnv

changeState :: (StateMap -> StateMap) -> StateMonadType ()
changeState f = let 
  changeStateHelper :: (StateMap -> StateMap) -> StateAndEnv -> StateAndEnv
  changeStateHelper f (MyStateAndEnv env state funcState) = MyStateAndEnv env (f state) funcState
  in do 
    modify $ changeStateHelper f

changeEnv :: (EnvMap -> EnvMap) -> StateMonadType ()
changeEnv f = let
    changeEnvHelper :: (EnvMap -> EnvMap) -> StateAndEnv -> StateAndEnv
    changeEnvHelper f (MyStateAndEnv env state funcState) = MyStateAndEnv (f env) state funcState
  in do
    modify $ changeEnvHelper f

changeFunEnv :: (FunEnvMap -> FunEnvMap) -> StateMonadType ()
changeFunEnv f = let
    changeFunEnvHelper :: (FunEnvMap -> FunEnvMap) -> StateAndEnv -> StateAndEnv
    changeFunEnvHelper f (MyStateAndEnv env state funcState) = MyStateAndEnv env state (f funcState)
  in do
    modify $ changeFunEnvHelper f

getInt :: MyType -> StateMonadType Integer
getInt (MyInt x) = do
  return x
getInt (MyBool x) = fail $ cannotInterpretTypeErr ++ "Bool as Int"

getBool :: MyType -> StateMonadType Bool
getBool (MyBool x) = do
  return x
getBool (MyInt x) = fail $ cannotInterpretTypeErr ++ "Int as Bool"

sameType :: MyType -> MyType -> StateMonadType ()
sameType (MyBool x) (MyBool y) = do
  return ()

sameType (MyInt x) (MyInt y) = do
  return ()

sameType x y = fail variableTypeErr

checkTypeWithDeclr :: Type -> MyType -> StateMonadType ()
checkTypeWithDeclr expType resultExp = do
  if (expType == TBool) then
      do 
        getBool resultExp -- test type
        return 0 -- if type have to match
    else
      getInt resultExp -- test type
  return ()

mapLookup :: (Ord a, Eq a) => a -> Map.Map a b -> StateMonadType b
mapLookup idx map = let 
  mapLookupHelp :: Maybe b -> StateMonadType b
  mapLookupHelp (Just x) = do
    return x
  mapLookupHelp Nothing = fail "Variable does not exist or function haven't got return value"
  in do
    mapLookupHelp (Map.lookup idx map)

getInstr :: FunType -> Instr
getInstr (MyFun instr args funType) = instr

getFunArgs :: FunType -> Args
getFunArgs (MyFun instr args funType) = args

getType :: FunType -> Type
getType (MyFun instr args funType) = funType

getReturnValue :: Location -> MyType
getReturnValue (ReturnValue ret) = ret

toOutput :: MyType -> Location
toOutput (MyInt x) = Output $ show x
toOutput (MyBool x) = Output $ show x

concatOutput :: Location -> Location -> Location
concatOutput (Output new) (Output fromMap)  = Output $ fromMap ++ new ++ "\n"

concatOutputWithoutNewLine :: Location -> Location -> Location
concatOutputWithoutNewLine (Output new) (Output fromMap)  = Output $ fromMap ++ new

-- this design is ugly, cuz I wanted to use Map.insertWith
incrementLocation :: Location -> Location -> Location
incrementLocation (LocationId x) (LocationId y) = LocationId (x + y)

generateNextLocation :: StateMonadType Location
generateNextLocation = do
  changeEnv $ Map.insertWith incrementLocation newLocationId (LocationId 1)
  currentEnvAndState <- get
  mapLookup newLocationId (getEnv currentEnvAndState)

execExp :: Exp -> StateMonadType MyType
execExp exp = let

  doArtmethicOperation :: (Integer -> Integer -> Integer) -> Exp -> Exp -> StateMonadType MyType
  doArtmethicOperation op exp1 exp2 = do
    val1 <- execExpHelp exp1
    int1 <- getInt val1
    val2 <- execExpHelp exp2
    int2 <- getInt val2
    return $ MyInt $ op int1 int2  

  doBoolOperation :: (Bool -> Bool -> Bool) -> Exp -> Exp -> StateMonadType MyType
  doBoolOperation op exp1 exp2 = do
    val1 <- execExpHelp exp1
    bool1 <- getBool val1
    val2 <- execExpHelp exp2
    bool2 <- getBool val2
    return $ MyBool $ op bool1 bool2

  doArtmethicCompersion :: (Integer -> Integer -> Bool) -> Exp -> Exp -> StateMonadType MyType
  doArtmethicCompersion op exp1 exp2 = do
    val1 <- execExpHelp exp1
    int1 <- getInt val1
    val2 <- execExpHelp exp2
    int2 <- getInt val2
    return $ MyBool $ op int1 int2

  execExpHelp :: Exp -> StateMonadType MyType
  execExpHelp (EInt x) = do
    return $ MyInt x

  execExpHelp (EAdd exp1 exp2) = do
    doArtmethicOperation (+) exp1 exp2

  execExpHelp (ESub exp1 exp2) = do
    doArtmethicOperation (-) exp1 exp2

  execExpHelp (EMul exp1 exp2) = do
    doArtmethicOperation (*) exp1 exp2

  execExpHelp (EDiv exp1 exp2) = do
    doArtmethicOperation div exp1 exp2

  execExpHelp (BNeg exp) = do
    val <- execExpHelp exp
    bool <- getBool val
    return $ MyBool $ not bool 

  execExpHelp (BAnd exp1 exp2) = do
    doBoolOperation (&&) exp1 exp2

  execExpHelp (BOr exp1 exp2) = do
    doBoolOperation (||) exp1 exp2

  execExpHelp BTrue = do
    return $ MyBool True

  execExpHelp BFalse = do
    return $ MyBool False

  execExpHelp (ELess exp1 exp2) = do
    doArtmethicCompersion (<) exp1 exp2

  execExpHelp (EMore exp1 exp2) = do
    doArtmethicCompersion (>) exp1 exp2

  execExpHelp (EEq exp1 exp2) = do
    doArtmethicCompersion (==) exp1 exp2

  execExpHelp (ENeq exp1 exp2) = do
    doArtmethicCompersion (/=) exp1 exp2

  execExpHelp (EVar ident) = do
    stateAndEnv <- get
    loc <- mapLookup ident (getEnv stateAndEnv)
    mapLookup loc (getState stateAndEnv)

  execExpHelp (EFunc ident callArgs) = let
    fixReferences :: Args -> CallArgs -> StateAndEnv -> StateMonadType StateAndEnv
    fixReferences (Args1 (ArgRef t identFun)) (CallArgs1 (CallArg (EVar identCall))) resultStateAndEnv = do
      stateAndEnv <- get
      loc <- mapLookup identCall (getEnv stateAndEnv)
      resultLoc <- mapLookup identFun (getEnv resultStateAndEnv)
      resultVar <- mapLookup resultLoc (getState resultStateAndEnv)
      changeState $ Map.insert loc resultVar
      get

    fixReferences (Args (ArgRef t identFun) nextArgs) (CallArgs (CallArg (EVar identCall)) nextCallArgs) resultStateAndEnv = do
      fixReferences (Args1 (ArgRef t identFun)) (CallArgs1 (CallArg (EVar identCall))) resultStateAndEnv
      fixReferences nextArgs nextCallArgs resultStateAndEnv

    fixReferences (Args (Arg t identFun) nextArgs) (CallArgs (CallArg exp) nextCallArgs) resultStateAndEnv = do
      fixReferences nextArgs nextCallArgs resultStateAndEnv

    fixReferences argsOther callArgsOther resultStateAndEnv = do
      get

    getStateAndEnvFromErr :: Err ((), StateAndEnv) -> StateMonadType StateAndEnv
    getStateAndEnvFromErr (Ok ((), stateAndEnv)) = do
      return stateAndEnv
    getStateAndEnvFromErr (Bad str) = fail str

    addArgsToStateAndEnv :: Args -> CallArgs -> FunEnvMap-> StateMonadType StateAndEnv
    addArgsToStateAndEnv args callArgs funEnv = let
      addToNewState :: Ident -> MyType -> StateMonadType ()
      addToNewState ident resultExp = do
        newLoc <- generateNextLocation
        changeEnv $ Map.insert ident newLoc
        changeState $ Map.insert newLoc resultExp

      addArgsToStateAndEnvHelp :: Args -> CallArgs -> StateAndEnv -> StateMonadType StateAndEnv
      addArgsToStateAndEnvHelp (Args (Arg t ident) nextArgs) (CallArgs (CallArg exp) nextCallArgs) stateAndEnv = do
        resultStateAndEnv <- addArgsToStateAndEnvHelp (Args1 (Arg t ident)) (CallArgs1 (CallArg exp)) stateAndEnv
        addArgsToStateAndEnvHelp nextArgs nextCallArgs resultStateAndEnv

      addArgsToStateAndEnvHelp (Args (ArgRef t ident) nextArgs) (CallArgs (CallArg exp) nextCallArgs) stateAndEnv =
        addArgsToStateAndEnvHelp (Args (Arg t ident) nextArgs) (CallArgs (CallArg exp) nextCallArgs) stateAndEnv

      addArgsToStateAndEnvHelp (Args1 (Arg t ident)) (CallArgs1 (CallArg exp)) stateAndEnv = do
        resultExp <- execExp exp
        let resultErrStateAndEnv = runStateT (addToNewState ident resultExp) stateAndEnv
        resultStateAndEnv <- getStateAndEnvFromErr resultErrStateAndEnv
        return resultStateAndEnv

      addArgsToStateAndEnvHelp (Args1 (ArgRef t ident)) (CallArgs1 (CallArg exp)) stateAndEnv =
        addArgsToStateAndEnvHelp (Args1 (Arg t ident)) (CallArgs1 (CallArg exp)) stateAndEnv

      addArgsToStateAndEnvHelp args0 callArgs0 stateAndEnv = do
        return stateAndEnv

      in do
        addArgsToStateAndEnvHelp args callArgs (MyStateAndEnv initialEnv Map.empty funEnv)

    in do
      stateAndEnv <- get
      let funEnv = getFunEnv stateAndEnv
    
      function <- mapLookup ident (getFunEnv stateAndEnv)
      let funType = getType $ function
      let args = getFunArgs $ function
      let instr = getInstr $ function

      newStateAndEnv <- (addArgsToStateAndEnv args callArgs funEnv)
      
      let resultErrStateAndEnv = runStateT (execInstrSet (ISetOne instr)) newStateAndEnv
      resultStateAndEnv <- getStateAndEnvFromErr resultErrStateAndEnv

      let resultEnv = getEnv $ resultStateAndEnv

      fixReferences args callArgs resultStateAndEnv

      functionOutput <- mapLookup outputElement resultEnv
      changeEnv $ Map.insertWith concatOutputWithoutNewLine outputElement functionOutput
      
      returnedValueWrapped <- mapLookup returnValue resultEnv
      let returnedValue = getReturnValue $ returnedValueWrapped
      checkTypeWithDeclr funType returnedValue
      return returnedValue

  in execExpHelp exp

-- Unwrap instructions
execInstr :: Instr -> StateMonadType ()
execInstr instr = let
  doIfElse :: Exp -> Instr -> Instr -> StateMonadType ()
  doIfElse exp instr1 instr2 = do
    resultExp <- execExp exp
    bool <- getBool resultExp
    if bool then
      execInstrHelp instr1
    else
      execInstrHelp instr2

  doWhile :: Exp -> InstrSet -> StateMonadType ()
  doWhile exp instrSet = do
    resultExp <- execExp exp
    bool <- getBool resultExp
    if bool then
      execInstrSet instrSet
    else
      return ()

  execInstrHelp :: Instr -> StateMonadType ()
  execInstrHelp (IInstrM (IInstrSemico SSkip)) = do
    return ()

  execInstrHelp (IInstrM (IInstrSemico (SReturn exp))) = do
    result <- execExp exp
    changeEnv $ Map.insert returnValue (ReturnValue $ result)

  execInstrHelp (IInstrM (IInstrSemico (SExp exp))) = do
    result <- execExp exp
    return ()

  execInstrHelp (IInstrM (IInstrSemico (SPrint exp))) = do
    resultExp <- execExp exp
    changeEnv $ Map.insertWith concatOutput outputElement (toOutput resultExp)

  execInstrHelp (IInstrM (IInstrSemico (SAssign ident exp))) = do
    stateAndEnv <- get
    resultExp <- execExp exp
    loc <- mapLookup ident (getEnv stateAndEnv)
    current <- mapLookup loc (getState stateAndEnv)
    sameType current resultExp
    changeState $ Map.insert loc resultExp

  execInstrHelp (IDeclr (DVar expType ident exp)) = do
    resultExp <- execExp exp
    newLoc <- generateNextLocation
    changeEnv $ Map.insert ident newLoc
    checkTypeWithDeclr expType resultExp
    changeState $ Map.insert newLoc resultExp

  execInstrHelp (IDeclr (DFun funType ident args instr)) = do
    stateAndEnv <- get
    let locMaybe = Map.lookup ident (getFunEnv stateAndEnv)
    if locMaybe == Nothing then -- don't allow declaration of function with same name twice
      changeFunEnv $ Map.insert ident (MyFun instr args funType)
    else 
      fail "Function with this name exist"
    

  execInstrHelp (IInstrU (SIf exp instr)) = do
    doIfElse exp instr (IInstrM (IInstrSemico SSkip))

  execInstrHelp (IInstrU (SIfEU exp instr1 instr2)) = do
    doIfElse exp (IInstrM instr1) (IInstrU instr2)
    
  execInstrHelp (IInstrM (IInstrNoSemico (SIfE exp instr1 instr2))) = do
    doIfElse exp (IInstrM instr1) (IInstrM instr2)

  execInstrHelp (IInstrU (SWhileU exp instr)) = do
    doWhile exp (ISetMore (IInstrU instr) (ISetOne (IInstrU (SWhileU exp instr))))

  execInstrHelp (IInstrM (IInstrNoSemico (SWhile exp instr))) = do
    doWhile exp (ISetMore (IInstrM instr) (ISetOne (IInstrM (IInstrNoSemico (SWhile exp instr)))))

  execInstrHelp (IInstrM (IInstrNoSemico (SForStmt instrFirst exp instrAfter instr))) = do
    let instrAfterWithNextFor = ISetMore (IInstrM (IInstrSemico instrAfter)) (ISetOne (IInstrM (IInstrNoSemico (SForStmt SSkip exp instrAfter instr))))
    let instrAndInstrAfter = ISetMore (IInstrM instr) instrAfterWithNextFor 
    
    execInstrHelp (IInstrM (IInstrSemico instrFirst))
    resultExp <- execExp exp
    bool <- getBool resultExp
    if bool then
      execInstrHelp(IInstrM (ICurlyBracket instrAndInstrAfter))
    else
      return ()

  execInstrHelp (IInstrU (SForStmtU instrFirst exp instrAfter instr)) = do
    let instrAfterWithNextFor = ISetMore (IInstrM (IInstrSemico instrAfter)) (ISetOne (IInstrU(SForStmtU SSkip exp instrAfter instr)))
    let instrAndInstrAfter = ISetMore (IInstrU instr) instrAfterWithNextFor 
    
    execInstrHelp (IInstrM (IInstrSemico instrFirst))
    resultExp <- execExp exp
    bool <- getBool resultExp
    if bool then
      execInstrHelp(IInstrM (ICurlyBracket instrAndInstrAfter))
    else
      return ()

  execInstrHelp (IInstrM (IInstrNoSemico (SFor declr exp instrAfter instr))) = do
    let instrAfterWithNextFor = ISetMore (IInstrM (IInstrSemico instrAfter)) (ISetOne (IInstrM (IInstrNoSemico (SForStmt SSkip exp instrAfter instr))))
    let instrAndInstrAfter = ISetMore (IInstrM instr) instrAfterWithNextFor 
    let instrSet = ISetMore (IDeclr declr) instrAndInstrAfter
    execInstrHelp(IInstrM (ICurlyBracket instrSet))
  
  execInstrHelp (IInstrU (SForU declr exp instrAfter instr)) = do
    let instrAfterWithNextFor = ISetMore (IInstrM (IInstrSemico instrAfter)) (ISetOne (IInstrU (SForStmtU SSkip exp instrAfter instr)))
    let instrAndInstrAfter = ISetMore (IInstrU instr) instrAfterWithNextFor 
    let instrSet = ISetMore (IDeclr declr) instrAndInstrAfter
    execInstrHelp(IInstrM (ICurlyBracket instrSet))
  
  execInstrHelp (IInstrM (ICurlyBracket instrSet)) = do
    oldStateAndEnv <- get
    execInstrSet instrSet
    newStateAndEnv <- get
    -- We will overwrite new Env with the old one, but we want to update Output descriptor and return value
    output <- mapLookup outputElement (getEnv newStateAndEnv)
    let returnValMaybe = Map.lookup returnValue (getEnv newStateAndEnv)
    put $ MyStateAndEnv (getEnv oldStateAndEnv) (getState newStateAndEnv) (getFunEnv oldStateAndEnv)
    changeEnv $ Map.insert outputElement output
    if returnValMaybe /= Nothing then -- Update only if block contained return
      changeEnv $ Map.insert returnValue (fromJust returnValMaybe)
    else 
      return ()

  in execInstrHelp instr 

execInstrSet :: InstrSet -> StateMonadType ()
execInstrSet (ISetOne instr) = do
  execInstr instr

execInstrSet (ISetMore instr1 instr2) = do
  execInstrSet (ISetOne instr1)
  stateAndEnv <- get
  let returnValMaybe = Map.lookup returnValue (getEnv stateAndEnv)
  if returnValMaybe /= Nothing then 
    return ()
  else 
    execInstrSet instr2

-- Main function
execProg :: Program -> Err ((), StateAndEnv)
execProg prog = let

  execProgHelp :: Program -> StateMonadType ()
  execProgHelp (Prog instrSet) = do
    execInstrSet instrSet 

  in runStateT (execProgHelp prog) (MyStateAndEnv initialEnv Map.empty Map.empty)

printProgram :: StateAndEnv -> String
printProgram (MyStateAndEnv env state funEnv) = let
  strFromOutput (Output str) = str
  in strFromOutput $ fromJust $ Map.lookup outputElement env
