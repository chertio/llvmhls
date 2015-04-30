#ifndef GENERATECINS
#define GENERATECINS

#include "llvm/Support/IncludeFile.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "InstructionGraph.h"
#include "generatePartitionsUtil.h"
#include <string>
#define ENDBLOCK "END"



typedef std::map<BasicBlock*, std::vector<std::string>*> BBMap2outStr;

static void addBarSubTabs(bool addBarSub);
static bool genCPUCode();
static void addTabbedLine(std::string& original, std::string next);


static int getNumOfBitsForTag(int numSuc)
{

    int tagWidth = std::ceil(std::log(numSuc));
    tagWidth = tagWidth<1? 1: tagWidth;
    return tagWidth;
}

struct argPair
{
    std::string argType;
    std::string argName;
    // 0 means read, 1 means write, 2 means read/write
    int size;
    char dir;
};

std::string generateArgStr(argPair* ap)
{
    return ap->argType +" "+ ap->argName;
}

std::string getLLVMTypeStr(Type* valPtrType)
{
    std::string varType;
    switch(valPtrType->getTypeID())
    {
        case Type::VoidTyID:
            varType="";
            break;
        case Type::HalfTyID:
            varType="short";
            break;
        case Type::FloatTyID:
            varType="float";
            break;
        case Type::DoubleTyID:
            varType ="double";
            break;
        //X86_FP80TyID,    ///<  4: 80-bit floating point type (X87)
        //FP128TyID,       ///<  5: 128-bit floating point type (112-bit mantissa)
        //PPC_FP128TyID,   ///<  6: 128-bit floating point type (two 64-bits, PowerPC)
        //LabelTyID,       ///<  7: Labels
        //MetadataTyID,    ///<  8: Metadata
        //X86_MMXTyID,     ///<  9: MMX vectors (64 bits, X86 specific)

    // Derived types... see DerivedTypes.h file.
    // Make sure FirstDerivedTyID stays up to date!
        case Type::IntegerTyID:     ///< 10: Arbitrary bit width integers
            // only support 32 bit or less now
            assert(valPtrType->getScalarSizeInBits()<=32);
            varType ="int";
            break;
        //FunctionTyID,    ///< 11: Functions
        //StructTyID,      ///< 12: Structures
        //FIXME: wanna support array type
        //ArrayTyID,       ///< 13: Arrays
        case Type::PointerTyID:
            {
                Type* ptedType = valPtrType->getPointerElementType();
                std::string ptedTypeStr = getLLVMTypeStr(ptedType);
                varType = ptedTypeStr+"*";
            }
            break;
        //VectorTyID,      ///< 15: SIMD 'packed' format, or other vector type
        default:
            errs()<<"unhandled type, exit\n";
            exit(1);
    }

    return varType;
}



std::string generateVariableName(Instruction* ins, int seqNum)
{
    std::string rtVarName= ins->getParent()->getName();

    rtVarName = rtVarName+int2Str(seqNum);
    return rtVarName;
}

int getInstructionSeqNum(Instruction* ins)
{
    BasicBlock* BB=ins->getParent();
    int seqNum = -1;
    for(BasicBlock::iterator insPt = BB->begin(), insEnd = BB->end(); insPt != insEnd; insPt++)
    {
        seqNum++;
        if( ins == insPt)
            break;
    }
    return seqNum;
}


std::string generateVariableName(Instruction* ins)
{
    int seqNum = getInstructionSeqNum(ins);
    return generateVariableName(ins, seqNum);
}
/*
std::string generateGetElementPtrInstVarDec(Instruction& ins)
{
    std::string varType;
    if(!isa<GetElementPtrInst>(ins))
    {
        errs()<<"returning pointer type but not getele\n";
        exit(1);
    }
    GetElementPtrInst& gepi = cast<GetElementPtrInst>(ins);
    SmallVector<Value*, 16> Idxs(gepi.idx_begin(), gepi.idx_end());
    Type *ElTy = GetElementPtrInst::getIndexedType(gepi.getPointerOperandType(), Idxs);
    // now check what is it refered to
    switch(ElTy->getTypeID())
    {
        case Type::IntegerTyID:
            varType="int* ";
            break;
        case Type::FloatTyID:
            varType="float* ";
            break;
        case Type::DoubleTyID:
            varType ="double* ";
            break;
        case Type::HalfTyID:
            varType="short* ";
            break;
        //FIXME: need to recursively get the pointer type?
        case Type::PointerTyID:
        default:
            varType ="void* ";

    }
    return varType;
}*/


// the thing about the type generation is that
// if a pointer value is transported, then they should be
// transported as unsigned, as the local reference would
// be adding it to a memory access pointer
// FIXME: later the actual memory operation would need
// to add a port for memory access at the function declaration
// too
std::string generateVariableType(const Value* valPtr)
{
    std::string varType;
    if(isa<Instruction>(*valPtr))
    {
        const Instruction* ins  = &(cast<Instruction>(*valPtr));
        // a special case for generating the branches
        // they might be used to communicate control
        // dependencies thus need a type
        if(ins->isTerminator()&&!isa<ReturnInst>(*ins))
        {
            // got to check the number of successors
            // log2 it to get number of bits
            const TerminatorInst* termIns =&(cast<TerminatorInst>(*ins));
            int numSuc = termIns->getNumSuccessors();
            int tagWidth = getNumOfBitsForTag(numSuc);
            if(genCPUCode())
                varType = "int";
            else
            {
                varType = "ap_int<";
                varType += int2Str(tagWidth);
                varType += ">";
            }
            return varType;

        }
    }
    return getLLVMTypeStr(valPtr->getType());


}

std::string generateFifoType(Value* valPtr)
{
    std::string varType;


    if(isa<Instruction>(*valPtr))
    {
        Instruction* ins =0;
        ins = &(cast<Instruction>(*valPtr));
        if(isa<GetElementPtrInst>(*ins))
        {
            if(genCPUCode())
                varType = "u64";
            else
                varType = "u32";
        }
        else if(isa<TerminatorInst>(*ins))
        {
            varType = generateVariableType(ins);
        }
        else
        {

            std::string rawType =getLLVMTypeStr(valPtr->getType());
            varType = rawType;
        }
    }
    else
    {
        errs()<<"not instruction for fifo args\n";
        exit(1);

    }
    if(genCPUCode())
    {
        // the parameter would be a fifo chanel
        varType = "struct channel_info<"+varType+">*";
    }
    else
    {
        varType = varType+"*";
    }


    return varType;


}

std::string generatePushOp(std::string varName, std::string channelName)
{
    std::string rtStr="push ("+channelName+","+varName+");\n";
    return rtStr;
}

std::string generateVariableDeclStr(Instruction* ins, int seqNum)
{

    std::string rtVarName = generateVariableName(ins,seqNum);

    std::string rtStr="";
    std::string varType=generateVariableType(ins);
    if(varType.length()>1)
    {
        rtStr = varType+" " +rtVarName+";";
    }
    /* FIXME  special case*/
    if(isa<GetElementPtrInst>(*ins))
    {
        rtStr +="\n";
        std::string rawType;
        if(genCPUCode())
        {
            rawType = "u64";
        }
        else
        {
            rawType = "u32";
        }
        rtStr +=rawType+" "+rtVarName+"Raw;";
    }
    return rtStr;
}

std::string generateChannelString(int type, int seqNum, std::string source)
{                                           // seqNum denotes which instruction it is in the BB
    // type 0, branch tage channel
    // type 1, data channel
    std::string channelTypeStr;
    if(type == 0)
        channelTypeStr = "brTag";
    else
        channelTypeStr = "data";


    std::string final = channelTypeStr+int2Str(seqNum)+source;
    return final;
}

std::string generateOperandStr(Value* operand)
{
    std::string rtStr;
    if(isa<Instruction>(*operand))
    {
        Instruction& curIns = cast<Instruction>(*operand);
        // got to generate the varname
        int seqNum = getInstructionSeqNum(&curIns);
        std::string varName = generateVariableName(&curIns,seqNum);
        rtStr = varName;
    }
    else if(isa<Constant>(*operand))
    {
        Constant& curCon = cast<Constant>(*operand);
        rtStr = getConstantStr(curCon);

    }
    else
    {

        rtStr = operand->getName();

    }
    return rtStr;
}

std::string generateGenericSwitchStatement(std::string varName,bool explicitCase, std::vector<std::string>* caseVal,
                                           std::vector<std::string>* tgtLabel,std::string defaultDest,
                                           bool remoteDst=false,std::string channelName="", unsigned int defaultSeq=0)
{
    assert((!explicitCase)||(caseVal->size()==tgtLabel->size()));
    std::string rtStr="";
    //rtStr+= rtStr+"switch("+varName+")\n";
    addTabbedLine(rtStr,"switch("+varName+")");
    addTabbedLine(rtStr,"{");
    addBarSubTabs(true);
    unsigned int successorSeqNum = 0;
    for(unsigned int sucCount=0; sucCount<tgtLabel->size(); sucCount++ )
    {

        if(successorSeqNum ==defaultSeq)
            successorSeqNum++;
        std::string curCaseNum = explicitCase? caseVal->at(sucCount):int2Str(sucCount);
        addTabbedLine(rtStr,"case "+curCaseNum+":");

        addBarSubTabs(true);
        if(remoteDst)
        {
            // we need to push something to the channel
            // this should be which target it is
            addTabbedLine(rtStr,generatePushOp(int2Str(successorSeqNum),channelName));
        }
        addTabbedLine(rtStr,"goto "+tgtLabel->at(sucCount)+";");
        successorSeqNum++;
        addBarSubTabs(false);
    }
    addTabbedLine(rtStr,"default:");
    if(remoteDst)
    {
        //rtStr+="\t";
        addTabbedLine(rtStr,generatePushOp(int2Str(defaultSeq),channelName));
    }
    addTabbedLine(rtStr,"goto "+defaultDest+ ";");
    addBarSubTabs(false);
    addTabbedLine(rtStr,"}");
    return rtStr;
}

argPair* createArg(std::string channelName, std::string type, int size, int dir)
{
    argPair* s = new argPair;
    s->argName = channelName;
    s->argType = type;
    s->size = size;
    s->dir = dir;
    return s;
}


std::string generateGettingRemoteBranchTag(TerminatorInst& curIns, int seqNum, std::vector<argPair*>& p)
{
    std::string rtStr="";
    int channelType =  0;
    std::string channelStr = generateChannelString(channelType,seqNum,curIns.getParent()->getName());
    std::string varName = generateVariableName(&curIns,seqNum);

    // the name of the argument is gonna be the name of the channel
    // type of the channel is gonna be char?
    p.push_back(createArg(channelStr,generateFifoType(&curIns),8,0));

    unsigned numSuc = curIns.getNumSuccessors();
    assert(numSuc < 255 && numSuc>0);

    // we need to get remote target tag
    addTabbedLine(rtStr,"pop("+channelStr+","+varName+");");
    //rtStr = rtStr+"pop("+channelStr+","+varName+");\n";
    // if this is a unconditional branch we just do it
    if(numSuc==1)
    {
        BasicBlock* curSuc = curIns.getSuccessor(0);
        std::string sucName =  curSuc->getName();
        addTabbedLine(rtStr,"goto "+sucName+";");
        /*
        rtStr= rtStr+"goto ";
        rtStr= rtStr+ sucName;
        rtStr = rtStr +";\n";*/
        return rtStr;
    }
    std::vector<std::string> allTgt;
    for(unsigned int sucCount=0; sucCount<numSuc; sucCount++ )
    {
        BasicBlock* curSuc = curIns.getSuccessor(sucCount);
        allTgt.push_back(   curSuc->getName() );
    }
    rtStr = rtStr+generateGenericSwitchStatement(varName,0,0,&allTgt,ENDBLOCK);
    return rtStr;

}
std::string generateGettingRemoteData(Instruction& curIns, int seqNum, std::vector<argPair*>& fifoArgs)
{
    std::string rtStr="";
    int channelType =  1;
    std::string channelStr = generateChannelString(channelType,seqNum,curIns.getParent()->getName());
    std::string varName = generateVariableName(&curIns,seqNum);
    // when it is a getElementPtr instruction
    // we will pop a raw value off the queue
    // and cast it --> this is
    if(isa<GetElementPtrInst>(curIns))
    {
        std::string varNameU= varName+"Raw";
        addTabbedLine(rtStr,"pop("+channelStr+","+varNameU+");");
        // do a cast to the var
        addTabbedLine(rtStr, varName+"=("+getLLVMTypeStr(curIns.getType())+")"+varNameU+";");
    }
    else
    {
        addTabbedLine(rtStr,"pop("+channelStr+","+varName+");");
    }
    //FIXME: add the declaration of the raw data
    fifoArgs.push_back(createArg(channelStr,generateFifoType(&curIns),curIns.getType()->getScalarSizeInBits(),0 ) );

    // cast it to the var
    //addTabbedLine(rtStr,varName+"=("+ +")"+varNameU+";");
    return rtStr;
}
std::string generateLoadInstruction(LoadInst& li, std::string varName,std::vector<argPair*>& functionArgs)
{

    Value* ptrVal = li.getPointerOperand();
    // the pointer operand is not a functional argument normally?
    if(isa<Argument>(*ptrVal))
        functionArgs.push_back(createArg(ptrVal->getName(),generateVariableType(ptrVal),ptrVal->getType()->getScalarSizeInBits(),0));
    std::string ptrStr = generateOperandStr(ptrVal);
    return varName+"= *("+ptrStr+");";
}
std::string generateStoreInstruction(StoreInst& si,std::vector<argPair*>& functionArgs )
{

    Value* ptrVal = si.getPointerOperand();
    Value* val = si.getValueOperand();
    if(isa<Argument>(*ptrVal))
        functionArgs.push_back(createArg(ptrVal->getName(),generateVariableType(ptrVal),ptrVal->getType()->getScalarSizeInBits(),0));
    if(isa<Argument>(*val))
        functionArgs.push_back(createArg(val->getName(),generateVariableType(val),val->getType()->getScalarSizeInBits(),0));

    std::string ptrStr = generateOperandStr(ptrVal);

    std::string valStr = generateOperandStr(val);

    std::string rtStr ="*("+ptrStr+") = "+valStr+";";
    return rtStr;
}
std::string generateGetElementPtrInstruction(GetElementPtrInst& gepi, std::string varName,std::vector<argPair*>& functionArgs )
{

    Value* ptr = gepi.getPointerOperand();
    if(isa<Argument>(*ptr))
        functionArgs.push_back(createArg(ptr->getName(),generateVariableType(ptr),ptr->getType()->getScalarSizeInBits(),0));
    std::string ptrStr = generateOperandStr( ptr);

    Value* offsetVal = gepi.getOperand(1);
    if(isa<Argument>(*offsetVal))
        functionArgs.push_back(createArg(offsetVal->getName(),generateVariableType(offsetVal),offsetVal->getType()->getScalarSizeInBits(),0));

    std::string offSetStr = generateOperandStr(offsetVal);
    // check the index array and do additions
    std::string rtStr = varName+"= "+ptrStr+"+"+offSetStr+";";
    return rtStr;
}
std::string generateEndBlock(std::vector<BasicBlock*>* BBList )
{
    std::vector<BasicBlock*> outsideBBs;

    for(unsigned int bbInd = 0; bbInd < BBList->size(); bbInd++)
    {

        BasicBlock* curBB = BBList->at(bbInd);
        TerminatorInst* bTerm = curBB->getTerminator();
        for(unsigned int sucInd = 0; sucInd < bTerm->getNumSuccessors(); sucInd++)
        {
            BasicBlock* curSuc = bTerm->getSuccessor(sucInd);
            if(std::find(BBList->begin(),BBList->end(),curSuc) == BBList->end()  )
            {
                // add the curSuc to outsideBBs if it is not already there
                if(std::find(outsideBBs.begin(),outsideBBs.end(),curSuc) == outsideBBs.end() )
                {
                    outsideBBs.push_back(curSuc);
                }
            }
        }
    }
    // now generate the endblock
    std::string rtStr=ENDBLOCK;
    rtStr += ":\n;\n";
    for(unsigned int k = 0; k<outsideBBs.size(); k++)
    {
        rtStr += outsideBBs.at(k)->getName();
        rtStr += ":\n;\n";

    }
    return rtStr;

}
std::string generateCmpOperations(CmpInst& curIns, bool remoteDst, int seqNum,std::vector<argPair*>& fifoArgs,std::vector<argPair*>& functionArgs )
{

    int channelType = 1;

    std::string channelStr = generateChannelString(channelType,seqNum,curIns.getParent()->getName());
    std::string varName = generateVariableName(&curIns,seqNum);
    //int numberOfOperands = curIns.getNumOperands();

    Value* first = curIns.getOperand(0);
    Value* second = curIns.getOperand(1);
    if(isa<Argument>(*first))
    {
        functionArgs.push_back(createArg(first->getName(),generateVariableType(first),first->getType()->getScalarSizeInBits(),0));
    }
    if(isa<Argument>(*second))
    {
        functionArgs.push_back(createArg(second->getName(),generateVariableType(second),second->getType()->getScalarSizeInBits(),0));
    }

    std::string firstVal = generateOperandStr(first);
    std::string secondVal = generateOperandStr(second);
    bool def=false;
    std::string constBool="";
    std::string cmpOperator="";
    switch(curIns.getPredicate())
    {
          case CmpInst::FCMP_FALSE:
            def=true;
            constBool+="0";
            break;
          case CmpInst::FCMP_TRUE:
            def=true;
            constBool+="1";
            break;
          case CmpInst::ICMP_EQ:
          case CmpInst::FCMP_OEQ:
          case CmpInst::FCMP_UEQ:
            cmpOperator+="==";
            break;
          case CmpInst::ICMP_SGT:
          case CmpInst::ICMP_UGT:

          case CmpInst::FCMP_UGT:
          case CmpInst::FCMP_OGT:
            cmpOperator+=">";
            break;

          case CmpInst::ICMP_SGE:
          case CmpInst::ICMP_UGE:

          case CmpInst::FCMP_UGE:
          case CmpInst::FCMP_OGE:
            cmpOperator+=">=";
            break;

          case CmpInst::ICMP_SLT:
          case CmpInst::ICMP_ULT:
          case CmpInst::FCMP_ULT:
          case CmpInst::FCMP_OLT:
            cmpOperator+="<";
            break;
          case CmpInst::ICMP_ULE:
          case CmpInst::ICMP_SLE:
          case CmpInst::FCMP_ULE:
          case CmpInst::FCMP_OLE:
            cmpOperator+="<=";
            break;
          case CmpInst::ICMP_NE:
          case CmpInst::FCMP_UNE:
          case CmpInst::FCMP_ONE:
            cmpOperator+="!=";
            break;

          default:
            errs()<<"unhandled cmp type\n";
            exit(1);



    }
    std::string rtStr="";
    if(def)
    {
        addTabbedLine( rtStr, varName+"="+ constBool+";");
    }
    else
    {
        addTabbedLine( rtStr, varName+" = "+firstVal+cmpOperator+" "+secondVal+";");

    }
    //std::string condStr  = generateOperandStr( curIns.getCondition());
    //std::string trueStr = generateOperandStr( curIns.getTrueValue());
    //std::string falseStr = generateOperandStr( curIns.getFalseValue());
    //rtStr+= varName+" = "+condStr+"?"+trueStr+":"+falseStr+";\n";
    if(remoteDst)
    {
        addTabbedLine(rtStr,generatePushOp(varName,channelStr));
        fifoArgs.push_back(createArg(channelStr,generateFifoType(&curIns),curIns.getType()->getScalarSizeInBits(),1));
    }
    return rtStr;


}

std::string generateSelectOperations(SelectInst& curIns,bool remoteDst,int seqNum,std::vector<argPair*>& functionArgs, std::vector<argPair*>& fifoArgs)
{
    std::string rtStr="";
    int channelType =  1;
    std::string channelStr = generateChannelString(channelType,seqNum,curIns.getParent()->getName());
    std::string varName = generateVariableName(&curIns,seqNum);

    Value* condVal =  curIns.getCondition();
    std::string condStr  = generateOperandStr(condVal);
    Value* trueVal =  curIns.getTrueValue();
    std::string trueStr = generateOperandStr(trueVal );
    Value* falseVal = curIns.getFalseValue();
    std::string falseStr = generateOperandStr(falseVal);
    // any of cond true false can come from function args
    if(isa<Argument>(*(condVal)))
    {
        functionArgs.push_back(createArg(condVal->getName(),generateVariableType(condVal),condVal->getType()->getScalarSizeInBits(),0));
    }
    if(isa<Argument>(*(trueVal)))
    {
        functionArgs.push_back(createArg(trueVal->getName(),generateVariableType(trueVal),trueVal->getType()->getScalarSizeInBits(),0));
    }
    if(isa<Argument>(*(falseVal)))
    {
        functionArgs.push_back(createArg(falseVal->getName(),generateVariableType(falseVal),falseVal->getType()->getScalarSizeInBits(),0));
    }


    addTabbedLine(rtStr, varName+" = "+condStr+"?"+trueStr+":"+falseStr+";");
    if(remoteDst)
    {
        fifoArgs.push_back(createArg(channelStr,generateFifoType(&curIns),curIns.getType()->getScalarSizeInBits(),1));
        addTabbedLine(rtStr,generatePushOp(varName,channelStr));
    }
    return rtStr;


}


std::string generatePhiNode(PHINode& curIns,bool remoteDst,int seqNum,
                                  BBMap2outStr& preAssign,std::vector<argPair*>& functionArgs, std::vector<argPair*>& fifoArgs)
{
    std::string rtStr="";
    int channelType =  1;
    std::string channelStr = generateChannelString(channelType,seqNum,curIns.getParent()->getName());
    std::string varName = generateVariableName(&curIns,seqNum);
    for(unsigned int inBlockInd = 0; inBlockInd<curIns.getNumIncomingValues();inBlockInd++)
    {
        BasicBlock* curPred = curIns.getIncomingBlock(inBlockInd);
        Value* curPredVal = curIns.getIncomingValueForBlock(curPred);

        if(isa<Argument>(*curPredVal))
        {
            functionArgs.push_back(createArg(curPredVal->getName(),generateVariableType(curPredVal),curPredVal->getType()->getScalarSizeInBits(),0));
        }
        // now we check if the BB has a vector of strings, if not we add one
        if(preAssign.find(curPred)==preAssign.end())
        {
            std::vector<std::string>*& predPhiStrings = preAssign[curPred];
            predPhiStrings = new std::vector<std::string>();
        }
        // now we generate the string,
        std::string valueStr = generateOperandStr(curPredVal);
        std::string preAssignStr="";
        addTabbedLine(preAssignStr, varName+"="+valueStr+";");
        (preAssign[curPred])->push_back(preAssignStr);
    }
    if(remoteDst)
    {
        fifoArgs.push_back(createArg(channelStr,generateFifoType(&curIns),curIns.getType()->getScalarSizeInBits(),1));
        addTabbedLine(rtStr,generatePushOp(varName,channelStr));
    }
    return rtStr;

}

std::string generateMemoryOperations(Instruction& curIns, bool remoteDst, int seqNum,std::vector<argPair*>& fifoArgs, std::vector<argPair*>& functionArgs)
{
    std::string rtStr="";
    int channelType =  1;
    std::string channelStr = generateChannelString(channelType,seqNum,curIns.getParent()->getName());
    std::string varName = generateVariableName(&curIns,seqNum);

    switch(curIns.getOpcode())
    {
    case Instruction::Alloca:
        // FIXME: untested just generate a declaration
        rtStr = generateVariableDeclStr(&curIns,seqNum);
        break;
    case Instruction::Load:
        //LoadInst& li = cast<LoadInst>(curIns);
        addTabbedLine(rtStr,generateLoadInstruction(cast<LoadInst>(curIns),varName,functionArgs));
        break;
    case Instruction::Store:
        addTabbedLine(rtStr, generateStoreInstruction(cast<StoreInst>(curIns),functionArgs));
        break;
    case Instruction::GetElementPtr:
        addTabbedLine(rtStr,generateGetElementPtrInstruction( cast<GetElementPtrInst>(curIns), varName,functionArgs));
        break;
    default:
        errs()<<"unhandled instruction\n";
        exit(0);
    }
    if(remoteDst)
    {
        fifoArgs.push_back(createArg(channelStr,generateFifoType(&curIns),curIns.getType()->getScalarSizeInBits(),1));
        // may need the raw and cast if it is getElemptr
        std::string varNamePush = varName;
        if(curIns.getOpcode()==Instruction::GetElementPtr)
        {
            varNamePush += "Raw";
            addTabbedLine( rtStr, varNamePush+"=(u32)"+varName+";");
        }
        addTabbedLine(rtStr,generatePushOp(varNamePush,channelStr));
    }

    return rtStr;

}
std::string generateSimpleAssign(Instruction& curIns, std::string varName)
{
    std::string rtStr = varName;
    Value* v = curIns.getOperand(0);
    std::string originalVal = generateOperandStr(v );
    rtStr += "=" + originalVal+";\n";
    return rtStr;
}


std::string generateCastOperations(Instruction& curIns, bool remoteDst, int seqNum,std::vector<argPair*>& functionArgs, std::vector<argPair*>& fifoArgs)
{
    std::string rtStr="";
    int channelType =  1;
    std::string channelStr = generateChannelString(channelType,seqNum,curIns.getParent()->getName());
    std::string varName = generateVariableName(&curIns,seqNum);
    Value* oriv =0;
    switch(curIns.getOpcode())
    {
    case Instruction::Trunc:
    case Instruction::ZExt:
    case Instruction::SExt:
    case Instruction::BitCast:
        // just generate a declaration
        addTabbedLine(rtStr, generateSimpleAssign(curIns,varName));
        oriv = curIns.getOperand(0);
        if(isa<Argument>(*(oriv)))
            functionArgs.push_back(createArg(oriv->getName(),generateVariableType(oriv),oriv->getType()->getScalarSizeInBits(),0));
        break;
    default:
        errs()<<"unhandled cast instruction\n"<<curIns;
        exit(0);
    }
    if(remoteDst)
    {
        fifoArgs.push_back(createArg(channelStr,generateFifoType(&curIns),curIns.getType()->getScalarSizeInBits(),1));
        //rtStr=rtStr+generatePushOp(varName,channelStr);
        addTabbedLine(rtStr,generatePushOp(varName,channelStr));
    }

    return rtStr;

}

std:: string generateBinaryOperations(BinaryOperator& curIns, bool remoteDst,int seqNum, std::vector<argPair*>& fifoArgs, std::vector<argPair*>& functionArgs )
{
    std::string rtStr="";
    int channelType =  1;
    std::string channelStr = generateChannelString(channelType,seqNum,curIns.getParent()->getName());
    std::string varName = generateVariableName(&curIns,seqNum);
    // need to get the operand
    // they can be instruction, they can be functional argument or they can be
    // constant -- we need to get operand var name when
    // two operand
    Value* firstOperand = curIns.getOperand(0);
    Value* secondOperand = curIns.getOperand(1);
    // now check if these operands are from the function argument
    //FIXME: get the function arguement through settings port in accelerator
    //Or we can just change the part where functionDecl is generated
    if(isa<Argument>(*firstOperand))
    {
        functionArgs.push_back(createArg(firstOperand->getName(), generateVariableType(firstOperand),firstOperand->getType()->getScalarSizeInBits(),0 ) );
    }
    if(isa<Argument>(*secondOperand))
    {
        functionArgs.push_back(createArg(secondOperand->getName(), generateVariableType(secondOperand),secondOperand->getType()->getScalarSizeInBits(),0));
    }

    std::string firstOperandStr = generateOperandStr(firstOperand);
    std::string secondOperandStr = generateOperandStr(secondOperand);
    addTabbedLine(rtStr,varName+"=");
    // generate the actual computation
    switch(curIns.getOpcode())
    {
    case Instruction::Add:
    case Instruction::FAdd:
        rtStr = rtStr + firstOperandStr + "+";
        break;
    case Instruction::Sub:
    case Instruction::FSub:
        rtStr = rtStr + firstOperandStr + "-";
        break;
    case Instruction::Mul:
    case Instruction::FMul:
        rtStr = rtStr + firstOperandStr + "*";
        break;
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::FDiv:
        rtStr = rtStr + firstOperandStr + "/";
        break;
    case Instruction::URem:
    case Instruction::SRem:
    case Instruction::FRem:
        rtStr = rtStr + firstOperandStr + "%";
        break;
    case Instruction::Shl:
        rtStr = rtStr + firstOperandStr + "<<";
        break;
    case Instruction::LShr:
    case Instruction::AShr:
        rtStr = rtStr + firstOperandStr + ">>";
        break;
    case Instruction::And:
        rtStr = rtStr + firstOperandStr + "&";
        break;
    case Instruction::Or:
        rtStr = rtStr + firstOperandStr + "|";
        break;
    case Instruction::Xor:
        rtStr = rtStr + firstOperandStr +"^";
        break;
    default:
        errs()<<"Unrecognized binary Ops\n";
        exit(1);

    }
    rtStr = rtStr + secondOperandStr+";";
    if(remoteDst)
    {
        addTabbedLine(rtStr,generatePushOp(varName,channelStr));
        fifoArgs.push_back(createArg(channelStr, generateFifoType(&curIns),curIns.getType()->getScalarSizeInBits(),1 ) );
    }
    return rtStr;
}

std::string generateControlFlow(TerminatorInst& curIns,bool remoteDst, int seqNum, std::vector<argPair*>& fifoArgs, std::vector<argPair*>& functionArgs)
{
    // we currently deal with br and switch only
    assert(isa<BranchInst>(curIns) || isa<SwitchInst>(curIns) );
    std::string rtStr="";
    std::string channelName = generateChannelString(0, seqNum, curIns.getParent()->getName());
    if(isa<BranchInst>(curIns))
    {
        BranchInst& bi = cast<BranchInst>(curIns);
        std::string firstSucName= bi.getSuccessor(0)->getName();
        if(bi.isUnconditional())
        {
            if(remoteDst)
            {
                //rtStr=rtStr+generatePushOp("1",channelName);
                // this is a fifo args
                addTabbedLine(rtStr, generatePushOp("1",channelName));
            }
            addTabbedLine( rtStr,"goto "+firstSucName +";");
        }
        else
        {
            Value* condVal = bi.getCondition();
            assert(isa<Instruction>(*condVal) || isa<Argument>(*condVal) );
            std::string switchVar="";

            if(isa<Argument>(*condVal))
            {
                Argument* valArg = &(cast<Argument>(*condVal));
                switchVar+= valArg->getName();
                functionArgs.push_back(createArg(valArg->getName(), generateVariableType(valArg), valArg->getType()->getScalarSizeInBits(),0   ));
            }
            else
            {
                Instruction* valGenIns = &(cast<Instruction>(*condVal));
                switchVar += generateVariableName(valGenIns);
            }
            addTabbedLine(rtStr,"if("+switchVar+")");
            addTabbedLine(rtStr,"{");
            addBarSubTabs(true);
            if(remoteDst)
            {
               addTabbedLine(rtStr, generatePushOp("0",channelName));
            }

            addTabbedLine( rtStr,"goto "+firstSucName+";");
            addBarSubTabs(false);
            addTabbedLine(rtStr,"}");
            addTabbedLine(rtStr,"else");
            addTabbedLine(rtStr,"{");
            addBarSubTabs(true);
            if(remoteDst)
                addTabbedLine(rtStr,generatePushOp("1",channelName));

            std::string secondSucName = bi.getSuccessor(1)->getName();
            addTabbedLine(rtStr,"goto "+secondSucName+";");
            addBarSubTabs(false);
            addTabbedLine(rtStr,"}");
        }

    }
    else
    {
        // this is when its a switch
        // we need to build a set of potential destination/case values
        SwitchInst& si = cast<SwitchInst>(curIns);
        std::vector<std::string> caseVal;
        std::vector<std::string> allTgt;
        std::string defaultDest=ENDBLOCK;
        unsigned int defaultSeq = 0;
        for(unsigned int sucInd=0; sucInd < si.getNumSuccessors(); sucInd++)
        {
            BasicBlock* curBB = si.getSuccessor(sucInd);
            ConstantInt* curCaseVal = si.findCaseDest(curBB);
            if(curCaseVal==NULL)
            {
                defaultDest =  curBB->getName();
                defaultSeq=sucInd;
            }
            else
            {
                allTgt.push_back( curBB->getName());
                caseVal.push_back(curCaseVal->getValue().toString(10,true));
            }

        }

        // if this is local, this value doesnt exist -- it should assume
        // the value of the instruction generating the value -- or constant
        // -- or whatever
        // anyhow, generateOperand

        //FIXME
        //std::string varName = generateVariableName(&curIns,seqNum);
        std::string switchName = generateOperandStr(si.getCondition());
        // I guess there is a possibility this is from the function argument

        if(isa<Argument>(*(si.getCondition())))
        {
            // need to add it to the function arg list
            Value* valArg = si.getCondition();
            functionArgs.push_back(createArg(valArg->getName(),generateVariableType(valArg), valArg->getType()->getScalarSizeInBits(),0 ));
        }

        addTabbedLine(rtStr, generateGenericSwitchStatement(switchName,true,&caseVal,&allTgt,defaultDest,true,channelName,defaultSeq));

    }
    if(remoteDst)
        fifoArgs.push_back(createArg(channelName,generateFifoType(&curIns),8,1));
    return rtStr;

    // for branch, we can convert it to switch statement as well


}
std::string generateReturn(ReturnInst& curIns, std::vector<argPair*>& functionArgs)
{

    std::string returnStatement="return ";
    if(curIns.getReturnValue()==0)
    {
        returnStatement = returnStatement+"void;\n";
    }
    else
    {
        // find the variable name
        Value* retVal = curIns.getReturnValue();
        assert(isa<Instruction>(*retVal) || isa<Argument>(*retVal));
        std::string retVar="";
        if(isa<Instruction>(*retVal))
        {
            Instruction* valGenIns = &(cast<Instruction>(*retVal));
            retVar += generateVariableName(valGenIns);

        }
        else
        {
            retVar += retVal->getName();
            if(isa<Argument>(*retVal))
                functionArgs.push_back(createArg(retVal->getName(),generateVariableType(retVal),retVal->getType()->getScalarSizeInBits(),0 ));
        }
        returnStatement=returnStatement+retVar+";";

    }
    std::string rtStr;
    addTabbedLine(rtStr, returnStatement);
    return rtStr;
}

#endif
