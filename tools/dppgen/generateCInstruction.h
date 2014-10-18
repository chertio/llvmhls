#ifndef GENERATECINS
#define GENERATECINS

#include "llvm/Support/IncludeFile.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/APInt.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "InstructionGraph.h"
#include "generatePartitionsUtil.h"
#define ENDBLOCK "END"
std::string generateVariableName(Instruction* ins, int seqNum)
{
    std::string rtVarName=ins->getParent()->getName();

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

std::string generateVariableType(Instruction* ins)
{
    std::string varType;
    if(ins->isTerminator()&&!isa<ReturnInst>(*ins))
    {
        varType = "char";
        return varType;

    }
    switch(ins->getType())
    {
        case Type::VoidTyID:
            varType="";
            break;
        case Type::HalfTyID:
            varType="short ";
            break;
        case Type::FloatTyID:
            varType="float ";
            break;
        case Type::DoubleTyID:
            varType ="double ";
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
            varType ="int ";
            break;
        //FunctionTyID,    ///< 11: Functions
        //StructTyID,      ///< 12: Structures
        //ArrayTyID,       ///< 13: Arrays
        case Type::PointerTyID:
            varType ="void* ";
            break;
        //VectorTyID,      ///< 15: SIMD 'packed' format, or other vector type
        default:
            errs()<<"unhandled type, exit\n";
            exit(1);
    }

}


std::string generateVariableStr(Instruction* ins, int seqNum)
{

    std::string rtVarName = generateVariableName(ins,seqNum);

    std::string varType=generateVariableType(ins);
    if(varType.length()==0)
        rtVarName="";
    std::string rtStr;
    rtStr = varType+" "+rtVarName+";";
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

std::string generateGenericSwitchStatement(std::string varName,bool explicitCase, std::vector<std::string>* caseVal,
                                           std::vector<std::string>* tgtLabel,std::string defaultDest,
                                           bool remoteDst=false,std::string channelName="", unsigned int defaultSeq=0)
{
    assert((!explicitCase)||(caseVal->size()==tgtLabel->size()),"unmatched dest in switch");
    std::string rtStr="";
    rtStr+= rtStr+"switch("+varName+")\n";
    rtStr+="{\n";

    unsigned int successorSeqNum = 0;
    for(unsigned int sucCount=0; sucCount<tgtLabel->size(); sucCount++ )
    {

        if(successorSeqNum ==defaultSeq)
            successorSeqNum++;
        std::string curCaseNum = explicitCase? caseVal->at(sucCount):int2Str(sucCount);
        rtStr+="\tcase "+curCaseNum+":\n";
        if(remoteDst)
        {
            // we need to push something to the channel
            // this should be which target it is
            rtStr+="\tpush ("+channelName+","+int2Str(successorSeqNum)+");\n";

        }
        rtStr+="\tgoto "+tgtLabel->at(sucCount)+";\n";
        successorSeqNum++;

    }
    rtStr+="default:\n";
    if(remoteDst)
    {
        rtStr+="\tpush ("+channelName+","+int2Str(defaultSeq)+");\n";
    }
    rtStr+="\tgoto "+defaultDest+ ";}\n";
    return rtStr;
}

std::string generateGettingRemoteBranchTag(TerminatorInst& curIns, int seqNum)
{
    std::string rtStr="";
    int channelType =  0;
    std::string channelStr = generateChannelString(channelType,seqNum,curIns.getParent()->getName());
    std::string varName = generateVariableName(ins,seqNum);
    unsigned numSuc = curIns.getNumSuccessors();
    assert(numSuc < 255 && numSuc>0);

    // we need to get remote target tag
    rtStr = rtStr+"pop("+channelStr+","+varName+");\n";
    // if this is a unconditional branch we just do it
    if(numSuc==1)
    {
        BasicBlock* curSuc = cast<TerminatorInst>(*curIns).getSuccessor(0);
        rtStr=rtStr+"goto "+curSuc->getName()+";\n";
        return rtStr;
    }
    std::vector<std::string> allTgt;
    for(unsigned int sucCount=0; sucCount<numSuc; sucCount++ )
    {
        BasicBlock* curSuc = cast<TerminatorInst>(*curIns).getSuccessor(sucCount);
        allTgt.pop_back(curSuc->getName());
    }
    rtStr = rtStr+generateGenericSwitchStatement(varName,0,0,&allTgt,ENDBLOCK);
    return rtStr;

}

std::string generateControlFlow(TerminatorInst& curIns,bool remoteDst, int seqNum)
{
    // we currently deal with br and switch only
    assert(isa<BranchInst>(curIns) || isa<SwitchInst>(curIns) , "unhandled control flow statement");
    std::string rtStr="";
    std::string channelName = generateChannelString(0, seqNum,curIns->getParent()->getName());
    if(isa<BranchInst>(curIns))
    {
        BranchInst& bi = cast<BranchInst>curIns;
        if(bi.isUnconditional())
        {
            if(remoteDst)
            {
                rtStr=rtStr+"push ("+channelName+",1);\n";
            }
            rtStr=rtStr+"goto "+ bi.getSuccessor(0)->getName()+";\n";
        }
        else
        {
            Value* condVal = bi.getCondition();
            assert(isa<Instruction>(*condVal),"br variable not from instruction");
            Instruction* valGenIns = &(cast<Instruction>(*condVal));
            std::string switchVar = generateVariableName(valGenIns);
            rtStr="if("+switchVar+"){\n";
            if(remoteDst)
                rtStr=rtStr+"push ("+channelName+",0);\n";
            rtStr=rtStr+"goto "+bi.getSuccessor(0)->getName()+";}\n";

            rtStr="else{\n";
            if(remoteDst)
                rtStr=rtStr+"push ("+channelName+",1);\n";
            rtStr=rtStr+"goto "+bi.getSuccessor(1)->getName()+";}\n";

        }

    }
    else
    {
        // this is when its a switch
        // we need to build a set of potential destination/case values
        SwitchInst& si = cast<SwitchInst>curIns;
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
                defaultDest = curBB->getName();
                defaultSeq=sucInd;
            }
            else
            {
                allTgt.push_back(curBB->getName());
                caseVal.push_back(curCaseVal->getValue().toString());
            }

        }
        std::string varName = generateVariableName(curIns,seqNum);
        rtStr = generateGenericSwitchStatement(varName,true,&caseVal,&allTgt,defaultDest,true,channelName,defaultSeq);
    }
    return rtStr;

    // for branch, we can convert it to switch statement as well
    Value* varGen = curIns.getOperand(0);
    // let's figure out the
    assert(isa<Instruction>(*varGen),"switch variable not from instruction");
    Instruction* valGenIns = &(cast<Instruction>(*varGen));

    std::string switchVar = generateVariableName(valGenIns);
    std::string rtStr;
    // if there is remote, we got to decide the output first

    // this is local source, so we figure out the operand instruction
    // use, it is the first operand normally
    for(unsigned int operandInd = 0; operandInd<curIns->getNumOperands(); operandInd++)
    {
        Value* curOp = curIns->getOperand(operandInd);
        if(curOp.getType()==Type::IntegerTyID)
        {
            assert(isa<Instruction>(curOp));
            Instruction* srcIns =&(cast<Instruction>(curOp));
            // now we find the varName corresponding to srcIns
            std::string varNameFromSrc = generateVariableName(srcIns);


        }
    }

    rtStr+="switch("+varName+")\n";
    rtStr+="{\n";

    for(unsigned int sucCount=0; sucCount<numSuc; sucCount++ )
    {
        BasicBlock* curSuc = cast<TerminatorInst>(*curIns).getSuccessor(sucCount);
        rtStr+="\tcase "+int2Str(sucCount)+":\n";
        rtStr+="\tgoto "+curSuc->getName()+";\n";
    }

    rtStr+="}\n";

}
std::string generateReturn(ReturnInst& curIns)
{

}

#endif
