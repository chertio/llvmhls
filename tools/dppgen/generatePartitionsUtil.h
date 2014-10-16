
#include "llvm/Support/IncludeFile.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "InstructionGraph.h"
using namespace llvm;
int instructionLatencyLookup(Instruction* ins)
{
    // normal instructions like "and, or , add, shift, are assigned a value of 3, multiply assigned a value of 10"
    // load and store assigned a value of 10, and 10 means one pipeline stage,
    if(ins->mayReadFromMemory())
        return 1;
    if(ins->getOpcode()==Instruction::Mul)
        return 5;
    if(ins->getOpcode()==Instruction::Br)
        return 0;
    return 1;
}
std::string int2Str(int in)
{

    std::ostringstream ss;
    ss << in;
    return ss.str();
}

std::string replaceAllDotWUS(std::string original)
{
   std::replace( original.begin(), original.end(), '.', '_');

}

std::string generateVariableName(Instruction* ins, int seqNum)
{
    std::string rtVarName=ins->getParent()->getName();

    rtVarName = rtVarName+int2Str(seqNum);
    return rtVarName;
}

std::string generateVariableStr(Instruction* ins, int seqNum)
{

    std::string rtVarName = generateVariableName(ins,seqNum);

    std::string varType="";

    std::string rtStr;
    if(ins->isTerminator()&&!isa<ReturnInst>(*ins))
    {
        varType = "char ";

    }
    switch(ins->getType())
    {
        case VoidTyID:
            rtVarName="";
            break;
        case HalfTyID:
            varType="short ";
            break;
        case FloatTyID:
            varType="float ";
            break;
        case DoubleTyID:
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
        //IntegerTyID,     ///< 10: Arbitrary bit width integers
        //FunctionTyID,    ///< 11: Functions
        //StructTyID,      ///< 12: Structures
        //ArrayTyID,       ///< 13: Arrays
        case PointerTyID:
            varType ="void* ";
            break;
        //VectorTyID,      ///< 15: SIMD 'packed' format, or other vector type
        default:
            errs()<<"unhandled type, exit\n";
            exit(1);
    }

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

